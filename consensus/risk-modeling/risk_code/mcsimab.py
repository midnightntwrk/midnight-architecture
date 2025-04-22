# !/usr/bin/env python
# -*- coding: utf-8 -*-

import numpy as np
import pandas as pd
import scipy.stats as stats
import seaborn as sns
from matplotlib import pyplot as plt
from numpy import arange, ceil, ndarray, ones, random, zeros
from tqdm import tqdm

from slot_alloc_sim import simulate_epoch_permissioned, simulate_epoch_registered


def sample_multinomial(num_participants: int) -> ndarray:
    """This function generates a probability vector from a flat Dirichlet distribution
    (with equal pseudo-counts for every participant)
    
    Args:
        num_participants: Number of participants (candidates from group)
        
    Returns:
        probabilities: A probability vector sampled from the Dirichlet distribution
    """
    # Define a "flat" Dirichlet prior where every pseudo-count is 1.
    alpha = ones(num_participants)
    
    # Sample a probability vector from the Dirichlet distribution,
    # which represents the multinomial probabilities for each participant.
    return random.dirichlet(alpha)


# Define the function to sample alpha from a joint distribution
def sample_alpha() -> dict:
    """
    Generates a sample allocation of seats among participants using a multinomial
    distribution.

    The function determines the total number of seats and the number of
    participants from predefined options. It then generates probabilities for
    each participant and uses these probabilities to allocate seats
    proportionally. The result is returned as a dictionary containing all the
    generated values.

    Returns:
        dict: A dictionary containing the following keys and values:
            - total_seats (int): Total number of available seats.
            - num_participants (int): Number of participants.
            - p (List[float]): Probabilities for each participant.
            - seat_counts (List[int]): List containing the number of seats
              allocated to each participant.

    Raises:
        AssertionError: If the internal logic fails, such as the sum of seat
        counts exceeding the specified total seats due to an unexpected error.
    """
    num_registered = random.choice([20, 40, 80, 160])
    num_permitted = int(ceil(random.choice([0.0, 0.1, 0.3, 0.5, 0.7]) * num_registered))
    total_seats = num_registered + num_permitted
    registered_probabilities = sample_multinomial(num_registered)
    max_faults = 7  # fault tolerance levels = [1, 2, ..., max_faults]
    sample = dict(
        total_seats=total_seats,
        num_registered=num_registered,
        num_permissioned=num_permitted,
        registered_probabilities=registered_probabilities,
        max_faults=max_faults,
        )
    return sample


def faults_tolerated(committee_seats: pd.Series) -> int:
    """
    Compute the number of faults tolerated by the committee

    Args:
        committee_seats (pd.Series): Series of committee seats.

    Returns:
        int: The number of faults tolerated by the committee.
    """
    voting_strength = committee_seats.sort_values(ascending=False).divide(
        committee_seats.sum(),
        )
    threshold = 1 / 3  # BFT finality risk threshold
    faults = np.where(np.cumsum(voting_strength) > threshold)[0][0]
    return faults


def simulate_epoch_federated(
    registered_seat_counts: ndarray,
    num_federated: int = 10,
    seats_per_federated: int = 2,
    verbose: bool = False,
    ) -> pd.DataFrame:
    """
    Creates a committee with registered and federated seats.

    The `simulate_epoch_federated` function allocates committee seats between two types of nodes: registered nodes
    (whose seat allocation is proportional to their stake) and federated nodes (which receive a fixed number of
    seats). It calculates the voting strength of each group, ensures they sum to 1.0, and returns a structured
    DataFrame containing the committee composition with seat assignments for both node types.

    Args:
        registered_seat_counts (ndarray): seat counts for registered participants.
        num_federated (int): Number of federated nodes.
        seats_per_federated (int): Number of seats per federated node.
        verbose (bool): Whether to print detailed information.
            Default is False.

    Returns:
        pd.DataFrame: Committee seats information with kind and seat assignments.
    """
    # Cast the seat counts to a pandas Series
    registered_seat_counts = pd.Series(registered_seat_counts, name="registered seats")
    
    # Get the number of registered participants (SPOs)
    num_registered = registered_seat_counts.shape[0]
    
    # Calculate the number of federated seats in the committee
    federated_seats = seats_per_federated * num_federated
    
    # Committee size is the total number of registered and federated seats
    registered_seats = registered_seat_counts.sum()
    committee_size = registered_seats + federated_seats
    
    # Calculate the voting strength of the registered seats
    registered_voting_strength = registered_seats / committee_size
    
    # Calculate the voting strength of the federated seats
    federated_voting_strength = federated_seats / committee_size
    
    # Assert that the voting strengths sum to 1.0
    assert (
        registered_voting_strength + federated_voting_strength == 1.0
    ), "Voting strength does not sum to 1.0"
    
    # Create a series for the federated seats on the committee
    federated_seat_counts = pd.Series(
        ones(num_federated, dtype="int64") * seats_per_federated,
        index=[str(i) for i in range(num_registered + 1, num_registered + num_federated + 1)],
        dtype="int64",
        name="federated seats",
        )
    
    # Combine the federated and registered seats into a single DataFrame
    committee_seats = (
        pd.concat(
            [federated_seat_counts, registered_seat_counts],
            keys=["federated", "registered"],
            names=["kind", "index"],
            ignore_index=False,
            )
        .reset_index()
        .rename(columns={0: "seats"})
        .set_index("index")
        .sort_values(by=["seats", "kind"], ascending=[False, True])
    )
    if verbose:
        print(
            f"Committee size .... = {committee_size} \n"
            "________________________________________\n"
            "Registered:\n"
            f"Number registered.. = {num_registered} \n"
            f"Number of seats.... = {registered_seats} \n"
            f"Voting strength.... = {registered_voting_strength:.2%} \n"
            "________________________________________\n"
            "Federated:\n"
            f"Number federated... = {num_federated} \n"
            f"Seats per federated = {seats_per_federated} \n"
            f"Number of seats.... = {federated_seats} \n"
            f"Voting strength.... = {federated_voting_strength:.2%}\n",
            )
    return committee_seats


def simulate_committee_federated(
    registered_probabilities: ndarray,
    num_registered: int = 15,
    num_federated: int = 5,
    seats_per_federated: int = 1,
    num_epochs: int = 100,
    **kwargs,
    ) -> pd.DataFrame:
    """
    Simulate the allocation of committee seats over multiple epochs.

    This function simulates the process of assigning committee seats for a specified
    number of epochs using the simulate_epoch_federated function. It collects seat
    assignments across all epochs and returns them as a DataFrame.

    Args:
        registered_probabilities (ndarray): Probabilities for registered participants.
        num_registered (int): Number of registered participants. Default is 15.
        num_federated (int): Number of federated nodes. Default is 5.
        seats_per_federated (int): Number of seats per federated node. Default is 1.
        num_epochs (int): Number of epochs to simulate. Default is 100.
        kwargs: Additional keyword arguments.

    Returns:
        pd.DataFrame: DataFrame containing committee seat assignments for all epochs,
                     with epochs as rows and committee members as columns.
    """
    committee_list = []
    for epoch in range(num_epochs):
        # Sample the committee seat configuration from the multinomial distribution
        # parameterized by registered_probabilities.
        registered_seat_counts = random.multinomial(num_registered, registered_probabilities)
        
        # Assign committee seats for the current epoch
        committee = simulate_epoch_federated(
            registered_seat_counts=registered_seat_counts,
            num_federated=num_federated,
            seats_per_federated=seats_per_federated,
            )
        committee_list.append(committee.seats)
    
    assert len(committee_list) == num_epochs, "Number of epochs does not match."
    
    committee_seats = pd.concat(committee_list, keys=range(num_epochs), axis=1).T
    
    return committee_seats


def simulate_proposed(
    registered_probabilities: ndarray,
    num_registered: int = 15,
    num_federated: int = 5,
    num_epochs: int = 100,
    **kwargs,
    ) -> pd.DataFrame:
    """Runs the proposed algorithm simulation. For each epoch, simulates both the
    registered and permissioned candidate selection. Stores the number of slots
    each candidate gets and returns the cumulative results.

    Args:
        registered_probabilities (ndarray): Probabilities for registered candidates.
        num_registered (int): Number of registered candidates. Default is 15.
        num_federated (int): Number of federated (permissioned) nodes. Default is 5.
        num_epochs (int): Number of epochs to simulate. Default is 100.
        kwargs: Additional keyword arguments.

    Returns:
        pd.DataFrame: DataFrame containing committee seat assignments for all epochs,
            with epochs as rows and committee members as columns.
    """
    permissioned_candidates = [f"P{i}" for i in range(num_federated)]
    permissioned_results = {name: [] for name in permissioned_candidates}
    registered_results = {i: [] for i in range(num_registered)}
    
    for _ in range(num_epochs):
        registered_candidates = {i: registered_probabilities[i] for i in registered_results.keys()}
        
        # Simulate this epoch
        reg_assign = simulate_epoch_registered(registered_candidates, num_registered)
        perm_assign = simulate_epoch_permissioned(permissioned_candidates, num_federated)
        
        # Collect results
        for name in registered_candidates:
            registered_results[name].append(reg_assign[name])
        for name in permissioned_candidates:
            permissioned_results[name].append(perm_assign[name])
    
    # Combine the two dictionaries
    combined = registered_results.copy()
    combined.update(permissioned_results)
    
    # Convert to DataFrame
    committee_seats = (
        pd.DataFrame.from_dict(combined, orient="index")
        .astype(int)
        .fillna(0)
        .transpose()
    )
    return committee_seats


def calculate_fault_tolerance_probability(
    committee_seats: pd.DataFrame,
    fault_tolerance: int = 1,
    ) -> float:
    """
    Calculate the probability of tolerating a given number of faults
    in a committee of a given size.
    The function uses Monte Carlo simulation to estimate the probability.
    Args:
        committee_seats (pd.DataFrame): DataFrame of committee seat
            assignments of both registered and permissioned members
            for each epoch.
        fault_tolerance (int): Number of faults to tolerate.

    Returns:
        float: Estimated probability of tolerating the given number of faults.
    """
    # Calculate success rate through Monte Carlo simulation
    probability = (
        committee_seats.apply(faults_tolerated, axis=1) >= fault_tolerance
    ).mean()
    return probability


def compute_score(ft: pd.Series) -> float:
    """
    Compute the performance score from ft, the probability
    of tolerating a number of faults given by the p index.

    Args:
        ft (pd.Series): fault tolerance probability series

    Returns:
        float: computed score
    """
    # Convert index to numeric if it's not already
    numeric_index = pd.to_numeric(ft.index).values
    
    # Element-wise multiplication of index values with probabilities
    score = (numeric_index * ft.probability.values).sum()
    
    return score


# Stub functions for Algorithm A and B
def algorithm(function, **params) -> float:
    """
    Computes fault tolerance probabilities using an algorithm that processes a defined function and its
    parameters to determine committee seats and calculate probabilities for a fault tolerance metric.

    Args:
        function (Callable): A function that determines committee seats based on provided parameters.
        **params: A set of keyword arguments to be passed into the function `function`. Must include
            'max_faults' which defines the maximum faults for calculating probabilities; defaults to 5
            if not specified.

    Returns:
        mean_fault_tolerance: (float) The mean fault tolerance probability for the algorithm.
    """
    committee_seats = function(**params)
    
    # Calculate fault tolerance probabilities for the first algorithm
    prob_fault_tolerance = {
        f: calculate_fault_tolerance_probability(committee_seats, fault_tolerance=f)
        for f in arange(1, params.get("max_faults", 5) + 1)
        }
    
    prob_fault_tolerance = pd.DataFrame.from_dict(
        prob_fault_tolerance,
        orient="index",
        columns=["probability"],
        )
    
    # Compute fault tolerance performance score
    ft_score = compute_score(prob_fault_tolerance)
    
    return ft_score


def monte_carlo_simulation(num_trials: int = 50) -> tuple[np.ndarray, np.ndarray]:
    """
    Run the Monte Carlo simulation to compare Algorithms A and B across random scenarios.

    Args:
        num_trials: (int) The number of trials to run the simulation for. Defaults to 50.

    Returns:
        tuple[ndarray[Any, float], ndarray[Any, float]]: results_a, results_b
    """
    a = simulate_committee_federated
    b = simulate_proposed
    
    results_a = zeros(num_trials)
    results_b = zeros(num_trials)
    
    for i in tqdm(range(num_trials), desc="simulation trials"):
        alpha = sample_alpha()
        
        results_a[i] = algorithm(a, **alpha)
        results_b[i] = algorithm(b, **alpha)
    
    # Perform a paired t-test to determine if B is significantly better than A
    # difference: B - A
    t_stat, p_value = stats.ttest_rel(results_b, results_a, alternative='greater')
    
    # Display results
    print(f"Mean mA: {results_a.mean():.3f}, Mean mB: {results_b.mean():.3f}")
    print(f"Paired t-test result: t-statistic = {t_stat:.3f}, p-value = {p_value:.3f}")
    
    if p_value < 0.05:
        print("Conclusion: Algorithm B is significantly better than Algorithm A.")
    else:
        print("Conclusion: No statistically significant difference between A and B.")
    
    return results_a, results_b


if __name__ == "__main__":
    # Run the simulation
    results_a, results_b = monte_carlo_simulation(num_trials=1000)
    
    # ---------------------------
    # 1. Histogram each Score
    # ---------------------------
    plt.figure(figsize=(10, 6))
    plt.hist(results_a, bins=20, label="Algorithm A", alpha=0.5)
    plt.hist(results_b, bins=20, label="Algorithm B", alpha=0.5)
    plt.xlabel("Fault Tolerance Score")
    plt.ylabel("Frequency")
    plt.title("Histogram of Fault Tolerance Score")
    plt.legend()
    plt.show()

    differences = results_b - results_a  # difference: A - B
    
    # ---------------------------
    # 2. Histogram of Differences
    # ---------------------------
    plt.figure(figsize=(8, 6))
    sns.histplot(differences, bins=30, kde=True, color='skyblue', edgecolor='black')
    plt.xlabel("Difference (Algorithm B - Algorithm A)")
    plt.ylabel("Frequency")
    plt.title("Histogram of Differences in Scores")
    plt.axvline(
        np.mean(differences), color='red', linestyle='dashed', linewidth=2,
        label=f'Mean Difference = {np.mean(differences):.2f}',
        )
    plt.legend()
    plt.show()
    
    # ------------------------
    # 3. Boxplot of Differences
    # ------------------------
    plt.figure(figsize=(8, 4))
    sns.boxplot(x=differences, color='lightgreen')
    plt.xlabel("Difference (Algorithm B - Algorithm A)")
    plt.title("Boxplot of Differences in Scores")
    plt.show()
    
    # -------------------------------
    # 4. Scatter Plot of Paired Data
    # -------------------------------
    plt.figure(figsize=(8, 6))
    plt.scatter(results_a, results_b, alpha=0.5, color='purple', edgecolor='none')
    plt.xlabel("Algorithm A Score")
    plt.ylabel("Algorithm B Score")
    plt.title("Scatter Plot: Algorithm B vs. Algorithm A")
    plt.plot(
        [min(results_a), max(results_a)], [min(results_a), max(results_a)],
        linestyle='--', color='gray', label='Equality Line',
        )
    plt.legend()
    plt.show()
