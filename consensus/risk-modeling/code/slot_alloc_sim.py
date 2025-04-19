# !/usr/bin/env python
# -*- coding: utf-8 -*-
"""Consensus Slot Allocation Simulation Module

File: slot_alloc_sim.py
Date: 2025-04-16
Author: robert.jones@shielded.io
Description:
This module simulates the allocation of consensus slots to two types of block
validators:
1. Registered candidates: Stake-weighted allocation where slots are
    proportional to stake
2. Permissioned candidates: Uniform allocation across candidates

The goal of the algorithm is to assign slots in such a way that over a long
period (say, 100 million epochs), each candidate's slot count averages out to
its theoretical expectation. However, when committee sizes are relatively
small, the natural randomness can produce committees that are skewed or
insufficiently diverse—even to the extent that malicious candidates might
sometimes gain an over-representation.

The simulation allocates slots over multiple epochs to demonstrate the
statistical properties of the allocation algorithm. For registered candidates,
each receives a guaranteed floor(expected_slots) plus a probabilistic share
of remaining slots based on fractional remainders. For permissioned
candidates, slots are distributed evenly with remainders allocated
probabilistically.

Key Features:
- Stake-proportional slot allocation for registered candidates
- Uniform slot allocation for permissioned candidates
- Multi-epoch simulation with statistical analysis
- Configurable parameters (stake distribution, slot counts, epochs)

Dependencies:
- math: For mathematical calculations
- random: For probabilistic selection
- numpy: For statistical calculations
- tqdm: For progress bar display

Example use cases demonstrate different stake distributions and slot
allocations to analyze the fairness and variance of the allocation mechanism.

NOTE:
The `#%%` symbol in Python is often used in Jupyter notebooks or interactive
Python environments like JupyterLab or VS Code with Jupyter extension. It is
a cell marker that separates different sections of code or text within the
notebook. When you run a cell marked with `#%%`, it executes the code within
that cell.
"""
# %%
import math
import random
from tabnanny import verbose

import numpy as np
import pandas as pd
from tqdm import tqdm

import fault_tolerance


def simulate_epoch_federated(
    group_stakes: pd.DataFrame,
    committee_size: int = 100,
    num_federated: int = 10,
    seats_per_federated: int = 2,
    verbose: bool = False,
    plot_it=False,
    ) -> pd.DataFrame:
    """
    Creates a committee with registered and federated seats.

    The `simulate_epoch_federated` function allocates committee seats between two types of nodes: registered nodes
    (whose seat allocation is proportional to their stake) and federated nodes (which receive a fixed number of
    seats). It calculates the voting strength of each group, ensures they sum to 1.0, and returns a structured
    DataFrame containing the committee composition with seat assignments for both node types.
    
    Args:
        group_stakes (pd.DataFrame): DataFrame containing stake distribution.
        committee_size (int): Total size of the committee.
        num_federated (int): Number of federated nodes.
        seats_per_federated (int): Number of seats per federated node.
        verbose (bool): Whether to print detailed information.
            Default is False.
        plot_it (bool): Whether to plot the permissioned seats distribution.
            Default is False.

    Returns:
        pd.DataFrame: Committee seats information with kind and seat assignments.
    """
    # Get the number of permissioned participants (SPOs)
    group_size = group_stakes.shape[0]
    
    # Calculate the number of federated seats in the committee
    federated_seats_count = seats_per_federated * num_federated
    
    # Calculate the number of permissioned seats in the committee
    num_permissioned = committee_size - federated_seats_count
    
    # Create a series for the permissioned seats on the committee
    permissioned_seats = fault_tolerance.assign_commitee(
        group_stakes,
        committee_size=num_permissioned,
        plot_it=plot_it,
        ).rename("permissioned seats")
    
    # Calculate the voting strength of the permissioned seats
    permissioned_voting_strength = permissioned_seats.sum() / committee_size
    
    # Calculate the voting strength of the federated seats
    federated_voting_strength = federated_seats_count / committee_size
    
    # Assert that the voting strengths sum to 1.0
    assert (
            permissioned_voting_strength + federated_voting_strength == 1.0
    ), "Voting strength does not sum to 1.0"
    
    # Create a series for the federated seats on the committee
    federated_seats = pd.Series(
        np.ones(num_federated, dtype="int64") * seats_per_federated,
        index=[str(i) for i in range(group_size + 1, group_size + num_federated + 1)],
        dtype="int64",
        name="federated seats",
        )
    
    # Combine the federated and permissioned seats into a single DataFrame
    committee_seats = (
        pd.concat(
            [federated_seats, permissioned_seats],
            keys=["federated", "permissioned"],
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
            "Permissioned:"
            f"Number of seats = {num_permissioned} \n"
            f"Number of nodes = {group_size} \n"
            f"voting strength = {permissioned_voting_strength:.2%} \n"
            "________________________________________\n"
            "Federated:"
            f"Number of seats = {federated_seats_count} \n"
            f"Seats per node  = {seats_per_federated} \n"
            f"Number of nodes = {num_federated} \n"
            f"Voting strength = {federated_voting_strength:.2%}",
            )
    return committee_seats


def simulate_epoch_registered(
    registered_candidates: dict[str, int],
    total_slots: int,
    ) -> dict[str, int]:
    """Simulates one epoch for registered candidates.

    Each candidate's expected seat count is:
        E_i = total_slots * (stake / total_stake)

    Each candidate is guaranteed floor(E_i) seats. The remaining
    (total_slots - sum(floor(E_i))) are allocated one-by-one
    based on the fractional parts.

    Args:
        registered_candidates: Dictionary mapping candidate names to their
            stake (e.g., {'R1': 100, 'R2': 200, ...})
        total_slots: Number of available registered candidate seats (R)

    Returns:
        Dictionary mapping candidate names to allocated slots for this epoch
    """
    total_stake = sum(registered_candidates.values())
    
    assignments = {name: 0 for name in registered_candidates}
    guaranteed = {}  # floor(E_i)
    remainders = {}  # E_i - floor(E_i)
    
    # Calculate expected seats, guaranteed seats, and remainders
    for name, stake in registered_candidates.items():
        expected = total_slots * (stake / total_stake)
        guaranteed[name] = math.floor(expected)
        remainders[name] = expected - guaranteed[name]
        assignments[name] += guaranteed[name]
    
    # Calculate how many extra slots remain to be allocated
    total_guaranteed = sum(guaranteed.values())
    extra_slots = total_slots - total_guaranteed
    
    # Prepare for weighted random selection using
    # the fractional remainder as weights
    candidate_names = list(registered_candidates.keys())
    remainder_weights = [remainders[name] for name in candidate_names]
    
    for _ in range(extra_slots):
        # In the very rare case that all remainders are zero, select uniformly
        if sum(remainder_weights) == 0:
            chosen = random.choice(candidate_names)
        else:
            chosen = random.choices(
                candidate_names,
                weights=remainder_weights,
                k=1,
                )[0]
        assignments[chosen] += 1
    
    return assignments


def simulate_epoch_permissioned(
    permissioned_candidates: list[str],
    total_slots: int,
    ) -> dict[str, int]:
    """Simulates one epoch for permissioned candidates.

    For permissioned candidates, we assume a uniform expected value:
        E_i = total_slots / (number of permissioned candidates)

    Each candidate is guaranteed floor(E_i) seats.
    Leftover slots are allocated using a weighted random draw on the
    fractional parts.

    Args:
        permissioned_candidates: List of candidate names (e.g., ['P1', 'P2'])
        total_slots: Total number slots for permissioned candidates (P)

    Returns:
        Dictionary mapping candidate names to allocated slots
    """
    n = len(permissioned_candidates)
    assignments = {name: 0 for name in permissioned_candidates}
    
    # Calculate guaranteed seats and fractional parts.
    remainders = {}
    for name in permissioned_candidates:
        expected = total_slots / n
        guaranteed = math.floor(expected)
        remainders[name] = expected - guaranteed
        assignments[name] += guaranteed
    
    total_guaranteed = sum(math.floor(total_slots / n) for _ in permissioned_candidates)
    extra_slots = total_slots - total_guaranteed
    
    candidate_names = permissioned_candidates
    remainder_weights = [remainders[name] for name in candidate_names]
    
    for _ in range(extra_slots):
        if sum(remainder_weights) == 0:
            chosen = random.choice(candidate_names)
        else:
            chosen = random.choices(candidate_names, weights=remainder_weights, k=1)[0]
        assignments[chosen] += 1
    
    return assignments


def run_simulation(
    registered_candidates: dict[str, int],
    permissioned_candidates: list[str],
    num_registered_slots: int,
    num_permissioned_slots: int,
    num_epochs: int,
    seed: int = None,
    verbose: bool = False,
    ) -> tuple[dict[str, list[int]], dict[str, list[int]]]:
    """Runs simulation for a given number of epochs.

    For each epoch, simulates both the registered and permissioned candidate
    selection. Stores the number of slots each candidate gets and returns the
    cumulative results.

    Args:
        registered_candidates: Dictionary of registered candidates with
            associated stake
        permissioned_candidates: List of permissioned candidate names
        num_registered_slots: Number of slots available for registered candidates
        num_permissioned_slots: Number of slots available for permissioned candidates
        num_epochs: Number of epochs to simulate
        seed: Random seed for reproducibility (optional)
        verbose: bool, default False. If True, prints statistics information

    Returns:
        Two dictionaries mapping each candidate's name to list of slot counts
        per epoch
    """
    if seed is not None:
        random.seed(seed)
    
    registered_results = {name: [] for name in registered_candidates}
    permissioned_results = {name: [] for name in permissioned_candidates}
    
    for _ in tqdm(range(num_epochs), desc="Simulating epochs"):
        reg_assign = simulate_epoch_registered(registered_candidates, num_registered_slots)
        perm_assign = simulate_epoch_permissioned(permissioned_candidates, num_permissioned_slots)
        
        for name in registered_candidates:
            registered_results[name].append(reg_assign[name])
        for name in permissioned_candidates:
            permissioned_results[name].append(perm_assign[name])
       
    if verbose:
        print_statistics(registered_results)
        print_statistics(permissioned_results, candidate_type="Permissioned")
    
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

def print_statistics(
    results: dict[str, list[int]],
    candidate_type: str = "Registered",
    ) -> None:
    """Prints average and standard deviation of assigned seats for each candidate.

    Args:
        results: Dictionary mapping candidate names to lists of their slot
            assignments over epochs
        candidate_type: Label for the candidate group. Defaults to "Registered"
    """
    print(f"--- {candidate_type} Candidates Statistics over Epochs ---")
    for candidate, counts in results.items():
        avg = np.mean(counts)
        std = np.std(counts)
        print(f"Candidate {candidate}: Average seats = {avg:.3f}, Std Dev = {std:.3f}")
    print("")


def faults_tolerated(committee_seats: pd.Series) -> int:
    """
    Compute the number of faults tolerated by the committee
    based on the voting power of the committee members.

    Args:
        committee_seats (pd.Series): Series of committee seats
            with each row giving the number of seats assigned to
            each indexed member, both registered and permissioned.

    Returns:
        int: The number of faults tolerated by the committee.
    """
    voting_strength = committee_seats.sort_values(ascending=False).divide(
        committee_seats.sum(),
        )
    threshold = 1 / 3  # BFT finality risk threshold
    faults = np.where(np.cumsum(voting_strength) > threshold)[0][0]
    return faults


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


# %%
# ====== Use Case 1 ======
run_simulation(
    registered_candidates={
        "R1": 100,
        "R2": 200,
        "R3": 300,
        },
    permissioned_candidates=["P1", "P2"],
    num_registered_slots=10,  # Total registered slots
    num_permissioned_slots=5,  # Total permissioned slots
    num_epochs=10000,  # Number of epochs to simulate
    seed=1234567,  # Random seed for reproducibility
    verbose=True,
    )

# %%
# ====== Use Case 2 ======
run_simulation(
    registered_candidates={
        "R1": 100,
        "R2": 200,
        "R3": 300,
        "R4": 400,
        },
    permissioned_candidates=["P1", "P2"],
    num_registered_slots=15,  # Total registered slots
    num_permissioned_slots=5,  # Total permissioned slots
    num_epochs=10000,  # Number of epochs to simulate
    seed=1234567,  # Random seed for reproducibility
    verbose=True,
    )
# %%
# ====== Use Case 3 ======
run_simulation(
    registered_candidates={
        "R1": 100,
        "R2": 200,
        "R3": 300,
        "R4": 400,
        },
    permissioned_candidates=["P1", "P2"],
    num_registered_slots=20,  # Total registered slots
    num_permissioned_slots=5,  # Total permissioned slots
    num_epochs=10000,  # Number of epochs to simulate
    seed=1234567,  # Random seed for reproducibility
    verbose=True,
    )
# %%
# ====== Use Case 4 ======
run_simulation(
    registered_candidates={
        "R1": 100,
        "R2": 200,
        "R3": 300,
        "R4": 400,
        },
    permissioned_candidates=["P1", "P2"],
    num_registered_slots=21,  # Total registered slots
    num_permissioned_slots=5,  # Total permissioned slots
    num_epochs=10000,  # Number of epochs to simulate
    seed=1234567,  # Random seed for reproducibility
    verbose=True,
    )

# %%
committee_seats = run_simulation(
    registered_candidates={
        "R1": 100,
        "R2": 200,
        "R3": 300,
        "R4": 400,
        "R5": 500,
        "R6": 600,
        "R7": 700,
        "R8": 800,
        "R9": 900,
        "R10": 1000,
        },
    permissioned_candidates=["P1", "P2", "P3", "P4", "P5"],
    num_registered_slots=15,  # Total registered slots
    num_permissioned_slots=5,  # Total permissioned slots
    num_epochs=10000,  # Number of epochs to simulate
    seed=1234567,  # Random seed for reproducibility
    verbose=True,
    )

# %%
committee_seats

# %%
registered_candidates = {
    "R1": 100,
    "R2": 200,
    "R3": 300,
    "R4": 400,
    "R5": 500,
    "R6": 600,
    "R7": 700,
    "R8": 800,
    "R9": 900,
    "R10": 1000,
    }

group_stakes = pd.DataFrame.from_dict(
    registered_candidates,
    orient="index",
    columns=["stake"],
    )
group_stakes["stake_weight"] = group_stakes["stake"] / group_stakes["stake"].sum()

group_stakes

# %%
# Simulate the allocation of committee seats over multiple epochs
num_epochs = 10000
committee_list = []
for epoch in range(num_epochs):
    # Assign committee seats for the current epoch
    committee = simulate_epoch_federated(
        group_stakes,
        committee_size=20,
        num_federated=5,
        seats_per_federated=1,
        )
    committee_list.append(committee.seats)

assert len(committee_list) == num_epochs, "Number of epochs does not match."

committee_seats_federated = pd.concat(committee_list, keys=range(num_epochs), axis=1).sort_index().T

committee_seats_federated
# %%
def compare_fault_tolerance_probabilities(
    committee_seats: pd.DataFrame,
    committee_seats_federated: pd.DataFrame,
    max_faults: int = 5,
    first_name: str = "Proposed Algo",
    second_name: str = "Federated Algo"
    ) -> pd.DataFrame:
    """
    Compares fault tolerance probabilities between two committee seat allocation methods.

    Args:
        committee_seats: DataFrame of the first committee seat allocation
        committee_seats_federated: DataFrame of the second committee seat allocation
        max_faults: Maximum number of faults to evaluate (default: 5)
        first_name: Label for the first algorithm (default: "Proposed Algo")
        second_name: Label for the second algorithm (default: "Federated Algo")

    Returns:
        DataFrame comparing fault tolerance probabilities of both approaches
    """
    # Calculate fault tolerance probabilities for the first algorithm
    prob_fault_tolerance = {}
    for f in range(max_faults):
        p = calculate_fault_tolerance_probability(committee_seats, fault_tolerance=f)
        prob_fault_tolerance[f] = p
    
    prob_fault_tolerance = pd.DataFrame.from_dict(
        prob_fault_tolerance,
        orient="index",
        columns=["probability"],
        )
    
    # Calculate fault tolerance probabilities for the second algorithm
    prob_fault_tolerance_federated = {}
    for f in range(max_faults):
        p = calculate_fault_tolerance_probability(committee_seats_federated, fault_tolerance=f)
        prob_fault_tolerance_federated[f] = p
    
    prob_fault_tolerance_federated = pd.DataFrame.from_dict(
        prob_fault_tolerance_federated,
        orient="index",
        columns=["probability"],
        )
    
    # Combine the results
    prob_fault_tolerance_compared = pd.concat(
        [prob_fault_tolerance, prob_fault_tolerance_federated],
        keys=[first_name, second_name],
        axis=1,
        names=["faults"],
        )
    
    return prob_fault_tolerance_compared
# %%
compare_fault_tolerance_probabilities(committee_seats, committee_seats_federated)
# %%
# Output:
# faults Proposed Algo Federated Algo
#          probability    probability
# 0             1.0000         1.0000
# 1             0.9998         0.9783
# 2             0.8215         0.3113
# 3             0.0631         0.0052
# 4             0.0000         0.0000

# %%
