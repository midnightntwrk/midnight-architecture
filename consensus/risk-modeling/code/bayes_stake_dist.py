#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Module: bayes_stake_dist.py

Created on 2025-03-23 by Rob Jones <robert.jones@shielded.io>

This script calculates the group stake distribution using a Bayesian approach.
It uses a Dirichlet distribution as a generative model of the probabilities of
different participants being selected for a committee, based on their stake
sizes. The model is implemented using PyMC and ArviZ for sampling and
visualization.

The script includes:
- Bayesian model definition using PyMC
- Sampling from the posterior distribution
- Posterior predictive checks
- Visualization of the results
- Saving and loading the model and trace
- Saving and loading posterior predictive samples
"""
# %%
import random
import matplotlib.pyplot as plt
from scipy.stats import gamma
import pymc as pm
import arviz as az
from data import load_data
from participation_lib import get_stake_distribution, assign_commitee
from typing import List, Dict, Any, Union
import numpy as np
import pandas as pd
import argparse
from pathlib import Path
from joblib import Parallel, delayed


def load_population(input_data_file):
    """
    Load and clean the data from the specified CSV file.

    Args:
        input_data_file (Path or str): The path to the CSV data file.

    Returns:
        pd.DataFrame: The cleaned DataFrame containing SPO information.
    """
    print("Loading data...")
    population = load_data(input_data_file)
    print(population.info())
    print(population.describe())
    return population


# %% [markdown]
# ## Data Preprocessing
# The get_stake_distribution function is used to simulate the stake distribution
# of the population. It takes the following parameters:
# - `population`: The DataFrame containing the population data.
# - `group_size`: The size of the group to be sampled.
# - `num_iter`: The number of iterations for the simulation.
# - `plot_it`: A boolean flag indicating whether to plot the distribution.
#
# The function returns a DataFrame containing the simulated stake distribution.
# The function simulates the stake distribution by randomly sampling from the
# population and calculating the stake weights for each participant.
# The stake weights are normalized to sum to 1, representing the relative stake
# of each participant in the group.

# %%


def sample_group(
    population: pd.DataFrame,
    stake_size: List[int],
    group_size: int,
    plot_it: bool = False,
    num_ticks: int = 10,
) -> pd.DataFrame:
    """Sample a group of participants ensuring
    one has the given stake size(s).

    Args:
        population (pd.DataFrame): The population of registered SPOs.
        stake_size (List[int]): The stake size(s) to include in the group.
        group_size (int): The number of participants in the group.
        plot_it (bool): Whether to plot the distribution of stake weights.
        num_ticks (int): The number of ticks to display on the x-axis.

    Returns:
        pd.DataFrame: A DataFrame containing the group of participants.
    """
    # Sample a group of participants with the chosen stake size
    # at the beginning of the group (starting from index 1)
    group = pd.DataFrame()
    for stake in stake_size:
        # Find rows with the given stake value
        subset = population[population["stake"] == stake]
        if not subset.empty:
            # If present, sample one matching record
            selected = subset.sample(1, replace=False)
        else:
            # If not present, sample one record and set
            # its stake values to the given stake size
            selected = population.sample(1, replace=False).copy()
            selected["stake"] = stake
            selected["stake_weight"] = stake
        # Add the selected record to the group
        group = pd.concat([group, selected], ignore_index=True)
    if len(group) == 0:
        # No participants found with stake value, so add it artifically
        group = population.sample(1, replace=False)
        group["stake"] = stake
        group["stake_weight"] = stake
        group.index = [0]
    # Add to that group the remaining participants
    # sampled from the population, excluding the selected participant
    # and sort the group by stake value from highest to lowest
    other_participants = get_stake_distribution(
        population,
        group_size=group_size - 1,
        num_iter=1000,  # 1 for exact instance, >> 1 for smoothed
        plot_it=False,
    ).sort_values(by="stake", ascending=False)

    # Concatenate the selected participant with the other participants
    group = pd.concat([group, other_participants], ignore_index=True)
    # Reindex the group to start from 1
    group.index = group.index + 1
    # and sort the group by stake value from highest to lowest,
    # save for the selected stake in the first position and finally
    # normalize the stake values as "stake_weight"
    group["stake_weight"] = group.stake / group.stake.sum()

    # Plot the distribution of the stake weights
    if plot_it:
        plt.figure("Distribution of the Stake Weights", figsize=(10, 6))
        plt.bar(group.index, group.stake_weight, color="skyblue")
        # Choose a fixed number of ticks (e.g., 10) based on domain size
        tick_positions = np.linspace(
            group.index.min(),
            group.index.max(),
            num_ticks,
            dtype=int,
        )
        plt.xticks(tick_positions)
        plt.xlabel("Participant ID")
        plt.ylabel("Stake Weight")
        plt.title("Stake Weights of Sampled Participants")
        plt.show()

    return group


def predictive_checks(
    trace: az.InferenceData,
    model: pm.Model,
    plot_it: bool = False,
) -> pd.DataFrame:
    """Perform posterior predictive checks and return the results.

    Args:
        trace (az.InferenceData): The posterior samples.
        model (pm.Model): The PyMC model.
        plot_it (bool): Whether to plot the posterior predictive checks.
            Default is False.

    Returns:
        pd.DataFrame: A DataFrame containing the posterior predictive samples.
    """
    with model:
        ppc = pm.sample_posterior_predictive(
            trace=trace,
            var_names=["observed"],
            random_seed=42,
        )
    # The arviz library is used to visualize the posterior trace and summarize
    # the results (posterior means, credible intervals, etc.).
    print(pm.summary(trace, hdi_prob=0.95))
    if plot_it:
        pm.plot_trace(trace)
        pm.plot_posterior(trace)

    # Posterior predictive checks
    with model:
        ppc = pm.sample_posterior_predictive(
            trace=trace,
            var_names=["observed"],
            random_seed=42,
        )
    print(az.summary(ppc, hdi_prob=0.95))

    if plot_it:
        # Visualize posterior predictive checks
        fig = plt.figure("Posterior Predictive Check", figsize=(12, 6))
        ax = fig.add_subplot(111)
        az.plot_ppc(ppc, kind="kde", ax=ax)
        # az.plot_ppc(ppc, kind="scatter", ax=ax)
        plt.title("Posterior Predictive Check (Cumulative)")
        plt.xlabel("observed", fontsize="small")
        plt.ylabel("Cumulative Probability", fontsize="small")
        plt.legend(title="Posterior Predictive Checks", fontsize="small")
        plt.show()

    return ppc


def save_trace(trace: az.InferenceData, filename: str) -> None:
    """
    Save the posterior trace to a NetCDF file.

    Args:
        trace (az.InferenceData): The trace from posterior sampling.
        filename (str): The filename for saving the trace.

    Returns:
        None
    """
    # Save the trace to a NetCDF file
    trace_filename = Path(filename).with_suffix(".nc")
    az.to_netcdf(trace, trace_filename)


def load_trace(filename: str) -> az.InferenceData:
    """
    Load the trace from a NetCDF file.

    Args:
        filename (str): Filename for the trace data.
    Returns:
        az.InferenceData: The loaded trace.
    """
    trace_filename = Path(filename).with_suffix(".nc")
    # Load the trace from a NetCDF file
    trace = az.from_netcdf(trace_filename)
    return trace


def compute_and_adjust_seat_counts(
    group: pd.DataFrame,
    committee_size: int,
    plot_it: bool = False,
) -> np.ndarray:
    """
    Compute and adjust seat counts for a given group and committee size.

    This function assigns committee seats using the assign_commitee function,
    rounds the seat counts using floor, allocates any remaining seats based on
    the decimal remainders, and verifies that the total equals the committee size.

    Args:
        group (pd.DataFrame): DataFrame containing the group of participants.
        committee_size (int): Total number of committee seats.
        plot_it (bool): Whether to plot the seat assignment (default is False).

    Returns:
        np.ndarray: Adjusted seat counts as an integer array.
    """
    # Observed data (counts of committee seats for each participant)
    seats = assign_commitee(
        group,
        committee_size=committee_size,
        plot_it=plot_it,
    )
    seat_counts = seats["seat_counts"]

    # Initial integer allocation using floor
    rounded_seats = np.floor(seat_counts).astype(int)
    remainder = committee_size - rounded_seats.sum()

    if remainder > 0:
        # Compute decimal remainders
        decimals = seat_counts - np.floor(seat_counts)
        # Get indices sorted by descending order of remainders
        indices = decimals.sort_values(ascending=False).index
        # Allocate the remaining seats to those with highest decimals
        for idx in indices[:remainder]:
            rounded_seats[idx] += 1
    elif remainder < 0:
        # If over-allocated, subtract seats from those with smallest remainders
        decimals = seat_counts - np.floor(seat_counts)
        indices = decimals.sort_values(ascending=True).index
        for idx in indices[: abs(remainder)]:
            rounded_seats[idx] -= 1

    seat_counts = rounded_seats
    # Confirm the sum equals committee_size
    assert (
        seat_counts.sum() == committee_size
    ), f"Sum of seats {seat_counts.sum()} does not equal committee size {committee_size}"

    print("Sum of seats:", seat_counts.sum())
    return seat_counts


def plot_gamma_prior(
    group_size: int,
    alpha_param: float = 2.0,
    beta_param: float = 1.0,
    num_points: int = 1000,
):
    """
    Visualize the Gamma distribution used as a prior for the Dirichlet hyperparameter.

    Args:
        group_size (int): Maximum x-axis value (e.g., size of the group).
        alpha_param (float): Shape parameter of the Gamma distribution (default: 2.0).
        beta_param (float): Rate parameter of the Gamma distribution (default: 1.0).
            In scipy's gamma, scale = 1/beta.
        num_points (int): Number of points to generate for the x-axis (default: 1000).
    """
    scale_param = 1.0 / beta_param  # convert beta to scale for scipy's gamma
    x = np.linspace(0, group_size, num_points)
    y = gamma.pdf(x, a=alpha_param, scale=scale_param)
    plt.figure("Gamma Distribution", figsize=(10, 6))
    plt.plot(x, y, label=f"Gamma(α={alpha_param}, β={beta_param})")
    plt.title(f"Gamma Distribution (α={alpha_param}, β={beta_param})")
    plt.xlabel("x")
    plt.ylabel("Probability Density")
    plt.legend()
    plt.show()


def run_bayesian_model(
    committee_size: int,
    seat_counts: np.ndarray,
    group: pd.DataFrame,
    target_accept: float = 0.98,
    gamma_alpha=2.0,
    gamma_beta=1.0,
) -> Dict[str, Any]:
    """
    Run the hierarchical Bayesian model using a Dirichlet-Multinomial framework.

    Args:
        committee_size (int): Number of committee seats (k).
        seat_counts (np.ndarray): Observed counts of seats per participant.
        group (pd.DataFrame): DataFrame containing the group of participants.
        target_accept : float in [0, 1]. The step size is tuned such that we
              approximate this acceptance rate. Higher values like 0.9 or 0.98
              often work better for problematic posteriors. This argument is
              passed directly to sample. Default is 0.98.
        gamma_alpha (float): Shape hyper-parameter of the Gamma distribution,
            which is used as the hyper-prior on the Dirichlet distribution.
            Default is 2.0.
        gamma_beta (float): Rate hypter-parameter of the Gamma distribution.
            Default is 1.0.

    Returns:
        Dict[str, Any]: A dictionary containing the the following key:values
        - "concentration": The concentration of the Dirichlet distribution.
        - "mean_prob": The mean probability of each participant.
        - "model": The PyMC model object.
        - "trace": The posterior samples obtained from the MCMC sampling.
    """
    k: int = committee_size  # number of committee seats
    n: int = len(group)  # number of participants in the group
    X: np.ndarray = (
        seat_counts  # observed data: counts of committee seats per participant
    )
    with pm.Model() as model:
        # Priors for Dirichlet hyperparameters (Gamma prior)
        alpha = pm.Gamma("alpha", alpha=2.0, beta=1.0, shape=n)

        # Dirichlet distribution for probabilities (p)
        p = pm.Dirichlet("p", a=alpha)

        # Multinomial likelihood for observed counts
        pm.Multinomial("observed", n=k, p=p, observed=X)

        # Sampling from the posterior
        trace = pm.sample(
            return_inferencedata=True,
            target_accept=target_accept,
        )
    # Analyze Posterior Samples of Alpha
    posterior_mean_alpha: np.ndarray = (
        trace.posterior["alpha"].mean(dim=("chain", "draw")).values
    )
    # Concentration of the Dirichlet distribution:
    concentration = posterior_mean_alpha.sum()

    # Mean probability of each participant, which normalizes
    # the posterior mean of alpha by the concentration so it sums to 1:
    mean_prob = posterior_mean_alpha / concentration

    # Extend the mean probabilities to include the concentration
    # at the first position (index 0) of the array
    # and the mean probabilities at the remaining positions
    # (index 1 to n).
    extended_array = np.empty(mean_prob.shape[0] + 1)
    extended_array[0] = concentration
    extended_array[1:] = mean_prob

    return {
        "mean_prob": extended_array,
        "model": model,
        "trace": trace,
    }


def main_model(
    population: pd.DataFrame,
    stake_size: Union[int, List[int]],
    group_size: int = 50,
    committee_size: int = 10,
    plot_it: bool = False,
    debug_it: bool = False,
    verbose: bool = False,
) -> Dict[str, Any]:
    """
    Test the Bayesian model by running it and performing posterior
    predictive checks.

    Args:
        population (pd.DataFrame): The population of registered SPOs.
        stake_size (Union[int, List[int]]): The stake size(s) to include
            in the group. If an integer, it will be converted to a list.
        group_size (int): The number of participants in the group. Default
            is 50 for testing.
        committee_size (int): The number of committee seats. Default is 10
            for testing.
        plot_it (bool): Whether to plot the distribution of stake weights.
            Default is False.
        debug_it (bool): Whether to debug the model. Default is False.
        verbose (bool): Whether to print debug information. Default is False.

    Returns:
        Dict[str, Any]: A dictionary containing the the following key:values
        - "concentration": The concentration of the Dirichlet distribution.
        - "mean_prob": The mean probability of each participant.
        - "model": The PyMC model object.
        - "trace": The posterior samples obtained from the MCMC sampling.
    """
    print("Running the Bayesian model for stake sizes:", stake_size)
    print("Group size:", group_size)
    print("Committee size:", committee_size)

    # Ensure stake_size is a list even if an integer is provided
    if isinstance(stake_size, int):
        stake_size = [stake_size]

    # Sample a group of participants with the chosen stake size
    # at the beginning of the group (at index 1)
    group = sample_group(
        population,
        stake_size,
        group_size,
        plot_it=plot_it,
    )
    if verbose:
        print("Sampled group of participants:")
        print(group.head(10))

    seat_counts = compute_and_adjust_seat_counts(
        group,
        committee_size=committee_size,
        plot_it=plot_it,
    )

    # Plot the Gamma distribution used as a prior distribution
    # on the Dirichlet hyperparameter α
    if plot_it:
        plot_gamma_prior(group_size=group_size)

    # Run the Bayesian model
    result = run_bayesian_model(
        committee_size=committee_size,
        seat_counts=seat_counts,
        group=group,
    )
    model = result["model"]

    # Optional: Debug the model (if debugging is needed)
    if debug_it:
        # Perform posterior predictive checks
        print("Performing posterior predictive checks...")
        trace = result["trace"]
        result["ppc"] = predictive_checks(trace, model, plot_it)

    return result


def main(
    population: pd.DataFrame,
    stake_size: List[int],
    committee_size: int = 200,
    group_size: List[int] = [100, 200, 300],
    downsample: float = 1.0,
    debug_it: bool = False,
    plot_it: bool = False,
    verbose: bool = False,
) -> Dict[int, Dict[int, np.ndarray]]:
    """
    Main function to run the Bayesian model for different stake sizes
    and group sizes.

    Args:
        population (pd.DataFrame): The population of registered SPOs.
        stake_size (List[int]): The stake size(s) to include in the group.
            If empty list, a random selection of a stake size is chosen
            from the observed data.
        committee_size (int): The number of committee seats. Default is 200.
        group_size (List[int]): List of group sizes to sample. Default is
            [100, 200, 300].
        downsample (float): Fraction of the observed stake sizes to sample.
            Default is 1.0 (100%).
        debug_it (bool): Whether to debug the model. Default is False.
        plot_it (bool): Whether to plot the distribution of stake weights.
            Default is False.
        verbose (bool): Whether to print debug information. Default is False.

    Note:
        Without loss of generality, the committee size can be set to the
        group size to ensure that the model is not sensitive to the committee
        size and avoid overfitting. We are inferring the pseudo counts of
        committee seats for each participant based on their stake size (weight).
        Once inferred, the pseudo counts can be used to compute the
        expected number of committee seats for each participant in the group
        by normalizing the pseudo counts to sum to 1 and multiplying by
        the committee size, k.

    Returns:
        dict: A dictionary containing the psuedo counts for different
        stake sizes and group sizes.
    """
    print("Simulating model for different stake and group sizes...")
    print("Committee size:", committee_size)
    print("Group sizes:", group_size)
    print("Stake sizes:", stake_size)
    print("Downsample:", downsample)
    # =============================================================
    # Get the unique stake sizes in the population and and sort in
    # descending order. If stake_size is not provided, sample from
    # the population
    if len(stake_size) > 0:
        # Use the provided stake size list
        unique_stakes = np.array(stake_size)
    else:
        # Get the stake size from the population
        unique_stakes = population["stake"].unique()
    # Downsample the stake sizes if needed
    num_stakes = int(len(unique_stakes) * downsample)
    assert num_stakes > 0, "No stake size found in the population."
    # Randomly sample the stake size from the population
    stake_sizes = np.random.choice(unique_stakes, num_stakes, replace=False)
    stake_sizes = np.sort(stake_sizes)[::-1]  # sort in descending order
    print(
        "Number of unique stake sizes in the population:\n"
        f"\t{num_stakes} out of {len(unique_stakes)} "
        f"({num_stakes/len(unique_stakes):.1%})"
    )
    # =============================================================
    # Parallelize the computation using joblib and run the model
    # for each combination of stake and group size

    def process_stake_group(s, n):
        """Function to execute for each combination of stake and group size"""
        print(f"Stake size: {s}")
        print(f"Group size: {n}")
        result = main_model(
            population,
            stake_size=[s],
            group_size=n,
            committee_size=committee_size,
            plot_it=plot_it,
            debug_it=debug_it,
            verbose=verbose,
        )
        return s, n, result

    print("Running the model in parallel...")
    results = Parallel()(  
        # Process each combination of stake size and group size 
        delayed(process_stake_group)(s, n) for s in stake_sizes for n in group_size
    )
    # =================================================================
    # Store the results in a dictionary
    # where the keys are the stake sizes and group sizes
    # and the values are the result dictionaries
    result_dict = {}
    for stake, group, data in results:
        if stake not in result_dict:
            result_dict[stake] = {}
        result_dict[stake][group] = data
    
    return result_dict


def convert_results_to_dataframe(result: dict) -> pd.DataFrame:
    """
    Convert a nested results dictionary into a DataFrame with a MultiIndex for rows.
    Each row corresponds to a (stake size, group size, data key) triple.

    Args:
        result (dict): Nested dictionary with structure:
            {stake_size: {group_size: {data_key: data_value, ...}, ...}, ...}

    Returns:
        pd.DataFrame: DataFrame with MultiIndex rows ("Stake Size", "Group Size", "Data").
                    The DataFrame columns are set to range based on the number of pseudo counts.
    """
    rows = []
    cols = []
    data = []
    for stake_size_key, groups in result.items():
        for group_size_key, result_dict in groups.items():
            for data_key, data_val in result_dict.items():
                if data_key in ["model", "trace", "ppc"]:
                    continue
                rows.append((stake_size_key, group_size_key, data_key))
                cols.append(data_key)
                data.append(data_val)
    multi_index = pd.MultiIndex.from_tuples(
        rows, names=["Stake Size", "Group Size", "Data"]
    )
    results_df = pd.DataFrame(data, index=multi_index)
    # Set the column names to [0, 1, ..., max_index] based on the length of data.
    results_df.columns = range(results_df.shape[1])
    return results_df


# %%
# Example usage during testing:
if __name__ == "__main__":

    # ====================================================================
    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description=(
            "Run the group stake distribution calculation with "
            "optional input/output file paths."
        )
    )
    default_data_dir = Path(__file__).parent.parent / "data"
    parser.add_argument(
        "--input-data-file",
        type=Path,
        default=default_data_dir / "pooltool-cleaned.csv",
        help="Path to the input CSV data file (default: %(default)s)",
    )
    parser.add_argument(
        "--output-data-file",
        type=Path,
        default=default_data_dir / "bayes_stake_dist_output.csv",
        help="Path to the output CSV file (default: %(default)s)",
    )
    parser.add_argument(
        "--downsample",
        type=float,
        default=1.0,
        help="Percentage of the population to sample (0.0-1.0).",
    )
    parser.add_argument(
        "--group-size",
        type=int,
        nargs="+",
        default=100,
        help="Number of participants in the group (default: 100)",
    )
    parser.add_argument(
        "--committee-size",
        type=int,
        default=50,
        help="Number of seats in the committee (default: 50)",
    )
    parser.add_argument(
        "--stake-size",
        type=int,
        nargs="+",
        default=None,
        help="List of stake sizes to analyze (default: None)",
    )
    parser.add_argument(
        "--all-in",
        action="store_true",
        default=False,
        help=(
            "Process all stake sizes specified in '--stake-size' "
            "simultaneously instead of individually."
        ),
    )
    parser.add_argument(
        "--plot",
        action="store_true",
        default=False,
        help="Enable plotting of data (default: False)",
    )
    parser.add_argument(
        "--test",
        action="store_true",
        default=False,
        help="Run in test mode",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=None,
        help="Random number generator seed (default: None)",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        default=False,
        help="Enable verbose output (default: False)",
    )
    args = parser.parse_args()
    # ====================================================================
    # Initialize variables
    INPUT_DATA_FILE = args.input_data_file
    OUTPUT_DATA_FILE = args.output_data_file
    TEST_IT = args.test
    PLOT_IT = args.plot
    VERBOSE = args.verbose
    DOWNSAMPLE = args.downsample
    GROUP_SIZE = args.group_size
    COMMITTEE_SIZE = args.committee_size
    STAKE_SIZE = args.stake_size
    ALL_IN = args.all_in
    # ====================================================================
    # Set the random seed for reproducibility
    if args.seed is not None:
        random.seed(args.seed)
        np.random.seed(args.seed)
    # ====================================================================
    # Load the population data
    print(f"Input data file: {INPUT_DATA_FILE}")
    population = load_population(INPUT_DATA_FILE)
    if DOWNSAMPLE < 1.0:
        print(f"Downsampling population to {DOWNSAMPLE:.1%} of original size.")
        population_size = int(len(population) * DOWNSAMPLE)
    else:
        print("Using full population size.")
        population_size = len(population)
    print(f"Population size: {population_size}")
    # Get the smoothed stake distribution of the population
    # and downsample and plot it if if desired
    population = get_stake_distribution(
        population,
        group_size=population_size,
        num_iter=1,  # 1 for exact instance, >> 1 for smoothed
        plot_it=PLOT_IT,
    )
    # ====================================================================
    # Prepare the stake sizes for processing
    if isinstance(STAKE_SIZE, list):
        # If stake size is a list, convert to a list of integers
        stake_size = [int(s) for s in STAKE_SIZE]
    elif STAKE_SIZE is None:
        stake_size = []
    if ALL_IN:
        # If all-in mode is enabled, convert to a list of lists so that
        # all stake sizes are processed at once in a batch
        stake_size = [stake_size]
    # ====================================================================
    if TEST_IT:
        # Test the model with a specific stake, group, and committee sizes
        print(
            f"Testing with stake size {stake_size}",
            f"and group size {GROUP_SIZE}.",
        )
        # Run the model for each combination of stake and group size
        # and accumulate the psuedo counts.
        result = {}
        for stake in stake_size:
            for group in GROUP_SIZE:
                result_sg = main_model(
                    population=population,
                    stake_size=stake,
                    group_size=group,
                    committee_size=COMMITTEE_SIZE,
                    plot_it=PLOT_IT,
                    debug_it=TEST_IT,
                    verbose=VERBOSE,
                )
                # Append the result dictionary to the result
                if isinstance(stake, list):
                    for s in stake:
                        result[s] = {group: result_sg}
                else:
                    result[stake] = {group: result_sg}
    # ====================================================================
    else:
        # Main function to run the model
        result = main(
            population,
            stake_size=stake_size,
            committee_size=COMMITTEE_SIZE,
            group_size=GROUP_SIZE,
            downsample=DOWNSAMPLE,
            debug_it=TEST_IT,
            plot_it=PLOT_IT,
            verbose=VERBOSE,
        )
    # ====================================================================
    # Convert the results to a DataFrame and save to a CSV file
    results_df = convert_results_to_dataframe(result)
    
    OUTPUT_DATA_FILE = Path(args.output_data_file)
    OUTPUT_DATA_FILE.parent.mkdir(parents=True, exist_ok=True)
    # Ensure the output file has the correct suffix
    if OUTPUT_DATA_FILE.suffix != ".csv":
        OUTPUT_DATA_FILE = OUTPUT_DATA_FILE.with_suffix(".csv")
    try:
        # Save the DataFrames to a CSV file
        results_df.to_csv(OUTPUT_DATA_FILE, index=True)
        print(f"Psuedo counts prediction saved to file {OUTPUT_DATA_FILE}.")

    except Exception as e:
        print(f"Error saving result: {e}")
    if VERBOSE:
        print("Predictions DataFrame:")
        print(results_df.head(10))
    print("Done.")
    # ====================================================================
    # End of script

# %%
