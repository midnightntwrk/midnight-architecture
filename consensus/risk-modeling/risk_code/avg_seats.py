#!/usr/bin/env python
# coding: utf-8
#
# Module: avg_seats.py
# Author: Rob Jones
# Created: 2025-03-20
#
# Description:
# This module computes the expected number of committee seats that an
# SPO participant can expect to receive based on their stake, and the
# number of participants in the group, and the committee size. This is
# done by simulating the committee selection process over multiple
# iterations and calculating the average number of committee seats
# that each participant receives. The results are then plotted to
# visualize the distribution of committee seats for each participant.
#
# Simulation Steps:
# 1. For each distinct stake value in the population, sample with replacement
#    a group of participants of group_size that contain that stake value and
#    a balance of other stake values from the population.
# 2. Assign a committee of size committee_size from the group of participants
#    based on the stake weight of each participant.
# 3. Repeat the above steps for num_iter iterations to get a distribution of
#    committee seat counts for each participant for the given stake value.
# 4. Calculate the average committee seat count for each participant and store
#    the results in a DataFrame.
# 5. Repeat the above steps for each distinct stake value in the population.
# 6. Save the results to a parquet file for further use.
#
# Inputs:
# The module requires the pooltool-cleaned.csv file which contains
# the population of registered SPOs and their stake information.
#
# Outputs:
# The results are also saved as a 3-d array with dimensions
# (distinct stake in pool, participant group size, committee size) where
# the latter two dimensions are in the set {100, 200, ..., 500}.
# The results are then saved to a parquet file for further use.
# %%
# Load the required libraries
import random
import numpy as np
import pandas as pd
import time
from scipy import stats
from multiprocessing import Pool, cpu_count

from participation_lib import (
    load_data,
)

# CONFIGFURABLES
# The following constants are used to configure the simulation.
# They define the input and output data files, the population size,
# the maximum group size, and the maximum committee size.
# These constants can be adjusted to change the behavior of the simulation.
# Input and output data files
# The input data file is expected to be a CSV file containing the population
# of registered SPOs and their stake information.
# The output data file is where the results of the simulation will be saved.
# The input data file should contain the following columns:
# - id: The unique identifier for each SPO.
# - stake: The stake value of each SPO.
# - stake_percent: The percentage of the total stake that each SPO holds.
# The output data file will contain the average committee seat counts for
# each participant in the population, along with the confidence intervals.
# The results will be saved in a CSV file format.

# Data files
INPUT_DATA_FILE = "../data/pooltool-cleaned.csv"
OUTPUT_DATA_FILE = "../data/avg_seat_counts.csv"

# Set the population size for the simulation.
population_size = 500  # maximum number of SPOs assumed registered
max_group_size = 500  # maximum number of SPOs in a participation group
max_committee_size = 500  # maximum number of seats in a committee

# Load the data from the CSV file
print("Loading data...")
# The load_data function reads the data from the specified CSV file
# and returns a DataFrame. The data is expected to contain information
# about the stake pool operators (SPOs) and their respective stake values.
# The data is cleaned to remove any missing or zero stake values.

# The cleaned data is then returned as a DataFrame.
population = load_data(INPUT_DATA_FILE)
print(population.info())
print(population.describe())

# The data is expected to contain the following columns:
# - id: The unique identifier for each SPO.
# - stake: The stake value of each SPO.
# - stake_percent: The percentage of the total stake that each SPO holds.
# For testing, let's take a smaller sample of the population
population = population.sample(500, random_state=42)

# How many unique stake values are there in the population?
population_size = len(population)
stake_values = np.sort(population["stake"].unique())
num_stakes = len(stake_values)
print(
    "Number of unique stake values in the population:\n"
    f"\t{num_stakes} out of {population_size} ({num_stakes/population_size:.1%})"
)

assert (
    population_size <= max_group_size
    and population_size <= max_committee_size
    and population_size <= len(population)
), "Population size exceeds the maximum group or committee size."

# The risk_code computes the half-width of a 95% confidence interval for the
# mean using the t-distribution. Here's a step-by-step breakdown:
#
# Sample Standard Deviation (sd_val):
# Using data.std(ddof=1) calculates the sample standard deviation. The
# parameter ddof=1 means "delta degrees of freedom" is 1, which gives the
# unbiased estimate of the standard deviation in a sample.
#
# t-distribution and Confidence Interval:
# The t-distribution is used here because when you estimate the standard
# deviation from a sample, there's extra uncertainty. With degrees of
# freedom df=iter_count - 1, the t-distribution compensates for that
# uncertainty.
#
# The cumulative probability up to the lower tail is 0.025.
# To capture the upper bound, you use the complementary cumulative
# probability: 1 - 0.025 = 0.975.
# Thus, stats.t.ppf(0.975, df=iter_count - 1) gives the critical value such
# that 97.5% of the t-distribution lies below it, ensuring the interval
# covers the middle 95% of the distribution.
#
# Combining with the Standard Error:
# The half-width (or margin of error) of the confidence interval is computed
# as:
#
#   1. The t-critical value from the t-distribution at 97.5% quantile.
#   2. Multiplied by the standard error (sd_val / np.sqrt(iter_count)), which
#      adjusts the standard deviation based on the sample size.
#
# This product yields the value by which you add/subtract from the sample
# mean to form the 95% confidence interval.
#
# Tolerance: require that the relative 95% half‐width of the confidence interval is below tol.
tol = 0.05  # 5% relative error tolerance
min_iter = 3  # minimum iterations to start checking for convergence
max_iter = 100  # safeguard to prevent endless loops

# Initialize the random seed for reproducibility.
random.seed(42)


def sample_group(
    population: pd.DataFrame,
    stake: int,
    group_size: int,
) -> pd.DataFrame:
    """Sample a group of participants ensuring one has the given stake.

    Args:
        population (pd.DataFrame): The population of registered SPOs.
        stake (int): The stake value to include in the group.
        group_size (int): The number of participants in the group.

    Returns:
        pd.DataFrame: A DataFrame containing the group of participants.
    """
    # Sample a group of participants with the chosen stake value
    group = population[population["stake"] == stake].sample(1, replace=False)
    # Add to that group the remaining participants
    group = pd.concat(
        [group, population[population.index != group.index[0]].sample(group_size - 1)]
    )
    return group


def simulate_config(args):
    """Simulate the committee selection process for a given configuration.
    Args:
        args (tuple): A tuple containing the
                      given stake value, group size, and committee size.
    Returns:
        tuple: A tuple containing the stake value, group size,
               committee size, and the simulation results
               (mean, confidence intervals).
    """
    # Unpack arguments for this configuration.
    stake, group_size, committee_size = args

    # Dictionary to store simulation results for each stake value.
    sim_results = {s: [] for s in stake_values}
    iter_count = 0

    while True:
        iter_count += 1

        # Sample a group with the chosen stake value.
        group = sample_group(population, stake, group_size)

        # Sample a committee based on stake weight.
        committee = group.sample(committee_size, weights="stake_percent", replace=True)
        committee["seat_count"] = committee["id"].map(committee["id"].value_counts())
        aggregated = committee.groupby("stake")["seat_count"].sum()

        # Record the seat counts for every stake.
        for s in stake_values:
            sim_results[s].append(aggregated.get(s, 0))

        if iter_count >= min_iter:
            all_within_tol = True
            for s in stake_values:
                data = np.array(sim_results[s])
                mean_val = data.mean()
                sd_val = data.std(ddof=1)  # sample standard deviation
                half_width = (
                    stats.t.ppf(0.975, df=iter_count - 1) * sd_val / np.sqrt(iter_count)
                )
                if mean_val != 0:
                    if (half_width / mean_val) > tol:
                        all_within_tol = False
                        break
                else:
                    if half_width > tol:
                        all_within_tol = False
                        break

            if all_within_tol or iter_count >= max_iter:
                break

    # Compute final statistics for this configuration.
    mean_series = pd.Series({s: np.mean(sim_results[s]) for s in stake_values})
    ci_lower_series = pd.Series(
        {
            s: np.mean(sim_results[s])
            - stats.t.ppf(0.975, df=len(sim_results[s]) - 1)
            * np.std(sim_results[s], ddof=1)
            / np.sqrt(len(sim_results[s]))
            for s in stake_values
        }
    )
    ci_upper_series = pd.Series(
        {
            s: np.mean(sim_results[s])
            + stats.t.ppf(0.975, df=len(sim_results[s]) - 1)
            * np.std(sim_results[s], ddof=1)
            / np.sqrt(len(sim_results[s]))
            for s in stake_values
        }
    )

    return (
        stake,
        group_size,
        committee_size,
        (mean_series, ci_lower_series, ci_upper_series),
    )


# %%
if __name__ == "__main__":

    # Create the set of configurations (group_size, committee_size).
    configs = [
        (s, g, c)
        for s in stake_values
        for g in range(100, 501, 100)
        for c in range(100, 501, 100)
    ]

    # Start the timer to measure the execution time.
    start_time = time.time()
    print(f"Starting simulation with {len(configs)} configurations...")
    print(f"Number of configurations: {len(configs)}")
    print(f"Number of CPU cores: {cpu_count()}")
    print(f"CPU cores available: {cpu_count()}")
    print(f"Population size: {population_size}")
    print(f"Stake values: {stake_values}")
    print("-" * 50)
    # Print the configurations to be simulated.
    print("Configurations to be simulated:")
    for config in configs:
        print(f"Group Size: {config[0]}, Committee Size: {config[1]}")
    print("-" * 50)
    # Print the start time.
    print(
        f"Start time: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(start_time))}"
    )
    print("-" * 50)

    # Use multiprocessing to speed up the simulation process.
    # The Pool class allows you to create a pool of worker processes.
    # Each worker will execute the simulate_config function with a different configuration.
    # The cpu_count() function returns the number of CPU cores available on the machine.
    # Use all available CPU cores for parallel processing.
    with Pool(cpu_count()) as pool:
        results = pool.map(simulate_config, configs)

    print("-" * 50)
    print("Simulation completed.")
    # Print the end time.
    print(
        f"End time: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(time.time()))}"
    )
    # Print the total execution time.
    print(f"Total execution time: {time.time() - start_time:.2f} seconds")

    # Print and save the results as a DataFrame via converting the results
    # first to a dictionary for easier DataFrame creation.
    results_dict = {}
    for s, g, c, stats_tuple in results:
        mean_series, ci_lower_series, ci_upper_series = stats_tuple
        print(f"Stake: {s}, Group Size: {g}, Committee Size: {c}")
        print("Mean Seat Counts:\n", mean_series)
        print("CI Lower Bounds:\n", ci_lower_series)
        print("CI Upper Bounds:\n", ci_upper_series)
        print("-" * 50)
        results_dict[(s, g, c)] = {
            "mean_seats:": mean_series,
            "ci_lower": ci_lower_series,
            "ci_upper": ci_upper_series,
        }
    # Convert the dictionary to a DataFrame.
    results_df = pd.DataFrame.from_dict(results_dict, orient="index")

    # Save the results to two CSV files: one with an index and one without.
    # The index is the configuration (group_size, committee_size).
    results_df.to_csv(
        OUTPUT_DATA_FILE.replace(".csv", "_index.csv"),
        index=True,
    )
    print(f"Results saved to {OUTPUT_DATA_FILE.replace('.csv', '_index.csv')}")
    # Save the results to a CSV file without an index.
    # The index is the configuration (group_size, committee_size).
    results_df.to_csv(
        OUTPUT_DATA_FILE.replace(".csv", "_no_index.csv"),
        index=False,
    )
    print(f"Results saved to {OUTPUT_DATA_FILE.replace('.csv', '_no_index.csv')}")
    print("-" * 50)
