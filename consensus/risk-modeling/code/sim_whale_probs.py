#!/usr/bin/env python
# coding: utf-8
"""
The code provided is part of a Python script designed to run simulations in
parallel using the multiprocessing library. The script imports the Pool class
from the multiprocessing module, which allows for the creation of a pool of
worker processes to execute tasks concurrently.

The main function is the core of the script, responsible for running the
simulation and saving the results to a CSV file. It takes several parameters:
file_path (the path to the input data file), output_path (the path where the
results will be saved), num_trials (the number of simulation trials to run,
defaulting to 1000), group_sizes (a range of group sizes to simulate,
defaulting to values from 10 to 50 in steps of 5), and R_ws (a list of whale
probabilities to simulate).

The function begins by loading the input data using a load_data function (not
shown in the provided code). It then prepares the arguments for the simulation
by creating a list of tuples, where each tuple contains a combination of R_ws,
group_sizes, num_trials, and the loaded data. This is done using the product
function from the itertools module, which generates the Cartesian product of
the input iterables.

Next, the script creates a pool of worker processes using the Pool class. The
with Pool() as pool statement ensures that the pool is properly managed and
closed after use. The pool.map method is used to distribute the simulation
tasks across the worker processes. Each worker process runs the
simulate_whale_probability function (not shown in the provided code) with the
corresponding arguments from the simulation_args list.

Once all simulations are complete, the results are collected into a list and
converted into a pandas DataFrame. The DataFrame is then pivoted to a wide
format, where the index is R_w, the columns are Group_Size, and the values are
the simulated probabilities. The column names are converted to strings, and
the index is reset to ensure a clean DataFrame.

Finally, the wide-format DataFrame is saved to a CSV file at the specified
output_path, and a message is printed to indicate that the simulation is
complete and the results have been saved. This script efficiently leverages
parallel processing to handle potentially large and computationally intensive
simulations.
"""

import logging
import json
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from pathlib import Path
from itertools import product
from multiprocessing import Pool
from config_loader import load_config


def load_data(file_path: str):
    """
    Load and normalize SPO data from a CSV file.
    """
    df = pd.read_csv(file_path)

    # # Remove any leading or trailing spaces in the column names
    # df.columns = df.columns.str.strip()

    # # Remove any leading or trailing spaces in the values
    # df = df.applymap(lambda x: x.strip() if isinstance(x, str) else x)

    df = df[["id", "stake"]].copy()
    df["stake"] = pd.to_numeric(df["stake"], errors="coerce")
    total_stake = df["stake"].sum()
    df["stake_percent"] = (df["stake"] / total_stake) * 100
    return df


def simulate_whale_probability(args):
    """
    Simulate whale emergence probability for a specific R_w and group size.
    """
    R_w, group_size, num_trials, data = args

    logging.info(f"Running simulation for R_w={R_w}, Group_Size={group_size}...")

    whale_count = 0

    for _ in range(num_trials):
        # Randomly select a group of SPOs
        group_indices = np.random.choice(data.index, size=group_size, replace=False)
        group = data.loc[group_indices].copy()

        # Calculate the group's total stake
        total_group_stake = group["stake"].sum()

        # Check if any SPO exceeds the threshold
        max_stake_percent = (group["stake"] / total_group_stake) * 100
        if max_stake_percent.max() > R_w:
            whale_count += 1

    # Calculate probability
    probability = whale_count / num_trials

    logging.info(f"Simulation complete for R_w={R_w}, Group_Size={group_size}.")

    return {"R_w": R_w, "Group_Size": group_size, "Probability": probability}


def main(
    file_path: str,
    output_path: str,
    num_trials: int = 10000,
    group_sizes=range(10, 51, 5),
    R_ws=[33, 43, 53, 63, 73, 83],
):
    """
    Run the simulation and save results to a wide-format CSV file.

    Args:
        file_path (str): Path to the input data file.
        output_path (str): Path to save the simulation results.
        num_trials (int, optional): Number of simulation trials.
            Defaults to 10000.
        group_sizes (range, optional): Range of group sizes to simulate.
            Defaults to range(10, 51, 5).
        R_ws (list, optional): List of whale probabilities to simulate.
            Defaults to [33, 43, 53, 63, 73, 83].
    """
    # Load data
    data = load_data(file_path)

    # Print data information
    print(data.head())
    print(data.info())
    print(data.describe())

    # Prepare simulation arguments
    simulation_args = list(product(R_ws, group_sizes, [num_trials], [data]))

    # Run simulations in parallel
    logging.info("Starting simulation...")
    with Pool() as pool:
        results = pool.map(simulate_whale_probability, simulation_args)

    logging.info("Simulation complete.")

    # Convert results to a DataFrame
    results_df = pd.DataFrame(results)

    print("Results:")
    print(results_df.head())
    print(results_df.info())
    print(results_df.describe())

    # Pivot results to wide format
    wide_format = results_df.pivot(
        index="R_w", columns="Group_Size", values="Probability"
    )
    wide_format.columns = list(map(str, map(int, wide_format.columns)))
    wide_format.reset_index(inplace=True)

    # Save to CSV
    wide_format.to_csv(output_path, index=False)
    logging.info(f"Simulation complete. Results saved to {output_path}")


if __name__ == "__main__":

    # Load configuration
    config = load_config("config.json")

    # Access parameters
    ROOT_PATH = config["root_path"]
    DATA_PATH = config["data_path"]
    FILE_NAME = config["file_name"]
    OUTP_NAME = config["outp_name"]
    FILE_PATH = config["file_path"]
    OUTP_PATH = config["outp_path"]
    NUM_TRIALS = config["num_trials"]
    GROUP_SIZES = config["group_sizes"]
    R_WS = config["r_ws"]

    # Now you can use these parameters in your script
    print("Group Sizes:", GROUP_SIZES)
    print("R_ws:", R_WS)

    # Run simulation
    main(
        str(FILE_PATH),
        str(OUTP_PATH),
        NUM_TRIALS,
        GROUP_SIZES,
        R_WS,
    )

    # Print completion message
    logging.info("Program exiting.")
