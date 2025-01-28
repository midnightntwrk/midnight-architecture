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

The main function of the script, named main, takes several arguments, including
Group Sizes: [10, 30, 50, 70, 90, 110, 130, 150, 170, 190, 200]
R_ws: [1, 6, 11, 16, 21, 26, 31, 33, 36, 40, 51, 66, 75, 80, 90]

The main function then runs simulations in parallel using the Pool class and
saves the results to a wide-format CSV file. The script also includes two
functions, sim_whale_prob_basic and sim_whale_prob_vectorized, which define
probabilistic models to estimate the probability of whale emergence for
different R_w values and group sizes.

The sim_whale_prob_basic function uses a basic Monte Carlo simulation approach
to estimate the probability of whale emergence, while the sim_whale_prob_vectorized
function uses a vectorized approach with PyTorch to improve performance.

Function: sim_whale_prob_basic

2025-01-27 18:10:52,307 - INFO - Starting simulation...
2025-01-27 18:13:40,335 - INFO - Simulation complete.
2025-01-27 18:13:40,386 - INFO - Time taken: 168.10 seconds

Function: sim_whale_prob_vectorized

2025-01-27 18:13:40,407 - INFO - Starting simulation...
2025-01-27 18:15:07,146 - INFO - Simulation complete.
2025-01-27 18:15:07,255 - INFO - Time taken: 86.87 seconds

Speedup: 1.94x

Vectorized simulation is faster than the basic simulation by a factor of 1.94x.
This speedup is achieved by leveraging PyTorch's vectorized approach processes
simulations in parallel using optimized tensor operations, resulting in
significantly faster execution times compared to the basic simulation method.
This is even more pronounced when running simulations with larger datasets or
more complex models, as the vectorized approach can take advantage of GPUs.

"""

import logging
import time
import json
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from pathlib import Path
from itertools import product
from multiprocessing import Pool
from config_loader import load_config

import pyro
import pyro.poutine as poutine
import torch
import pyro.distributions as dist


def load_data(file_path: str):
    """
    Load and normalize SPO data from a CSV file.
    """
    df = pd.read_csv(file_path)

    df = df[["id", "stake"]].copy()
    df["stake"] = pd.to_numeric(df["stake"], errors="coerce")
    total_stake = df["stake"].sum()
    df["stake_percent"] = (df["stake"] / total_stake) * 100
    return df


def sim_whale_prob_basic(args):
    """
    Probabilistic model to estimate the probability of whale emergence.
    for a specific R_w and group size.

    Args:
        args (tuple): Tuple containing R_w, group_size, num_trials, and data.

    Returns:
        dict: Dictionary containing R_w, group_size, and probability.
    """
    R_w, group_size, num_trials, data = args

    logging.info(f"Running simulation for R_w={R_w}, Group_Size={group_size} ...")

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


def sim_whale_prob_vectorized(args):
    """
    Probabilistic model to estimate the probability of whale emergence
    for a specific R_w and group size using vectorization with PyTorch.

    Args:
        args (tuple): Tuple containing R_w (threshold percentage),
                      group_size (number of SPOs in a group),
                      num_trials (number of simulations),
                      and data (DataFrame with SPO stakes).

    Returns:
        dict: Dictionary containing R_w, group_size, and estimated probability.
    """
    import torch

    R_w, group_size, num_trials, data = args

    logging.info(f"Running simulation for R_w={R_w}, Group_Size={group_size} ...")

    # Convert stakes to a PyTorch tensor
    stakes = torch.tensor(data["stake"].values, dtype=torch.float)

    num_SPOs = stakes.size(0)

    # Generate random permutations of SPO indices for each trial
    rand_vals = torch.rand(num_trials, num_SPOs)
    perm_indices = rand_vals.argsort(dim=1)
    group_indices = perm_indices[:, :group_size]

    # Select stakes for each group in all trials
    selected_stakes = stakes[group_indices]  # Shape: (num_trials, group_size)

    # Calculate total stake for each group
    total_group_stakes = selected_stakes.sum(
        dim=1, keepdim=True
    )  # Shape: (num_trials, 1)

    # Calculate stake percentages within each group
    stake_percentages = (
        selected_stakes / total_group_stakes
    ) * 100  # Shape: (num_trials, group_size)

    # Determine if any SPO in each group exceeds the threshold R_w
    max_stake_percentages, _ = stake_percentages.max(dim=1)  # Shape: (num_trials,)
    whales = max_stake_percentages > R_w

    # Estimate probability
    probability = whales.float().mean().item()

    logging.info(f"Simulation complete for R_w={R_w}, Group_Size={group_size}.")

    return {"R_w": R_w, "Group_Size": group_size, "Probability": probability}


def print_data_info(label: str, data: pd.DataFrame, sample_size: int = 5):
    """
    Print information about the data.

    Args:
        label (str): Label for the data.
        data (pd.DataFrame): Data to describe.
        sample_size (int, optional): Number of samples to display. Defaults to 5.

    Returns:
        None
    """
    print("_" * 50)
    print(f"{label}")
    print("Data Information:")
    print(data.info())
    print("Data Description:")
    print(data.describe())
    print("Data Sample:")
    size = min(sample_size, len(data))
    print(data.sample(size))


def main(
    sim_whale_prob,
    file_path: str,
    output_path: str,
    num_trials: int = 1000,
    group_sizes=range(10, 51, 5),
    R_ws=[33, 43, 53, 63, 73, 83],
):
    """
    Run the simulation and save results to a wide-format CSV file.

    Args:
        file_path (str): Path to the input data file.
        output_path (str): Path to save the simulation results.
        num_trials (int, optional): Number of simulation trials.
            Defaults to 1000.
        group_sizes (range, optional): Range of group sizes to simulate.
            Defaults to range(10, 51, 5).
        R_ws (list, optional): List of whale probabilities to simulate.
            Defaults to [33, 43, 53, 63, 73, 83].

    Returns:
        None
    """
    logging.info("Starting program ...")

    # Load data
    data = load_data(file_path)

    # Print data information
    print_data_info("Input Data:", data)

    # Prepare simulation arguments
    simulation_args = list(product(R_ws, group_sizes, [num_trials], [data]))

    # Run simulations in parallel
    logging.info("Starting simulation...")
    with Pool() as pool:
        results = pool.map(sim_whale_prob, simulation_args)

    logging.info("Simulation complete.")

    # Convert results to a DataFrame
    results_df = pd.DataFrame(results)

    # Pivot results to wide format
    wide_format = results_df.pivot(
        index="R_w", columns="Group_Size", values="Probability"
    )
    wide_format.columns = list(map(str, map(int, wide_format.columns)))
    wide_format.reset_index(inplace=True)
    print_data_info("Result Data", wide_format)

    # Round floats to 5 significant digits
    wide_format = wide_format.round(5)

    # Save to CSV
    wide_format.to_csv(output_path, index=False)
    logging.info(f"Program complete. Results saved to {output_path}")


if __name__ == "__main__":

    # Set up logging to print to stdout
    logging.basicConfig(
        level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
    )

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

    # start time
    start_time = time.time()

    # Choose the simulation function to use
    function = sim_whale_prob_vectorized

    # Run simulation
    main(
        function,
        str(FILE_PATH),
        str(OUTP_PATH).replace(".csv", f"_{function.__name__}.csv"),
        NUM_TRIALS,
        GROUP_SIZES,
        R_WS,
    )

    stop_time = time.time()
    logging.info(f"Time taken: {stop_time - start_time:.2f} seconds")
