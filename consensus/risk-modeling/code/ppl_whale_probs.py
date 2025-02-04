# !/usr/bin/env python3
# coding: utf-8
"""
Model and estimate the probability that a whale (a stakeholder exceeding a 
certain stake threshold) emerges within a group of randomly selected 
stakeholders.

Approach:
- Data Loading: Load and preprocess the stake distribution data.
- Model Definition: Define a probabilistic model in Pyro that captures the 
    stake distribution and whale emergence condition.
- Inference: Use Pyro's inference algorithms to estimate the probability 
    across different group sizes and stake thresholds.
- Result Aggregation: Collect and save the results in the desired format.

"""
# %%
import logging
import time
from pathlib import Path
import pandas as pd
import torch
import pyro
import pyro.distributions as dist
import pyro.poutine as poutine
from pyro.infer.autoguide import AutoNormal
from pyro.infer import Importance, EmpiricalMarginal
import pyro.infer.mcmc as pyromcmc
from pyro.infer import MCMC, NUTS
from config_loader import load_config
from utils import measure_time

# %%


def load_data(file_path: str):
    """
    Load and preprocess the stake distribution data.

    Args:
        file_path (str): Path to the input data file.

    Returns:
        pd.DataFrame: DataFrame containing the stakeholders' data with columns
        'id' and 'stake_percent'.
    """
    df = pd.read_csv(file_path)
    df = df[["id", "stake"]].copy()
    df["stake"] = pd.to_numeric(df["stake"], errors="coerce")
    total_stake = df["stake"].sum()
    df["stake_percent"] = df["stake"] / total_stake  # Normalize to sum to 1
    return df


# %%
def whale_model(data, group_size, R_w):
    """
    Probabilistic model to estimate the probability of whale emergence
    for a specific R_w and group size.

    Args:
        data (pd.DataFrame): Stakeholder data with columns 'id' and 'stake_percent'.
        group_size (int): The size of the group being analyzed.
        R_w (float): The whale emergence rate parameter.

    Returns:
        None: The model conditions on the observed data and generates samples.
    """
    num_spos = len(data)
    stake_probs = torch.tensor(data["stake_percent"].values, dtype=torch.float)

    # Sample a group of SPO indices
    group_indices = pyro.sample(
        "group_indices",
        dist.Categorical(torch.ones(num_spos) / num_spos)
        .expand([group_size])
        .to_event(1),
    )

    # Get the stakes of the selected SPOs
    group_stakes = stake_probs[group_indices]

    # Normalize the stakes within the group
    group_stakes_normalized = group_stakes / group_stakes.sum()

    # Check if a whale exists
    max_stake_percent = group_stakes_normalized.max() * 100.0
    whale_exists = (max_stake_percent > R_w).float()

    # Observe the whale existence
    pyro.sample("obs", dist.Bernoulli(whale_exists), obs=whale_exists)


def estimate_whale_probability(data, group_size, R_w, num_samples=1000):
    """
    Estimate the probability of whale emergence using importance sampling.

    Args:
        data (pd.DataFrame): Observed data for conditioning the model.
        group_size (int): The size of the group being analyzed.
        R_w (float): The whale emergence rate parameter.
        num_samples (int): The number of importance samples to draw.

    Returns:
        float: The estimated probability of whale emergence.
    """
    conditioned_model = pyro.condition(whale_model, data=data)

    importance = Importance(conditioned_model, num_samples=num_samples)
    posterior = importance.run(data, group_size, R_w)

    marginal = EmpiricalMarginal(posterior, "obs")
    samples = marginal._get_samples_and_weights()[0]
    probability = samples.mean().item()
    return probability


def run_simulations(
    data,
    group_sizes,
    R_ws,
    num_samples=10000,
    calc_prob=estimate_whale_probability,
):
    """
    Run simulations across different group sizes and stake thresholds.

    Args:
        data (pd.DataFrame): Stakeholder data with columns 'id' and 'stake_percent'.
        group_sizes (list): List of group sizes to simulate.
        R_ws (list): List of whale probabilities to simulate.
        num_samples (int): Number of samples to generate in the simulation.
        calc_prob (function): Function to calculate the probability of whale emergence.

    Returns:
        pd.DataFrame: DataFrame containing the simulation results.
    """
    # Setting up simulations across different group sizes and stake thresholds.
    results = []
    for R_w in R_ws:
        for group_size in group_sizes:
            print(f"Simulating for R_w={R_w}, Group_Size={group_size} ...")
            probability = calc_prob(
                data,
                group_size,
                R_w,
                num_samples,
            )
            results.append(
                {
                    "R_w": R_w,
                    "Group_Size": group_size,
                    "Probability": probability,
                }
            )
    return pd.DataFrame(results)


# %%


@measure_time
def main(
    file_path: str,
    output_path: str,
    num_samples: int = 1000,
    group_sizes=range(10, 51, 5),
    R_ws=[33, 43, 53, 63, 73, 83],
):
    """
    Run the simulation and save results to a wide-format CSV file.

    Args:
        file_path (str): Path to the input data file.
        output_path (str): Path to save the simulation results.
        num_samples (int, optional): Number of samples to generate in the
            simulation. Defaults to 1000.
        group_sizes (range, optional): Range of group sizes to simulate.
            Defaults to range(10, 51, 5).
        R_ws (list, optional): List of whale probabilities to simulate.
            Defaults to [33, 43, 53, 63, 73, 83].

    Returns:
        None
    """
    # We start by loading the stake data and normalizing it.
    data = load_data(file_path)

    # Print data information
    print(data.head())
    print(data.info())
    print(data.describe())

    # Multiprocessing can be used to parallelize simulations for faster results.
    # However, Pyro's parallelization capabilities can also be leveraged for this purpose.
    #
    # # Prepare simulation arguments
    # simulation_args = list(product(R_ws, group_sizes, [num_trials], [data]))

    # Run simulations
    results_df = run_simulations(data, group_sizes, R_ws, num_samples)

    # Pivot results to wide format
    wide_format = results_df.pivot(
        index="R_w", columns="Group_Size", values="Probability"
    )
    wide_format.columns = wide_format.columns.astype(str)
    wide_format.reset_index(inplace=True)

    # Save to CSV
    wide_format.to_csv(output_path, index=False)
    print(f"Simulation complete. Results saved to {output_path}")


# %%
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

    # Run simulation
    main(
        str(FILE_PATH),
        str(OUTP_PATH),
        NUM_TRIALS,
        GROUP_SIZES,
        R_WS,
    )

# %% [markdown]
# ## Understanding the Transition
#
# **From Monte Carlo to Probabilistic Programming:
#
# - Monte Carlo Simulation: Repeated random sampling to estimate probabilities.
# - Probabilistic Programming (Pyro): Defines a generative model and uses
#   inference algorithms to estimate probabilities, capturing uncertainty
#   more formally.
#
# By using a PPL like Pyro, we're not just simulating outcomes but modeling
# the underlying probability distributions, allowing for more powerful
# inference and insights.
#
