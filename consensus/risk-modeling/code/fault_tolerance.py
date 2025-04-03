#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Module: fault_tolerance.py

Created on 2025-04-02 by Rob Jones <robert.jones@shielded.io>

This script simulates the process of selecting a committee
and evaluating its BFT finality risk based on the stake distribution
of the participants.

"""
# %%
# import random
# import pymc as pm
# import arviz as az
# from scipy.stats import gamma
import matplotlib.pyplot as plt
import seaborn as sns
from data import load_data
from participation_lib import get_stake_distribution
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


def assign_commitee(
    group: pd.DataFrame,
    committee_size: int = 300,
    plot_it: bool = False,
    figsize: tuple[int, int] = (16, 8),
) -> dict[pd.DataFrame, pd.Series, float, float, int]:
    """
    Assumes participants in a given group of size group_size are assigned to
    a committee using random selection with replacement based on their stake
    weight. The committee has a fixed size equal to the group_size. As such,
    partipants with larger stake-weight will occupy multiple committee seats.

    Args:
    - group: DataFrame containing the group of participants, assumed size n.
    - committee_size: Size of the committee (k).
    - plot_it: Boolean flag to plot the committee seat distribution.
    - figsize: Size of the figure.

    Returns:
        seat_counts: pd.Series containing the committee seat average.

    """
    group_size = group.shape[0]  # size n

    # Initialize an array to store the number of
    # committee seats per participant as first-order statistics
    seat_counts = pd.Series(
        np.zeros(group_size, dtype="int64"),
        index=group.index,
        dtype="int64",
        name="seat counts",
    )
    # Select a committee based on the stake weight of each
    # participant stake holder.
    #
    committee = group.sample(
        n=committee_size,
        weights="stake_weight",
        replace=True,
    )

    # Count the number of times each participant is selected
    # for a committee seat
    participant_counts = committee.index.value_counts()

    # Reindex participant_counts to match seat_counts index and
    # fill missing values with 0
    participant_counts = participant_counts.reindex(
        seat_counts.index,
        fill_value=0,
    )

    # Add the counts to the seat_counts array
    seat_counts += participant_counts

    # Get the index when the seat_counts value is first zero
    reversed_seat_count = seat_counts.loc[::-1]
    # which sorts the sum_counts in descending order to determine
    # the index when seat count first transitions from zero to non-zero
    first_zero_index = reversed_seat_count[reversed_seat_count > 0].index[0]

    # Let's plot both group and sum_counts with two y-axes,
    # one for each
    if plot_it:
        fig, ax1 = plt.subplots(figsize=figsize)
        fig.canvas.manager.set_window_title("Committee Participation per Stake Weight")
        ax2 = ax1.twinx()
        x = np.arange(len(seat_counts))
        y = seat_counts.values
        # Plot only the participants with non-zero seat counts
        mask = y > 0
        x = x[mask]
        y = y[mask]

        sns.scatterplot(
            x=x,
            y=y,
            markers="o",
            alpha=0.5,
            color="blue",
            label="Committee Seat (average)",
            ax=ax1,
        )
        ax1.vlines(
            x=x,
            ymin=0,
            ymax=y,
            colors="blue",
            linestyles="-",
            alpha=0.5,
        )
        sns.lineplot(
            x=np.arange(len(group.stake_weight)),
            y=group.stake_weight.values,
            color="red",
            label="Participant Group Stake Weight",
            ax=ax2,
        )
        ax1.set_ylabel("Committee Seats (average)")
        ax2.set_ylabel("Stake Weight")
        ax1.set_xlabel("Participant Index")
        ax1.legend(loc="upper center")
        ax2.legend(loc="upper right")
        plt.title(
            f"Committee Participation per Stake Weight\n"
            f"Committee Size k = {committee_size}\n"
            f"Participation Group Size n = {group_size}",
            fontsize="medium",
        )
        plt.axhline(y=0, color="gray", linestyle="--", alpha=0.6)
        # Draw vertical line where the committee seat count first goes to zero
        plt.axvline(x=first_zero_index, color="green", linestyle="--")
        # Print the value of this first_zero_index along the center of the
        # vertical line
        plt.text(
            first_zero_index,
            ax2.get_ylim()[1] / 2.0,
            f"First Zero Index = {first_zero_index}",
            rotation=0,
            verticalalignment="center",
            horizontalalignment="center",
            color="green",
            backgroundcolor="white",
        )
        plt.show()

    return seat_counts


def faults_tolerated(committee_seats: pd.Series) -> int:
    """
    Compute the number of faults tolerated by the committee

    Args:
        committee_seats (pd.Series): Series of committee seats.

    Returns:
        int: The number of faults tolerated by the committee.
    """
    voting_strength = committee_seats.sort_values(ascending=False).divide(
        committee_seats.sum()
    )
    faults = np.where(np.cumsum(voting_strength) > 1 / 3)[0][0]
    return faults


def calculate_fault_tolerance_probability(
    participant_group: pd.DataFrame,
    committee_size: int,
    fault_tolerance: int,
    num_iters: int = 1000,
) -> float:
    """
    Calculate the probability of tolerating a given number of faults
    in a committee of a given size.
    The function uses Monte Carlo simulation to estimate the probability.
    Args:
        participant_group (pd.DataFrame): DataFrame of participants.
        committee_size (int): Size of the committee.
        fault_tolerance (int): Number of faults to tolerate.
        num_iters (int): Number of iterations for the simulation.
    Returns:
        float: Estimated probability of tolerating the given number of faults.
    """
    # Calculate success rate through Monte Carlo simulation
    probability = np.mean(
        [
            (
                1
                if faults_tolerated(
                    assign_commitee(
                        participant_group,
                        committee_size,
                    )
                )
                >= fault_tolerance
                else 0
            )
            for _ in range(num_iters)
        ]
    )
    return probability


def plot_fault_tolerance_heatmap(
    group_stakes,
    committee_sizes=np.arange(100, 800, 100),
    fault_tolerance=np.arange(1, 11, 1),
    plot_it=True,
    figsize=(12, 6),
):
    """
    Plot a heatmap of the probability of fault tolerance as a function of
    committee size and fault appetite.

    Args:
        group_stakes (pd.DataFrame): DataFrame containing stake distribution.
        committee_sizes (np.array): Array of committee sizes to test.
        fault_tolerance (np.array): Array of fault tolerance levels to test.
        plot_it (bool): Whether to display the plot.
        figsize (tuple): Size of the figure.

    Returns:
        np.ndarray: 2D array of probabilities.
    """
    probabilities = np.zeros((len(committee_sizes), len(fault_tolerance)))

    for i, k in enumerate(committee_sizes):
        for j, f in enumerate(fault_tolerance):
            probabilities[i, j] = calculate_fault_tolerance_probability(
                group_stakes,
                committee_size=k,
                fault_tolerance=f,
            )

    if plot_it:
        plt.figure(figsize=figsize)
        sns.heatmap(
            probabilities,
            annot=True,
            fmt=".2f",
            cmap="viridis",
            xticklabels=fault_tolerance,
            yticklabels=committee_sizes,
        )
        plt.xlabel("Fault Tolerance")
        plt.ylabel("Committee Size")
        plt.title("Fault Tolerance Probability Heatmap")
        plt.show()

    return probabilities


# %%
# Load the Data: The population of registered SPOs

population = load_population("../data/pooltool-cleaned.csv")

print(population.info())

# %%
population.describe()

# %%
# Let's now sample a group of participants from the population
# and calculate the stake weight for each participant.

group_size = 600

group_stakes = get_stake_distribution(
    population,
    group_size=group_size,
    num_iter=1,
    plot_it=True,
)
print(group_stakes)
group_stakes.describe()

# %%
# Let's test the code with an example:

committee_size = 100

committee_seats = assign_commitee(
    group_stakes,
    committee_size=committee_size,
    plot_it=True,
)
print(
    "Number of distinct voters =",
    len(committee_seats[committee_seats > 0]),
)


# %%
# Example usage
g = group_stakes  # group of participants
k = 100  # committee size
f = 7  # fault appetite
p = calculate_fault_tolerance_probability(g, k, f)
print(f"Probability of tolerating {f} faults in a committee of size {k} = {p:.2}")
# %%

# %%
plot_fault_tolerance_heatmap(
    group_stakes,
    committee_sizes=np.arange(50, 700, 50),
    fault_tolerance=np.arange(1, 17, 1),
    plot_it=True,
    figsize=(12, 6),
)
# %%
