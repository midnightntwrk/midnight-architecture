#!/usr/bin/env python
# coding: utf-8

"""
Module: participation_lib

This module performs risk modeling for participation distribution in a
consensus mechanism. It includes functions to load and normalize SPO data,
sample participants based on their stake, and perform Monte Carlo simulations
to analyze the committee seat selection process based on stake weight. The
module also demonstrates the uneven distribution of selections based on stake
weights and the finite committee.

Functions:
- sample_group: Uniformly sample from a population of participants without
    replacement.
- get_stake_distribution: Collect and plot the stake distribution for a sample
    group.
- assign_commitee: Assign participants to a committee using random selection
    based on stake weight.
- plot_group_to_committee_index: Scatter plot of group participant index vs.
    seat selection index.
- plot_committee_selection_counts: Plot the committee selection counts for
    varying group sizes.
- plot_selection_count_vs_stake: Plot the seat assignment count vs. stake for
    a committee.

Author: Rob Jones <robert.jones@shield.io>
Date: 12 Mar 2025

"""

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
from data import load_data


def sample_group(
    population: pd.DataFrame,
    group_size: int = 300,
) -> pd.DataFrame:
    """
    Uniformly sample from a population of participlants without replacement.
    Only samples groups with nonzero stake is returned.

    Args:
    - population: DataFrame containing the population.
    - group_size: Number of samples to draw.

    Returns:
    - sample: DataFrame of sample of size `group_size` (n).

    """
    sample = population[population.stake > 0].sample(
        group_size,
        replace=False,
    )
    sample["stake_weight"] = sample.stake / sample.stake.sum()
    # Sort by stake weight in descending order
    sample = sample.sort_values("stake_weight", ascending=False)
    return sample


def get_stake_distribution(
    population: pd.DataFrame,
    group_size: int = 300,
    num_iter: int = 1,
    plot_it: bool = False,
    figsize: tuple[int, int] = (16, 8),
) -> pd.DataFrame:
    """
    Collect and plot the stake distribution for a sample group of participants.
    The stake distribution is calculated by summing the stakes of each participant
    in the sample group. The average stake is calculated if num_iter > 1.

    Args:
    - population: DataFrame containing the population.
    - group_size: Number of samples to draw.
    - num_iter: Number of iterations for Monte Carlo simulation.
    - plot_it: Boolean flag to plot the stake distribution.
    - figsize: Size of the figure.

    Returns:
    - stakes: DataFrame containing the stake and stake weight of each participant.

    """
    # Let's collect the sample participants.stake.values
    # for every participant in the given sample group size.
    # Average them if num_iter > 1.

    # Initialize an array to store the sum of stakes for each participant
    stakes = np.zeros(group_size)
    for n in range(num_iter):
        participants = sample_group(population, group_size)
        # Add the stakes of the current iteration to the stake_sums array
        stakes += participants.stake.values

    if num_iter > 1:
        # Calculate the average stakes
        avg_stakes = stakes / num_iter
        stakes = pd.DataFrame(avg_stakes.round(), columns=["stake"], dtype="int")
    else:
        stakes = pd.DataFrame(stakes, columns=["stake"])

    min_stake = stakes.stake.min()
    max_stake = stakes.stake.max()

    if plot_it:
        # Plot the stake for each participant number 1 to group_size
        plt.figure("Participant Stake Size", figsize=figsize)
        sns.lineplot(
            x=np.arange(len(stakes)),
            y=stakes.stake.values,
            linestyle="-.",
            alpha=1,
            color="r",  # Color for the average curve
            # linewidth=2,
            # markersize=4,
            label="Average Stake",
        )

        # Draw a horizontal line at maximum stake value
        plt.axhline(
            y=max_stake,
            color="b",
            linestyle="--",
            alpha=0.6,
            label=f"Max. Stake = {max_stake}",
        )

        # Draw a horizontal line at minimum stake value
        plt.axhline(
            y=min_stake,
            color="g",
            linestyle="--",
            alpha=0.6,
            label=f"Min. Stake = {min_stake}",
        )

        plt.legend()
        plt.title(f"Stake for each Participant (1 to {group_size})")
        plt.xlabel("Participant Number")
        plt.ylabel("Stake")
        plt.show()

    # Add the stake weight column to the DataFrame
    stakes["stake_weight"] = stakes.stake / stakes.stake.sum()

    return stakes


def plot_group_to_committee_index(
    seat_counts: pd.Series,
    figsize: tuple[int, int] = (6, 6),
):
    """
    A simple scatter plot of the two series indexes
    to see how they align.

    Args:
    - seat_counts: Series containing the committee seat counts
      indexed by participant index.
    - figsize: Size of the figure.

    """
    plt.figure("Group and Committee Selection", figsize=figsize)
    plt.scatter(
        np.arange(len(seat_counts)),
        seat_counts.index,
        marker=".",
        color="green",
    )
    plt.xlabel("Group Participant Index")
    plt.ylabel("Seat Selection Participant Index")
    plt.title("Seat Selection Index vs. Participant Index")
    plt.legend()
    plt.show()


# Plot the selection counts for each group size
def plot_committee_selection_counts(
    committee_size: int,
    selection_counts: pd.DataFrame,
    first_zero_indices: np.ndarray,
    log_scale: bool = True,
    figsize: tuple[int, int] = (16, 8),
):
    """
    Plot the committee selection counts for varying group sizes.

    Args:
    - committee_size: Size of the committee (k).
    - selection_counts: DataFrame containing the committee seats on average.
    - first_zero_indices: Array containing the first zero index for each group size.
    - log_scale: Boolean flag to set the y-axis to log scale.
    - figsize: Size of the figure.

    """
    plt.figure("Committee Participation per Group Size", figsize=figsize)
    sns.lineplot(
        data=selection_counts,
        dashes=False,
        linewidth=1,
        alpha=0.9,
    )
    for i, cutoff in enumerate(first_zero_indices):
        plt.axvline(
            x=cutoff,
            color=plt.gca().lines[i].get_color(),
            linestyle="--",
            linewidth=1,
            alpha=0.6,
        )
        # Print the value of this cutoff value
        # along the center of the vertical line
        plt.text(
            cutoff,
            plt.gca().get_ylim()[1] / 2.0,
            f"{int(cutoff)}",
            rotation=0,
            verticalalignment="center",
            horizontalalignment="center",
            color=plt.gca().lines[i].get_color(),
            backgroundcolor="white",
            fontsize="medium",
        )
        if log_scale:
            plt.yscale("log")

    plt.legend(fontsize="small")
    plt.xlabel("Participant Index", fontsize="small")
    plt.ylabel("Committee Seat (average)", fontsize="small")
    plt.title(
        f"Committee Participation from Varying Group Sizes\n"
        f"Committee Size k = {committee_size}",
        fontsize="medium",
    )
    plt.show()


def plot_selection_count_vs_stake(
    group_stakes: pd.DataFrame,
    committee_seats: pd.DataFrame,
    first_zero_index: int,
    plot_cutoff_line: bool = False,
    figsize: tuple[int, int] = (16, 8),
):
    """
    Plot the seat assignment count vs. stake for a committee
    of a given size.

    Args:
    - group_stakes: DataFrame containing the stake weight of each participant.
    - committee_seats: DataFrame containing the committee members.
    - first_zero_index: Index where the seat count first goes to zero.
    - plot_cutoff_line: Boolean flag to plot the cutoff line.
    - figsize: Size of the figure.

    """
    committee_size = committee_seats.shape[0]
    group_size = group_stakes.shape[0]
    cutoff = group_stakes.loc[first_zero_index, "stake_weight"]

    # Count the number of seats each participant has in the committee
    participant_counts = committee_seats.index.value_counts()
    assert participant_counts.index.is_unique

    # Align committee_members with participant_counts
    committee_members = group_stakes.loc[participant_counts.index].sort_values(
        by="stake_weight", ascending=False
    )

    x = committee_members.stake_weight.values
    y = participant_counts.values
    # Plot only the participants with non-zero seat counts
    mask = y > 0
    x = x[mask]
    y = y[mask]

    # Plot selection seat count vs. stake
    plt.figure("Committee Participation per Stake Weight", figsize=figsize)
    sns.scatterplot(
        x=x,
        y=y,
        marker="o",
        alpha=0.8,
    )
    sns.lineplot(
        x=x,
        y=y,
        linestyle="-",
        alpha=0.8,
    )
    plt.grid(axis="y", which="major", linestyle="--", linewidth=0.5, alpha=0.7)
    plt.gca().invert_xaxis()
    plt.xlabel("Participant Stake Weight")
    plt.ylabel("Participant Seat Counts")
    plt.title(
        "Committee Participation per Stake Weight\n"
        f"Committee Size k = {committee_size}\n"
        f"Participation Group Size n = {group_size}",
        fontsize="medium",
    )
    if plot_cutoff_line:
        plt.axvline(
            x=cutoff,
            color="gray",
            linestyle="--",
            linewidth=1,
            alpha=0.6,
        )
        # Print the value of this cutoff value along the center of the vertical line
        plt.text(
            cutoff,
            plt.gca().get_ylim()[1] / 2.0,
            f"Cutoff stake weight = {int(cutoff)}",
            rotation=0,
            verticalalignment="center",
            horizontalalignment="right",
            color="black",
            backgroundcolor="white",
            fontsize="medium",
        )
    plt.show()


def plot_committee_selection_seat_cutoff(
    committee_sizes: list,
    committee_seats_df: pd.DataFrame,
    first_zero_indices: np.ndarray,
    log_scale: bool = False,
):
    """
    Plot the committee selection counts for each group size.

    Args:
    - committee_sizes: list of committee sizes
    - committee_seats_df: DataFrame of committee selection counts
    - first_zero_indices: array of first zero indices
    - log_scale: whether to use log scale for the plot

    Returns:
    - None

    """
    # Loop over the committee sizes
    for i, committee_size in enumerate(
        committee_seats_df.columns.get_level_values(0).unique()
    ):
        plot_committee_selection_counts(
            committee_size=committee_sizes[i],
            selection_counts=committee_seats_df[committee_size],
            first_zero_indices=first_zero_indices[i],
            log_scale=log_scale,
        )


def plot_participation(
    sim_results_df: pd.DataFrame,
    group_labels: list,
    committee_labels: list,
    num_iter: int,
):
    """
    Plot the percentage of group participants excluded from a committee
    of a given size vs. different group sizes.

    Args:
    - sim_results_df (pd.DataFrame): The simulation results DataFrame.
    - committee_labels (list): The labels for the committee sizes.
    - group_labels (list): The labels for the group sizes.
    - num_iter (int): The number of iterations for the simulation.

    Returns:
        None
    """
    # Extract the numerical value of group and committee sizes from the labels
    group_sizes = [int(c.split("=")[1].strip()) for c in group_labels]
    committee_sizes = [int(c.split("=")[1].strip()) for c in committee_labels]

    fig, (ax2, ax1) = plt.subplots(1, 2, figsize=(16, 8))
    fig.canvas.manager.set_window_title("Committee and Group Participation")
    sns.set(style="whitegrid")

    for group_label, group_size in zip(group_labels, group_sizes):

        # Extract the distinct voters data for the given group size
        committee_voters = sim_results_df.loc["Distinct Voters", group_label]

        # These are the mean committee seat counts and associated standard deviations
        mean_values = committee_voters.loc["mean"]
        std_dev_values = committee_voters.loc["sd"]

        # Calculate the percentage of participants not selected for committee seats
        not_selected_percentages = (1.0 - mean_values / group_size) * 100

        # Prepare data for plotting the percentage excluded on ax1
        # The risk_code `plot_data` appears to be a function or method call to plot some data. However,
        # without seeing the implementation of the `plot_data` function or method, it is not possible
        # to determine exactly what the risk_code is doing.
        # The risk_code `plot_data` appears to be a function or method call to plot some data. However,
        # without seeing the implementation of the `plot_data` function or method, it is not possible
        # to determine exactly what the risk_code is doing.
        plot_data = pd.DataFrame(
            {
                "Committee Sizes": committee_sizes,
                "Percentage of Participants Excluded": not_selected_percentages,
                "Std Dev": std_dev_values,
            }
        )

        # Plot the percentage excluded on ax1
        sns.lineplot(
            x="Committee Sizes",
            y="Percentage of Participants Excluded",
            data=plot_data,
            marker="o",
            label=group_size,
            ax=ax1,
        )

        # Prepare data for plotting the mean committee seat counts on ax2
        plot_data2 = pd.DataFrame(
            {
                "Committee Sizes": committee_sizes,
                "Distinct Number of Committee Members": mean_values.values,
            }
        )

        # Plot the mean committee seat counts on ax2
        sns.lineplot(
            x="Committee Sizes",
            y="Distinct Number of Committee Members",
            data=plot_data2,
            marker="o",
            label=group_size,
            ax=ax2,
        )

    ax1.set_ylabel("Percentage of Participants Excluded from Committee")
    ax1.set_xlabel("Committee Size, k")
    ax1.set_title("Percentage of Group Not Selected for Committee Seats")
    ax1.legend(title="Group Size, n", loc="upper right")
    ax1.grid(True)

    ax2.set_ylabel("Distinct Number of Committee Members")
    ax2.set_xlabel("Committee Size, k")
    ax2.set_title(
        f"Distinct Number of Committee Members Averaged over {num_iter} Epochs"
    )
    ax2.legend(title="Group Size, n", loc="upper left")
    ax2.grid(True)


# %%
def plot_participation_plus(
    sim_results_df: pd.DataFrame,
    group_labels: list,
    committee_labels: list,
    num_iter: int,
):
    """
    Plot the distinct number of committee members and the ratio of distinct members
    to committee size in the first two plots, and then the percentage of group participants
    excluded from a committee in the last plot. The ratio plot highlights Byzantine fault
    tolerance thresholds at 1/3 and 2/3.

    Args:
    - sim_results_df (pd.DataFrame): The simulation results DataFrame.
    - committee_labels (list): The labels for the committee sizes.
    - group_labels (list): The labels for the group sizes.
    - num_iter (int): The number of iterations for the simulation.

    Returns:
        None
    """
    # Extract numerical values from labels.
    group_sizes = [int(c.split("=")[1].strip()) for c in group_labels]
    committee_sizes = [int(c.split("=")[1].strip()) for c in committee_labels]

    # Create a 1x3 grid of subplots.
    # New order: left: Distinct Committee Members, middle: Distinct/Committee Ratio,
    # right: Percentage of Participants Excluded.
    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(24, 8))
    fig.canvas.manager.set_window_title(
        "Committee and Group Participation (Byzantine Fault Tolerance)"
    )
    sns.set(style="whitegrid")

    for group_label, group_size in zip(group_labels, group_sizes):
        # Extract distinct voters data for the given group size.
        committee_voters = sim_results_df.loc["Distinct Voters", group_label]
        mean_values = committee_voters.loc["mean"]
        std_dev_values = committee_voters.loc["sd"]

        # Calculate the percentage of participants not selected for committee seats.
        not_selected_percentages = (1.0 - mean_values / group_size) * 100
        plot_data_excluded = pd.DataFrame(
            {
                "Committee Sizes": committee_sizes,
                "Percentage of Participants Excluded": not_selected_percentages,
                "Std Dev": std_dev_values,
            }
        )
        # Plot percentage excluded on ax3 (now the last subplot).
        sns.lineplot(
            x="Committee Sizes",
            y="Percentage of Participants Excluded",
            data=plot_data_excluded,
            marker="o",
            label=group_size,
            ax=ax3,
        )

        # Plot the distinct number of committee members on ax1.
        plot_data_distinct = pd.DataFrame(
            {
                "Committee Sizes": committee_sizes,
                "Distinct Number of Committee Members": mean_values.values,
            }
        )
        sns.lineplot(
            x="Committee Sizes",
            y="Distinct Number of Committee Members",
            data=plot_data_distinct,
            marker="o",
            label=group_size,
            ax=ax1,
        )

        # Compute and plot the ratio of distinct committee members to committee size on ax2.
        dcs_ratios = mean_values.values / np.array(committee_sizes)
        plot_data_ratio = pd.DataFrame(
            {
                "Committee Sizes": committee_sizes,
                "Distinct/Committee Ratio": dcs_ratios,
            }
        )
        sns.lineplot(
            x="Committee Sizes",
            y="Distinct/Committee Ratio",
            data=plot_data_ratio,
            marker="o",
            label=group_size,
            ax=ax2,
        )

    # Formatting ax1: Distinct Committee Members Plot.
    ax1.set_ylabel("Distinct Committee Members")
    ax1.set_xlabel("Committee Size, k")
    ax1.set_title(f"Distinct Committee Members Averaged over {num_iter} Epochs")
    ax1.legend(title="Group Size, n", loc="upper left")
    ax1.grid(True)

    # Formatting ax2: Ratio Plot for Byzantine Tolerance (Distinct/Committee).
    ax2.set_ylabel("Distinct/Committee Ratio")
    ax2.set_xlabel("Committee Size, k")
    ax2.set_title(
        "Ratio of Distinct Members to Committee Size\n(Byzantine Fault Tolerance)"
    )
    ax2.axhline(
        y=1 / 3, color="red", linestyle="--", linewidth=1, label="1/3 Threshold"
    )
    ax2.axhline(
        y=2 / 3, color="blue", linestyle="--", linewidth=1, label="2/3 Threshold"
    )
    ax2.legend(title="Participant Group Size, n", loc="upper right")
    ax2.grid(True)

    # Formatting ax3: Percentage Excluded Plot.
    ax3.set_ylabel("Percentage Excluded from Committee")
    ax3.set_xlabel("Committee Size, k")
    ax3.set_title("Percentage of Group Not Selected for Committee Seats")
    ax3.legend(title="Group Size, n", loc="upper right")
    ax3.grid(True)

    plt.tight_layout()
    plt.show()


# %%
# Let's define a new function like plot_participation above that
# will plot the results in a 3D plot instead of two charts.
def plot_participation_3d(
    sim_results_df: pd.DataFrame,
    group_labels: list,
    committee_labels: list,
    num_iter: int,
):
    """
    Plot the percentage of group participants excluded from a committee
    of a given size vs. different group sizes in an interactive 3D plot,
    and connect the points with a mesh.

    Args:
    - sim_results_df (pd.DataFrame): The simulation results DataFrame.
    - committee_labels (list): The labels for the committee sizes.
    - group_labels (list): The labels for the group sizes.
    - num_iter (int): The number of iterations for the simulation.

    Returns:
        (fig, ax): Matplotlib figure and 3D axes objects for further interaction.
    """
    # Extract numerical values from labels.
    group_sizes = [int(c.split("=")[1].strip()) for c in group_labels]
    committee_sizes = [int(c.split("=")[1].strip()) for c in committee_labels]

    fig = plt.figure(
        "Percentage of Group Not Selected for Committee Seats", figsize=(16, 8)
    )
    ax = fig.add_subplot(111, projection="3d")

    # Prepare a mesh grid for the 3D surface.
    committee_sizes_arr = np.array(committee_sizes)
    group_sizes_arr = np.array(group_sizes)
    X, Y = np.meshgrid(committee_sizes_arr, group_sizes_arr)
    Z = np.empty(X.shape, dtype=float)

    # Loop over each group to compute the percentage excluded.
    for i, label in enumerate(group_labels):
        group_size = group_sizes[i]
        # Extract distinct voters metrics for the current group label.
        committee_voters = sim_results_df.loc["Distinct Voters", label]
        mean_values = committee_voters.loc["mean"]
        # Calculate the percentage of participants not selected.
        not_selected_percentages = (1.0 - mean_values / group_size) * 100
        # Store in the mesh grid array.
        Z[i, :] = not_selected_percentages.values

        # Also scatter the points.
        ax.scatter(
            committee_sizes_arr,
            [group_size] * len(committee_sizes_arr),
            not_selected_percentages.values,
            label=group_size,
            marker="o",
        )

    # Connect the points with a mesh (wireframe).
    ax.plot_wireframe(X, Y, Z, color="grey", linewidth=1, alpha=0.5)

    ax.set_xlabel("Committee Size, k")
    ax.set_ylabel("Participant Group Size, n")
    ax.set_zlabel("Percentage of Participants Excluded from Committee")
    ax.set_title("Percentage of Group Not Selected for Committee Seats", fontsize=16)
    ax.legend(
        title="Group Size, n",
        loc="center left",
        # bbox_to_anchor=(-0.9, 0.9),
    )
    plt.tight_layout(rect=[0, 0, 1.6, 1.6])
    plt.show()
    # Return the figure and axes for further interaction.
    return fig, ax


# %%


def std_error(data, **kwargs):
    """Function that returns lower and upper error bounds"""
    return (
        data["Percentage Excluded"] - data["Std Dev"],
        data["Percentage Excluded"] + data["Std Dev"],
    )


# %%


def assign_commitee(
    group: pd.DataFrame,
    committee_size: int = 300,
    alpha: float = 0.0,
    num_iter: int = 1000,
    plot_it: bool = False,
    figsize: tuple[int, int] = (16, 8),
) -> dict[pd.DataFrame, pd.Series, float, float, int]:
    """
    Assumes participants in a given group of size group_size are assigned to
    a committee using random selection with replacement based on their stake
    weight. The committee has a fixed size equal to the group_size. As such,
    partipants with larger stake-weight will occupy multiple committee seats.
    We perform Monte Carlo simulation of multiplle committee selections, thus
    repeated for the given number of iterations.

    Args:
    - group: DataFrame containing the group of participants, assumed size n.
    - committee_size: Size of the committee (k).
    - alpha: Probability of uniform random sampling in a mixture model.
    - num_iter: Number of iterations for Monte Carlo simulation.
    - plot_it: Boolean flag to plot the committee seat distribution.
    - figsize: Size of the figure.

    Returns:

    Dictionary containing the following key-values:
    - 'voting_strength_vectors': List of voting strength vectors for each iteration.
    - 'seat_counts': Series containing the committee seat average.
    - 'distinct_voters': Average number of distinct voters over the iterations.
    - 'distinct_voters_std': Standard deviation of the number of distinct voters.
    - 'first_zero_index': Index where the seat count first goes to zero.

    """
    group_size = group.shape[0]  # size n

    voting_strength_vectors = []

    # Initialize an array to store the number of
    # committee seats per participant as first-order statistics
    seat_counts = pd.Series(
        np.zeros(group_size, dtype="int64"),
        index=group.index,
        dtype="int64",
        name="seat counts",
    )

    # Initialize an array to store the number of distinct voters
    distinct_voters_lst = []
    # for each iteration and fist- and second-moment statistics
    # collected below

    for n in range(num_iter):  # Monte Carlo simulation loop
        #
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

        # Count the number of distinct voters
        # Store the voting-strength vector for each unique participant
        # sorted in descending order of the number of committee seats
        voting_strength_vec = participant_counts.sort_values(ascending=False)
        voting_strength_vec = voting_strength_vec[voting_strength_vec > 0]
        distinct_voters_lst.append(len(voting_strength_vec))

        # Store the voting strength vector for each iteration
        voting_strength_vectors.append(voting_strength_vec)

    ## Normalize the sum_counts by total sum of counts
    # seat_counts /= seat_counts.sum()
    # rather:
    # Average the seat_counts over the iterations
    seat_counts /= num_iter

    # Average the number of distinct voters over the iterations
    distinct_voters_avg = np.mean(distinct_voters_lst)

    # Standard deviation of the number of distinct voters
    distinct_voters_std = np.std(distinct_voters_lst)

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

    return dict(
        voting_strength_vectors=voting_strength_vectors,
        seat_counts=seat_counts,
        distinct_voters=(distinct_voters_avg, distinct_voters_std),
        first_zero_index=first_zero_index,
    )


# %%
def swap_column_levels(df):
    """Sort the 2-level column labels based on the numeric values
    in the labels and swap the levels of the columns for the next steps.

    Args:
    - df (DataFrame): The DataFrame with 2-level column labels

    Returns:
    - tuple: A tuple containing the following:
        - df (DataFrame): The DataFrame with sorted and swapped column levels
        - l0 (list): The sorted level 0 column labels
        - l1 (list): The sorted level 1 column labels

    """
    # Swap the levels of the columns for the next steps
    df = df.swaplevel(0, 1, axis=1).sort_index(axis=1)

    l0 = sorted(
        df.columns.get_level_values(0).unique(),
        key=lambda c: int(c.split("=")[1].strip()),
    )
    l1 = sorted(
        df.columns.get_level_values(1).unique(),
        key=lambda c: int(c.split("=")[1].strip()),
    )
    # Reorder df columns according to the sorted levels
    df = df.reindex(columns=pd.MultiIndex.from_product([l0, l1]))

    return df, l0, l1


# %%
def simulate(
    population: pd.DataFrame,
    comm_sizes: list,
    group_sizes: list,
    num_iter: int,
    plot_it: bool = False,
) -> pd.DataFrame:
    """Simulate the committee selection process for varying group sizes
    and committee sizes and return the results in a DataFrame.

    Args:
    - population: DataFrame containing the population of SPOs.
    - comm_sizes: list of committee sizes to simulate.
    - group_sizes: list of group sizes to simulate.
    - num_iter: int number of iterations for the Monte Carlo simulation.
    - plot_it: bool flag to plot the results. Default is False.

    Returns:
    - results_df: DataFrame containing the results of the simulation.

    """
    # Dictionary to hold simulation data for each (committee_size, group_size) pair.
    # For each pair, we compute a DataFrame of metrics (rows: e.g. "Distinct Voters",
    # "Committee Seats") with columns "mean" and "sd". Later we stack these so that
    # the row index becomes a MultiIndex (metric, statistic) and the DataFrame columns
    # become a MultiIndex over (committee_size, group_size).
    sim_dict = {}

    for comm_size in comm_sizes:
        print("_" * 50)
        print(f"\nCommittee Size = {comm_size}")
        print("=" * 50)
        print("Group Size | Distinct Voters (mean, std dev)")
        print("-" * 50)

        for group_size in group_sizes:
            group_stakes = get_stake_distribution(
                population,
                group_size=group_size,
                num_iter=num_iter,
                # plot_it=plot_it,  # Turn off
            )

            committee_results = assign_commitee(
                group_stakes,
                committee_size=comm_size,
                num_iter=num_iter,
                plot_it=plot_it,
            )

            # Distinct voters metrics from the tuple
            distinct_voters_avg, distinct_voters_std = committee_results[
                "distinct_voters"
            ]

            print(
                f"{group_size:>6d} | {distinct_voters_avg:.1f}, {distinct_voters_std:.1f}"
            )

            # Compute statistics for committee seat counts
            seat_counts = np.array(committee_results["seat_counts"])

            # Build the metrics dictionaries for DataFrame construction
            mean_stats = {
                "Distinct Voters": distinct_voters_avg,
                "Committee Seats": pd.Series(
                    seat_counts,
                    index=group_stakes.index,
                    name="Committee Seats (average)",
                ),
            }
            sd_stats = {
                "Distinct Voters": distinct_voters_std,
            }

            # Create a DataFrame with columns for mean and std dev
            tmp_df = pd.DataFrame({"mean": mean_stats, "sd": sd_stats})

            # Stack to get a Series with MultiIndex (metric, statistic)
            sim_dict[(comm_size, group_size)] = tmp_df.stack()

    # Convert the dictionary into a DataFrame.
    sim_results_df = pd.DataFrame(sim_dict)

    # Create MultiIndex column labels in the desired string format.
    sim_results_df.columns = pd.MultiIndex.from_tuples(
        [
            (f"Committee Size = {cs}", f"Group Size = {gs}")
            for cs, gs in sim_results_df.columns
        ],
        names=["Committee Size", "Group Size"],
    )

    return sim_results_df
