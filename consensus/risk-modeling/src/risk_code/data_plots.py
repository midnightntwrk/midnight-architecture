#!/usr/bin/env python
# coding: utf-8
"""
This script contains functions to plot various data visualizations from a dataset. 
It includes histograms, joint plots, and probability plots for whale emergence. 
The script reads configuration from a JSON file and uses the specified file paths 
to load data and generate the plots.

"""
# %%
import logging
import json
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from pathlib import Path
from config_loader import load_config
from sim_whale_probs import load_data


# Define a color palette
color_palette = sns.color_palette("tab20", 20)  # 20 colors


def plot_histograms_of_data(file_path: str):
    """Plots histograms of the 'stake' and 'blocks' columns in the dataset.

    Args:
        file_path (str): The path to the CSV file containing the dataset.
    """
    # Load the dataset
    df = pd.read_csv(file_path)

    # Set the aesthetic style of the plots
    sns.set_style("whitegrid")

    # Create histograms
    plt.figure(figsize=(14, 6))

    # Histogram for 'stake'
    plt.subplot(1, 2, 1)
    sns.histplot(df["stake"], bins=20, color="blue", kde=True)
    plt.xlabel("Stake")
    plt.ylabel("Frequency")
    plt.title("Histogram of Stake")

    # Histogram for 'blocks'
    plt.subplot(1, 2, 2)
    sns.histplot(df["blocks"], bins=20, color="green", kde=True)
    plt.xlabel("Blocks")
    plt.ylabel("Frequency")
    plt.title("Histogram of Blocks")

    # Adjust layout and show the plot
    plt.tight_layout()
    plt.show()


def plot_joint_plots(file_path: str):
    """This function loads the dataset from the specified file path,
    sets the aesthetic style of the plots, creates a joint plot of
    histograms for 'stake' and 'stake_percent' using a hexbin plot,
    and displays the plot with appropriate labels and title.

    Parameters:
        file_path (str): The path to the CSV file containing the dataset.

    Returns:
        None
    """
    # Load the dataset
    df = load_data(file_path)

    # Set the aesthetic style of the plots
    sns.set_style("whitegrid")

    # Create a joint plot of histograms for 'stake' and 'stake_percent'
    sns.jointplot(
        x=df["stake"],
        y=df["stake_percent"],
        kind="hex",
        color="green",
        marginal_kws=dict(bins=20, fill=True),
    )

    # Add labels and title
    plt.xlabel("Stake")
    plt.ylabel("Stake Percent")
    plt.suptitle("Joint Plot of Stake and Stake Percent", y=1.02)

    # Show the plot
    plt.show()


def plot_whale_probability(output_path: str, figsize=(16, 10)):
    """Plots the probability of whale emergence vs. Whale Real Stake (R_w)
    for different group sizes using facets.

    Args:
        output_path (str): The path to the CSV file containing the simulation results.
        figsize (tuple, optional): plot figure size. Defaults to (16, 12).
    """
    # Load the CSV file
    data = pd.read_csv(output_path)

    # Set the Whale Real Stake (R_w) as the index
    data.set_index("R_w", inplace=True)

    # Set the aesthetic style of the plots
    sns.set_theme(style="whitegrid")

    # Plot the data
    plt.figure(figsize=figsize)
    for i, column in enumerate(data.columns):
        sns.lineplot(
            x=data.index,
            y=data[column],
            marker="o",
            markersize=6,
            label=column,
            color=color_palette[i % len(color_palette)],  # Use the color palette
        )

    # Plot vertical lines at 33% and 66% stake
    plt.axvline(x=33, color="red", linestyle="--", label="33% Stake")
    plt.text(
        33,
        plt.ylim()[0],  # Position at the bottom
        "33% Stake",
        color="red",
        ha="center",
        va="bottom",
    )
    plt.axvline(x=66, color="blue", linestyle="--", label="66% Stake")
    plt.text(
        66,
        plt.ylim()[0],  # Position at the bottom
        "66% Stake",
        color="blue",
        ha="center",
        va="bottom",
    )

    # Add labels and title
    plt.xlabel("Whale Real Stake (R_w)", fontsize=14)
    plt.ylabel("Probability", fontsize=14)
    plt.title(
        "Probability vs. Whale Real Stake (R_w) for Different Group Sizes",
        fontsize=16,
    )
    plt.legend(
        title="Group Size",
        fontsize=12,
        title_fontsize=14,
        loc="center left",  # Position legend to the right
        bbox_to_anchor=(1, 0.5),  # Adjust position
    )
    plt.grid(True)

    # Show the plot
    plt.tight_layout()
    plt.show()


def plot_whale_probability_facet(output_path: str, figsize=(16, 10)):
    """Plots the probability of whale emergence vs. Whale Real Stake (R_w)
    for different group sizes using facets.

    Args:
        output_path (str): The path to the CSV file containing the simulation results.
        figsize (tuple, optional): plot figure size. Defaults to (16, 12).
    """
    # Load the CSV file
    data = pd.read_csv(output_path)

    # Set the Whale Real Stake (R_w) as the index
    data.set_index("R_w", inplace=True)

    # Melt the data for seaborn
    melted_data = pd.melt(
        data.reset_index(),
        id_vars=["R_w"],
        var_name="Group_Size",
        value_name="Probability",
    )

    # Set the aesthetic style of the plots
    sns.set_theme(style="whitegrid")

    # Using seaborn's FacetGrid to create multiple plots
    g = sns.FacetGrid(
        melted_data,
        col="Group_Size",
        col_wrap=3,
        height=2,
        aspect=1.5,
        palette=color_palette,
    )
    g.map_dataframe(
        sns.lineplot,
        x="R_w",
        y="Probability",
        hue="Group_Size",
        palette=color_palette,
    )
    g.set_titles("Group_Size_{col_name}")
    g.set_axis_labels("Whale Real Stake (R_w)", "Probability")
    g.add_legend()

    # Set y-axis to logarithmic scale
    g.set(yscale="log")

    # Show the plot
    plt.show()

# %%
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

    # %%
    plot_histograms_of_data(str(FILE_PATH))
    # %%
    plot_joint_plots(str(FILE_PATH))
    # %%
    plot_whale_probability(str(OUTP_PATH))
    # %%
    plot_whale_probability_facet(str(OUTP_PATH))
    # %%
