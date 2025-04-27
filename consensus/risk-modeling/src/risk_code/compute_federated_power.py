#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import numpy as np
import matplotlib.pyplot as plt


def compute_federated_power(
    whale_real_stake,
    other_real_stake,
    threshold_voting_power,
):
    """
    Purpose: This function calculates the federated voting power needed to
    reduce a whale's voting power below a specified threshold.

    Parameters:

    whale_real_stake: The whale's stake as a percentage of the total stake.
    other_real_stake: The combined stake of other Stake Pool Operators (SPOs)
    as a percentage of the total stake.
    threshold_voting_power: The threshold for the whale's effective voting
    power (in percentage).

    Logic:

    If the whale's stake is already below the threshold, no federated power
    is needed, so the function returns 0.
    Otherwise, it calculates the total real stake by summing the whale's stake
    and the other SPOs' stake.
    It then computes the whale's fraction of the total stake. The federated
    power needed is calculated to ensure the whale's voting power is reduced
    below the threshold.
    The function ensures the federated power is non-negative by returning the
    maximum of 0 and the calculated value.

    Returns:
    - Federated voting power as a fraction of total voting power (0 to 1).

    """
    # No federated power needed if whale stake is below the threshold
    if whale_real_stake < threshold_voting_power:
        return 0

    total_real_stake = whale_real_stake + other_real_stake

    whale_fraction = whale_real_stake / total_real_stake

    federated_power = 1 - (threshold_voting_power / 100) / whale_fraction

    return max(0, federated_power)  # Ensure F is non-negative


if __name__ == "__main__":

    # Define parameters
    threshold_voting_power = 33  # Whale voting power threshold (in %)
    other_real_stake = 60  # Other SPOs' stake (in %)
    whale_real_stake_range = np.linspace(
        10, 50, 100
    )  # Whale stake range from 10% to 50%

    # Compute federated power for each whale real stake
    federated_power_needed = [
        compute_federated_power(
            whale,
            other_real_stake,
            threshold_voting_power,
        )
        for whale in whale_real_stake_range
    ]

    # Convert to percentages
    federated_power_needed_percent = [f * 100 for f in federated_power_needed]

    # Plot the graph
    plt.figure(figsize=(10, 6))
    plt.plot(
        whale_real_stake_range,
        federated_power_needed_percent,
        label="Federated Power Needed",
        color="blue",
    )
    plt.axhline(
        40,
        color="red",
        linestyle="--",
        label="40% Federated Voting Power",
    )
    plt.axvline(
        threshold_voting_power,
        color="green",
        linestyle="--",
        label="33% Whale (Critical Threshold)",
    )
    plt.title(
        "Federated Voting Power Needed to Eliminate Whale as SPOF",
        fontsize=14,
    )
    plt.xlabel("Whale Real Stake (% of Total Real Stake)", fontsize=12)
    plt.ylabel("Federated Voting Power Needed (%)", fontsize=12)
    plt.legend(fontsize=10)
    plt.grid(alpha=0.3)
    plt.tight_layout()
    plt.show()
