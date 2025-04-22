#!/usr/bin/env python
# coding: utf-8
# %% [markdown]
## Pyro-based fault modeling for blockchain systems
### Fault Tree Model
#
# The following considers a fault tree model that incorporates BFT consensus
# thresholds, federated nodes, and the committee selection process for each
# epoch.
#
#### Understanding the System Components
#
# The key components and potential failures in the blockchain network:
#
# 1. **Federated Nodes (Known-Good Validators):**
#    - These are trusted nodes that are less likely to fail or act maliciously.
#    - Failures may occur due to hardware faults, network issues, or targeted
#      attacks.
#
# 2. **Stake Pool Operators (SPOs):**
#    - Registered operators who participate in consensus.
#    - May have varying levels of reliability and susceptibility to faults.
#
# 3. **Committee Selection:**
#    - Validators are selected randomly each epoch.
#    - The randomness and security of the selection process are crucial.
#
# 4. **BFT Thresholds:**
#    - **Liveness Threshold (33%):** The system can make progress if less than
#      33% of the validators are faulty.
#    - **Safety Threshold (67%):** The system remains secure if less than 33%
#      are malicious; it can tolerate up to 67% being offline.
#
#### Fault Tree Model
#
# The model captures the following concepts and salient features:
#
# - **Individual Validator Failures:**
#   - Differentiate between federated nodes and SPOs.
#   - Assign failure probabilities based on node types.
#
# - **Byzantine Faults:**
#   - Include the possibility of nodes acting maliciously.
#
# - **BFT Threshold Logic:**
#   - Define system failure based on the proportion of faulty/malicious
#     validators exceeding the thresholds.
#
# - **Epoch-Based Committee Selection:**
#   - Model the randomness in validator selection each epoch.
#
#### Implementation
# %%
import logging
import time
import functools
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import torch
import pyro
import pyro.distributions as dist
from utils import measure_time
from itertools import product
from multiprocessing import Pool, freeze_support

# Set the random seed for reproducibility
pyro.set_rng_seed(42)


def fault_tree_model(num_federated, num_spos, committee_size):
    """
    Simulates a fault tree model for a blockchain network with federated nodes and SPOs.

    Args:
        num_federated (int): The number of federated nodes in the system.
        num_spos (int): The number of SPOs (Single Point of Failures) in the system.
        committee_size (int): The size of the committee involved in the simulation.

    Returns:
        bool: A boolean indicating whether the system has failed.
    """
    # Total validators
    total_validators = num_federated + num_spos

    # Probabilities
    federated_failure_prob = 0.01  # Federated nodes are more reliable
    spo_failure_prob = 0.05  # SPOs have higher failure probability
    malicious_node_prob = 0.02  # Probability of a node acting maliciously
    network_partition_prob = 0.01  # Probability of a network partition

    # Select committee members randomly each epoch
    committee_members = pyro.sample(
        "committee_members",
        dist.Categorical(probs=torch.ones(total_validators))
        .expand([committee_size])
        .to_event(1),
    )
    committee_indices = committee_members.tolist()

    # Initialize counts
    faulty_nodes = 0
    malicious_nodes = 0

    # Simulate failures in the committee
    for idx in committee_indices:
        if idx < num_federated:
            # Federated node
            node_type = "federated"
            failure = pyro.sample(
                f"failure_{idx}", dist.Bernoulli(federated_failure_prob)
            ).bool()
        else:
            # SPO
            node_type = "spo"
            failure = pyro.sample(
                f"failure_{idx}", dist.Bernoulli(spo_failure_prob)
            ).bool()

        # Check for malicious behavior
        malicious = pyro.sample(
            f"malicious_{idx}", dist.Bernoulli(malicious_node_prob)
        ).bool()

        if failure or malicious:
            faulty_nodes += 1
        if malicious:
            malicious_nodes += 1

        # Log the node type and its status
        logging.debug(
            f"Node {idx} ({node_type}): failure={failure}, malicious={malicious}"
        )

    # Network-level faults
    network_partition = pyro.sample(
        "network_partition", dist.Bernoulli(network_partition_prob)
    ).bool()

    # BFT Thresholds
    faulty_threshold = committee_size * 0.33  # 33% liveness threshold
    malicious_threshold = committee_size * 0.33  # 33% safety threshold

    # Determine system failure
    liveness_failure = faulty_nodes > faulty_threshold
    safety_failure = malicious_nodes > malicious_threshold

    system_failure = (liveness_failure or safety_failure) or network_partition

    return system_failure


# @measure_time
# def simulate_fault_tree(
#     num_federated,
#     num_spos,
#     committee_size,
#     num_iterations,
# ):
#     """
#     Simulates the fault tree model to estimate the system failure probability.
#     Args:
#         num_federated (int): The number of federated nodes in the system.
#         num_spos (int): The number of SPOs (Single Point of Failures) in the system.
#         committee_size (int): The size of the committee involved in the simulation.
#         num_iterations (int): The number of iterations to run the simulation.

#     Returns:
#         None: This function prints the estimated system failure probability.
#     """
#     failures = torch.zeros(num_iterations)

#     for i in range(num_iterations):
#         failures[i] = fault_tree_model(num_federated, num_spos, committee_size)

#     failure_prob = failures.mean().item()
#     return failure_prob


# %%
# # Run the simulation with the specified parameters
# # Parameters
# NUM_ITERATIONS = 10000
# NUM_FEDERATED_NODES = 5
# NUM_SPOS = 20
# COMMITTEE_SIZE = 10

# simulate_fault_tree(
#     NUM_FEDERATED_NODES,
#     NUM_SPOS,
#     COMMITTEE_SIZE,
#     NUM_ITERATIONS,
# )

# %% [markdown]
### Explanation of the Model
#
##### 1. Node Types and Failure Probabilities
#
# - **Federated Nodes:**
#   - Assumed to be more reliable.
#   - **Failure Probability:** `0.01`
#
# - **Stake Pool Operators (SPOs):**
#   - Have a higher chance of failure due to varying resources.
#   - **Failure Probability:** `0.05`
#
# - **Malicious Behavior:**
#   - Any node (federated or SPO) can potentially act maliciously.
#   - **Malicious Probability:** `0.02`
#
##### 2. Committee Selection
#
# - **Random Selection:**
#   - Validators are selected randomly to form a committee each epoch.
#   - **Pyro Sampling:**
#     ```python
#     committee_members = pyro.sample(
#         "committee_members",
#         dist.Categorical(
#             probs=torch.ones(total_validators)
#         ).expand([committee_size]).to_event(1)
#     )
#     ```
#   - This ensures a uniform random selection without replacement.
#
##### 3. Fault Simulation in the Committee
#
# - **Iterating Over Committee Members:**
#   - For each selected validator, we simulate:
#     - **Node Failure:** Hardware/software issues.
#     - **Malicious Activity:** Byzantine faults.
#
# - **Updating Fault Counts:**
#   - **`faulty_nodes`** includes both failed and malicious nodes.
#   - **`malicious_nodes`** only counts malicious validators.
#
##### 4. Network-Level Faults
#
# - **Network Partition:**
#   - Represents a failure in the network that affects communication.
#   - **Probability:** `0.01`
#
##### 5. Applying BFT Thresholds
#
# - **Liveness Failure:**
#   - Occurs if more than 33% of the committee is faulty.
#   - **Calculation:**
#     ```python
#     faulty_threshold = committee_size * 0.33
#     liveness_failure = faulty_nodes > faulty_threshold
#     ```
#
# - **Safety Failure:**
#   - Occurs if more than 33% of the committee is malicious.
#   - **Ensures consensus security.**
#
##### 6. Determining System Failure
#
# - **System Failure Conditions:**
#   - **Liveness Failure:** The system cannot make progress.
#   - **Safety Failure:** The system's security is compromised.
#   - **Network Partition:** A critical network fault.
#   - **Overall Failure:**
#     ```python
#     system_failure = (liveness_failure or safety_failure)
#                      or network_partition
#     ```
# ---
##### NOTEWORTHY:
#
# * In the fault tree, the AND gate represents a scenario where
# multiple conditions must be met simultaneously for the subsequent event to occur.
# Specifically, for a Liveness Failure in your blockchain network, two critical conditions
# need to be satisfied:
#
#   1. Node Failures Occur:
# There must be failures among the nodes in the network—this includes both federated nodes and SPOs.
#
#   2. Failure Threshold Exceeded:
#   The number of faulty nodes exceeds 33% of the committee size.
#
# * The Liveness Failure event is triggered when both of these conditions are met,
# indicating that the network is unable to make progress due to the high proportion
# of faulty nodes.
# * The AND gate is placed between the Liveness Failure and the
# Node Failures to illustrate that both conditions are necessary.
# * It's not sufficient
# for some nodes to fail; the system is designed to handle a certain degree of failure.
# However, when the proportion of faulty nodes surpasses the 33% threshold, the network's
# ability to maintain liveness is compromised.
# ---
#
##### 7. Simulation Function
#
# - **`simulate_fault_tree`:**
#   - Runs multiple iterations to estimate the system failure probability.
#   - **Parameters:**
#     - **`num_iterations`:** Number of simulation runs.
#     - **`num_federated`:** Number of federated nodes.
#     - **`num_spos`:** Number of SPOs.
#     - **`committee_size`:** Number of validators in the committee.
#
#
##### 8. Visualization
#
# To gain more insight, we can run the simulation multiple times and
# plot the distribution of failure probabilities under varying conditions.


# %%
# Simulate with multiprocessing

"""
                  Main Process
                       |
         --------------------------------
        |                                |
   Trial 1 Process                  Trial 2 Process
        |                                |
  run_simulation_trial             run_simulation_trial
        |                                |
  Compute Failure Prob             Compute Failure Prob
        |                                |
   Returns Result                     Returns Result

"""


def run_simulation_trial(args):
    """Run a single simulation trial.

    Args:
        num_federated (int): The number of federated nodes in the system.
        num_spos (int): The number of SPOs (Single Point of Failures) in the system.
        committee_size (int): The size of the committee involved in the simulation.
        num_iterations (int): The number of iterations to run the simulation.
    Returns:
        float: The failure probability of the system.
    """
    num_federated, num_spos, committee_size, num_iterations = args

    failures = torch.zeros(num_iterations)
    for j in range(num_iterations):
        failures[j] = fault_tree_model(
            num_federated,
            num_spos,
            committee_size,
        )
    failure_prob = failures.mean().item()
    return failure_prob


def run_simulation_trials_parallel(
    num_federated: list,
    num_spos: list,
    committee_size: list,
    num_iterations: int,
):
    """Run multiple simulation trials in parallel.

    Args:
        num_federated (list): The number of federated nodes in the system.
        num_spos (list): The number of SPOs (Single Point of Failures) in the system.
        committee_size (list): The size of the committee involved in the simulation.
        num_iterations (int): The number of iterations per trial.
    Returns:
        List[float]: results is a list of failure probabilities from each trial.
    """
    # Run simulations in parallel
    logging.info("Starting simulation...")

    # Generate simulation arguments
    simulation_args = list(
        product(
            num_federated,
            num_spos,
            committee_size,
            [num_iterations],
        )
    )

    with Pool() as pool:
        results = pool.map(run_simulation_trial, simulation_args)

    logging.info("Simulation complete.")

    # Convert results to a DataFrame
    results_df = pd.DataFrame(
        simulation_args,
        columns=["Num Federated", "Num SPOs", "Committee Size", "Num Iterations"],
    )
    results_df["Failure Probability"] = results
    return results_df


def main():
    # Example usage
    NUM_FEDERATED_NODES = [10, 15, 20]
    NUM_SPOS = [10, 20, 30]
    COMMITTEE_SIZE = [10, 20, 30]
    NUM_ITERATIONS = 1000

    return run_simulation_trials_parallel(
        NUM_FEDERATED_NODES,
        NUM_SPOS,
        COMMITTEE_SIZE,
        NUM_ITERATIONS,
    )


# %% [markdown]
#
#### Future Improvements
# - **Dynamic Validator Behavior:**
#   - Model fluctuations in validator reliability over time.
#   - Incorporate historical performance data if available.
#
# - **Correlation of Failures:**
#   - Consider correlated failures, such as widespread power outages or
#     coordinated attacks.
#
# - **Adaptive Thresholds:**
#   - Adjust thresholds based on real-time network conditions.
#
# - **Sidechain Specifics:**
#   - Include any unique failure modes introduced by the Midnight sidechain.
#
# - **Epoch Length Variability:**
#   - Simulate over multiple epochs with varying committee sizes and node
#     counts.
#
# ### **Summary**
#
# By integrating the specifics of your Cardano blockchain network into the
# fault tree model, we have created a more realistic simulation that captures
# key aspects like BFT thresholds, node types, and committee selection. This
# enhanced model can help in assessing the resilience of the network and
# identifying areas for improvement.
#
# %%
if __name__ == "__main__":
    df = main()
    print(df)

    # Visualization

    # Heatmap
    plt.figure(figsize=(12, 8))
    heatmap_data = df.pivot_table(
        index="Num Federated", columns="Committee Size", values="Failure Probability"
    )
    sns.heatmap(heatmap_data, annot=True, cmap="coolwarm")
    plt.title("Failure Probability Heatmap")
    plt.savefig("docs/figs/failure_probability_heatmap.png")
    plt.show()

    # Pairplot
    sns.pairplot(df, hue="Num Federated", palette="coolwarm")
    plt.suptitle("Pairplot of Variables", y=1.02)
    plt.savefig("docs/figs/pairplot_variables.png")
    plt.show()

    # Bar Plot
    plt.figure(figsize=(12, 8))
    sns.barplot(
        x="Num Federated",
        y="Failure Probability",
        hue="Committee Size",
        data=df,
        palette="coolwarm",
    )
    plt.title("Failure Probability by Num Federated and Committee Size")
    plt.savefig("docs/figs/failure_probability_barplot.png")
    plt.show()


# %%
