#!/usr/bin/env python
# coding: utf-8
# %% [markdown]
## Pyro-based fault modeling for blockchain systems
#
# %%
import logging
import time
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import torch
import pyro
import pyro.distributions as dist

from utils import measure_time

# %% [markdown]
# ## Monte Carlo Simulations with Fault Injection
#
#### Concept:
#
# Simulate random faults across nodes to assess the network's resilience.
# By injecting faults based on predefined probabilities, you can observe
# how the system behaves under various failure conditions.
#
#### Implementation:

@measure_time
def monte_carlo_fault_injection(num_nodes, fault_prob, num_iterations):
    """
    Simulates a Monte Carlo fault injection process to estimate the failure rate
    of a consensus algorithm.

    Args:
        num_nodes (int): The number of nodes in the network.
        fault_prob (float): The probability of a fault occurring in any given node.
        num_iterations (int): The number of iterations to run the simulation.

    Returns:
        float: The estimated failure rate of the consensus algorithm based on the simulation.
    """
    s = (
        f"Running monte_carlo_fault_injection with {num_nodes} nodes, fault probability "
        f"{fault_prob}, and {num_iterations} iterations:"
    )
    print("_" * len(s))
    print(s)

    # Set the seed for reproducibility
    pyro.set_rng_seed(0)

    consensus_failures = 0

    for _ in range(num_iterations):
        # Simulate faults across nodes
        faults = pyro.sample(
            "faults", dist.Bernoulli(fault_prob).expand([num_nodes])
        ).bool()
        num_faulty_nodes = faults.sum().item()

        # Define consensus failure condition (e.g., exceeding Byzantine threshold)
        if num_faulty_nodes > (num_nodes // 3):
            consensus_failures += 1

    failure_rate = consensus_failures / num_iterations

    return failure_rate


@measure_time
def monte_carlo_fault_injection_vectorized(num_nodes, fault_prob, num_iterations):
    """
    Simulates fault injection in a network of nodes using a Monte Carlo method
    and vectorized operations.

    Args:
        num_nodes (int): The number of nodes in the network.
        fault_prob (float): The probability of a fault occurring in any given
        node.
        num_iterations (int): The number of Monte Carlo iterations to perform.

    Returns:
        float: The failure rate of the consensus mechanism, defined as the
        proportion of iterations where the number of faulty nodes exceeds the
        Byzantine threshold (one-third of the total nodes).
    """
    s = (
        f"Running monte_carlo_fault_injection_vectorized with {num_nodes} nodes, fault probability "
        f"{fault_prob}, and {num_iterations} iterations:"
    )
    print("_" * len(s))
    print(s)

    # Set the seed for reproducibility
    pyro.set_rng_seed(0)

    # Simulate faults across nodes for all iterations at once
    faults = pyro.sample(
        "faults", dist.Bernoulli(fault_prob).expand([num_iterations, num_nodes])
    ).bool()
    num_faulty_nodes = faults.sum(dim=1)

    # Define consensus failure condition (e.g., exceeding Byzantine threshold)
    consensus_failures = (num_faulty_nodes > (num_nodes // 3)).sum().item()

    failure_rate = consensus_failures / num_iterations

    return failure_rate


# %% [markdown]
#### Run Monte Carlo simulation with parameters:
# ```python
# NUM_NODES = 10
# FAULT_PROB = 0.222
# NUM_ITERATIONS = 100000
# ```

NUM_NODES = 10
FAULT_PROB = 0.222
NUM_ITERATIONS = 100000

for f in [monte_carlo_fault_injection, monte_carlo_fault_injection_vectorized]:
    r = f(NUM_NODES, FAULT_PROB, NUM_ITERATIONS)
    print(f"Consensus failure rate: {r:.4f}")


# %% [markdown]
#### Explanation:
#
# - **Fault Simulation**: Each node can fail independently with a probability
#     `fault_prob`.
# - **Consensus Condition**: In BFT systems, if more than a third of the nodes
#     are faulty, consensus can't be
#     guaranteed.
# - **Iterations**: Running the simulation multiple times provides a
#     statistical estimate of the failure rate.
#
#### Concept:
#
# Model the number of faulty nodes using a Binomial distribution to calculate
# the probability of observing a certain number of failures.
#
#### Implementation:


def binomial_fault_model(num_nodes, fault_prob):
    binomial_dist = dist.Binomial(total_count=num_nodes, probs=fault_prob)
    x = torch.arange(num_nodes + 1)
    probabilities = binomial_dist.log_prob(x).exp()

    # Probability table
    fault_counts = x.numpy()
    fault_probs = probabilities.numpy()
    return fault_counts, fault_probs


# Generate fault probability table
fault_counts, fault_probs = binomial_fault_model(NUM_NODES, FAULT_PROB)
data = pd.DataFrame(
    {"Number of Faulty Nodes": fault_counts, "Probability": fault_probs}
)
data
# %% [markdown]
#### Visualization:
#
# Plot the probability mass function to visualize the likelihood of different numbers of faulty nodes.
#
sns.barplot(x="Number of Faulty Nodes", y="Probability", data=data)
plt.xlabel("Number of Faulty Nodes")
plt.ylabel("Probability")
plt.title("Binomial Distribution of Faulty Nodes")
plt.show()

# %% [markdown]
# ## Markov Chains
#
# #### Concept:
#
# Represent the system's health as states and model transitions between them over time.
#
# #### State Diagram:
#
# ![Markov Chain State Diagram](docs/mc.png)
#
# #### Implementation:
#
# %%


def markov_chain_model(num_steps, failure_rate, recovery_rate):
    states = []
    state = "Healthy"

    for t in range(num_steps):
        if state == "Healthy":
            if pyro.sample(f"fail_{t}", dist.Bernoulli(failure_rate)):
                state = "Degraded"
        elif state == "Degraded":
            if pyro.sample(f"fail_{t}", dist.Bernoulli(failure_rate)):
                state = "Failed"
            elif pyro.sample(f"recover_{t}", dist.Bernoulli(recovery_rate)):
                state = "Healthy"
        states.append(state)

    return states

# %% [markdown]
#### Run the Markov chain model with parameters:
# ```python
# NUM_STEPS = 50
# FAILURE_RATE = 0.05
# RECOVERY_RATE = 0.1
# ```

NUM_STEPS = 50
FAILURE_RATE = 0.05
RECOVERY_RATE = 0.1

states = markov_chain_model(NUM_STEPS, FAILURE_RATE, RECOVERY_RATE)

states

# %% [markdown]
#### Analysis:
#
# - Track the state transitions over time to understand the system's reliability.
# - Analyze the steady-state probabilities of being in each state.
# %%
