#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import numpy as np
from ciw import Simulation, create_network, seed
from ciw.dists import Exponential

"""
Blockchain Consensus Queueing Network Simulator

This module implements a 10-node queueing network simulation to model the flow
of transactions through a blockchain consensus system using the Ciw library.

Network Structure:
- Node 1: Client Submission (external arrivals)
- Node 2: Initial Processing (Trusted Service Host / Proof Server) - 2 servers
- Node 3: Mempool Ingress
- Node 4: BFT Leader Proposal (Proposal Phase)
- Node 5: Voting Round-trip (Voting Phase)
- Node 6: Failure/Retry Processing (failed transactions; retries go back to Node 3)
- Node 7: Simple Consensus Finalization (successful simple branch)
- Node 8: Complex Consensus Additional RTT (pre-finalization for complex transactions)
- Node 9: Simple Finalization (exit for simple transactions)
- Node 10: Complex Finalization (exit for complex transactions)

The simulation includes probabilistic branching after the consensus phases with:
- 20% failure rate (transactions routed to failure/retry processing)
- 56% simple transaction rate (faster finalization path)
- 24% complex transaction rate (requiring additional round-trip time)

This model can be used to analyze throughput, waiting times, and bottlenecks
in blockchain consensus systems under various parameter configurations.

Dependencies:
- ciw: https://github.com/CiwPython/Ciw
- numpy: https://numpy.org/
"""
# Branching probabilities after the two-phase consensus:
p_failure = 0.2  # 20% chance of failure after voting phase.
p_simple = 0.56  # 56% chance to continue to a simple finalization.
p_complex = 0.24  # 24% chance to continue to a complex finalization.

assert p_failure + p_simple + p_complex == 1.0, "Branching probabilities must sum to 1.0."

# Routing matrix:
routing = [
    # Node 1 -> Node 2.
    [0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    # Node 2 -> Node 3.
    [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    # Node 3 -> Node 4 (BFT Leader Proposal)
    [0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    # Node 4 -> Node 5 (Voting Round-trip)
    [0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    # Node 5 -> Branching: Failure, Simple, Complex.
    # 20% to Node 6 (Failure), 56% to Node 7 (Simple path), 24% to Node 8 (Complex path)
    [0.0, 0.0, 0.0, 0.0, 0.0, p_failure, p_simple, p_complex, 0.0, 0.0],
    # Node 6 (Failure/Retry) routes back to Node 3 (retry loop).
    [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    # Node 7 -> Node 9 (Simple Finalization exit)
    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0],
    # Node 8 -> Node 10 (Complex Finalization exit)
    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0],
    # Node 9 is an exit node.
    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    # Node 10 is an exit node.
    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
]

network = create_network(
    arrival_distributions=[
        Exponential(5.0),  # Node 1: Client Submission
        None,  # Node 2
        None,  # Node 3
        None,  # Node 4
        None,  # Node 5
        None,  # Node 6
        None,  # Node 7
        None,  # Node 8
        None,  # Node 9
        None,  # Node 10
    ],
    service_distributions=[
        Exponential(1.0),  # Node 1: Client Submission
        Exponential(1.5),  # Node 2: Initial Processing (2 servers)
        Exponential(2.0),  # Node 3: Mempool Ingress
        Exponential(3.5),  # Node 4: BFT Leader Proposal
        Exponential(2.0),  # Node 5: Voting Round-trip
        Exponential(3.0),  # Node 6: Failure/Retry Processing
        Exponential(3.0),  # Node 7: Simple Consensus Finalization (pre-exit)
        Exponential(4.0),  # Node 8: Complex Consensus Additional RTT
        Exponential(2.5),  # Node 9: Simple Finalization (exit)
        Exponential(2.5),  # Node 10: Complex Finalization (exit)
    ],
    number_of_servers=[1, 2, 1, 1, 1, 1, 1, 1, 1, 1],
    routing=routing,
)
# %%
assert network, "Network construction failed."
num_nodes = network.number_of_nodes
# %%
# Simulate one realization (trial)
sim = Simulation(network)
assert sim, "Simulation construction failed."

# %%
# Simulate until max time.
seed(42)  # Set the seed for reproducibility.
sim.simulate_until_max_time(1000)

# %%
# Get all simulation records
records = sim.get_all_records()

# Report detailed statistics.
print("\nExtended Consensus Model Statistics:")
for node in range(1, num_nodes + 1):
    node_records = [r for r in records if r.node == node]
    if node_records:
        avg_wait = np.mean([r.waiting_time for r in node_records])
        avg_service = np.mean([r.service_time for r in node_records])
        print(f"  Node {node}: Average Waiting = {avg_wait:.3f} s, Average Service = {avg_service:.3f} s")
    else:
        print(f"  Node {node}: No transactions recorded.")

# Overall throughput from the two exit nodes (Node 9 and Node 10).
exit_departures = [r.exit_date for r in records if r.node in [9, 10]]
if exit_departures:
    overall_tps = len(exit_departures) / max(exit_departures)
    print(f"\nOverall Throughput: {overall_tps:.3f} transactions per second")
else:
    print("No transactions completed through the system.")

# Optionally, further analysis can be performed:
retry_records = [r for r in records if r.node == 6]
if retry_records:
    print(f"\nTotal Failure/Retry events (Node 6): {len(retry_records)}")
    avg_retry_wait = np.mean([r.waiting_time for r in retry_records])
    print(f"Average wait time in Retry Node: {avg_retry_wait:.3f} s")
