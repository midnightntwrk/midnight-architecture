#!/usr/bin/env python
# -*- coding: utf-8 -*-

import numpy as np


def compute_federated_nodes(f, F, V_others, quorum_threshold=66.67):
    """
    Compute the minimum number of federated nodes required to tolerate f faults.

    Parameters:
    - f: Desired fault tolerance (number of node failures to tolerate).
    - F: Total federated voting power (%).
    - V_others: Aggregate voting power of non-federated entities (%).
    - quorum_threshold: Quorum threshold (%). Default is 66.67%.

    Returns:
    - Minimum number of federated nodes required (n).
    """
    # Remaining federated voting power required after f faults
    remaining_federated_power = quorum_threshold - V_others

    # Avoid impossible configurations
    if remaining_federated_power > F:
        raise ValueError("Quorum cannot be maintained with the given parameters.")

    # Compute n
    n = (f * F) / (F - remaining_federated_power)
    return int(np.ceil(n))  # Return the ceiling value for integer nodes


# Example usage
if __name__ == "__main__":
    f = 3
    F = 66.67
    V_others = 33.33
    n = compute_federated_nodes(f, F, V_others)
    print(n)
