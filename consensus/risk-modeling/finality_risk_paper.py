# Module comment:
#   This module simulates the process of selecting a committee
#   and evaluating its fault tolerance.

import math
import numpy as np
import matplotlib.pyplot as plt

def random_participants(population: list[(int, int, int)], num_participants: int) -> list[int]:
    """
    Randomly select a committee from the population.
    """
    ids, stakes = zip(*population)
    # lookup population tuple by id
    if any(id < 0 for id in ids):
        raise ValueError("Negative ids found in population")
    return [population[i] for i in np.random.choice(len(population), num_participants, replace=False).tolist()]


PRINT_TABLE = False
PRINT_SEAT_INFO = False

def weighted_config(
        participants: list[(int, int)], 
        committee_size: int,
        num_federated_seats: int,
        ) -> list[int]:
    """
    Randomly select a committee from the population, weighted by stake.
    Return the list committe-seat counts of the unique
    committee members.
    """
    # Separate the IDs and stakes
    ids, stakes = zip(*participants)

    # Reserve seats for federated nodes
    permissionless_seats = committee_size - num_federated_seats
        
    # Check for negative stakes
    negative_stakes = [(id, stake) for id, stake in participants if stake < 0]
    if negative_stakes:
        # print(f"participants = {participants}")
        print(f"negative stakes found: {negative_stakes}")
        raise ValueError("Negative stakes found in participants")

    # Compute the probability of each member being selected
    total_weight = sum(stakes)
    if total_weight == 0:
        print(f"total_weight is zero, which means the population is all zero stakes")
        return [0] * permissionless_seats # reserve seats for federated nodes
    probabilities = [stake / total_weight for stake in stakes]
    
    # Debug prints
    #print(f"ids = {ids}")
    #print(f"stakes = {stakes}")
    #print(f"total_weight = {total_weight}")
    #print(f"probabilities = {probabilities}")
    
    # Ensure all probabilities are non-negative
    if any(prob < 0 for prob in probabilities):
        raise ValueError("Probabilities must be non-negative")
    
    # Check for NaN probabilities
    if any(math.isnan(prob) for prob in probabilities):
        bad_participants = [(id, stake) for id, stake, _ in participants if math.isnan(stake / total_weight)]
        print(f"NaN probability for total_weight = {total_weight}, participants = {bad_participants}")
        raise ValueError("NaN probabilities found")

    # Select the committee
    selected_indices = np.random.choice(len(ids), permissionless_seats, p=probabilities)
    selected_ids = [participants[i][0] for i in selected_indices]

    # adj = 1
    # if num_federated > 0:
    #     adj = 1 - federated_perc
    #     if adj > 1 or adj < 0:
    #         print(f"adjustment = {adj}")
    #         raise ValueError("Adjustment must be between 0 and 1")

    reintegrated = {}
    for id in selected_ids:
        if id in reintegrated:
            reintegrated[id] += 1
        else:
            reintegrated[id] = 1
        
    return [num_seats for id, num_seats in reintegrated.items()]


def faults_tolerated(
        committee_size: int,
        permissioned_seats: list[int], # list of adjusted voting strengths
        num_federated_seats: int,
        num_federated: int, # F
        num_participants: int, 
        ) -> int:
    """
    Expanded version of faults_tolerated that allows federated nodes to
    fail as well as SPOs.  Altered signature and return type: this is
    now a predicate for a given target f
    """
    global PRINT_SEAT_INFO

    seats_per_fed = num_federated_seats / num_federated
    feds = [ seats_per_fed ] * num_federated
    descending = sorted(permissioned_seats + feds, reverse=True)
    threshold = 0.34

    if PRINT_SEAT_INFO:
        print(f"selected {len(permissioned_seats)/num_participants:.0%}, seats_per_fed = {seats_per_fed}, descending = {sorted(permissioned_seats, reverse=True)}")
        PRINT_SEAT_INFO = False
        for n in descending:
            print(f"{n:.2f}")
        print('-' * 80)
    
    x, f = 0, 0
    for v in descending:
        strength = v/committee_size
        # print(f"strength = {strength}, x = {x}, f = {f}, threshold = {threshold}")
        if x + strength >= threshold:
            return f
        x += strength
        f += 1
    return f


def driver(
        population: list[int], 
        committee_size: int, 
        target_f: int, 
        iterations: int,
        num_participants: int,
        num_federated_seats: int,
        num_federated_nodes: int,
        ) -> float:
    """
    Simulate running the committee selection and fault tolerance calculation
    for a number of iterations, computing the probability of choosing a committee
    whose f escapes the target_f.
    """
    global PRINT_SEAT_INFO
    # PRINT_SEAT_INFO = True
    good_config_count = 0
    for _ in range(iterations):
        participants = random_participants(population, num_participants)
        permissioned_seats = weighted_config(participants, committee_size, num_federated_seats)
        f =  faults_tolerated(committee_size, permissioned_seats, num_federated_seats, num_federated_nodes, num_participants)
        if f >= target_f:
            good_config_count += 1
    print(f"num good configs = {good_config_count}")
    return 1 - good_config_count / iterations

def hex_to_int(hex_str):
    return int(hex_str, 16)

def plotter(
        committee_size: int, 
        num_participants: int,
        num_federated_nodes: int,
        ):
    """create datasets in a format needed to plot as in fake_consensus_fault_curves.py"""
    color_options = ['tab:red', 'tab:orange', 'tab:blue', 'tab:pink', 'tab:purple']
    federated_percs = [0.0, 0.20, 0.34, 0.49]
    # federated_percs = [0.2, 0.5]
    target_f = np.array(range(1, 51, 2))
    iterations = 1_000
    population = np.genfromtxt('data/pooltool-cleaned.csv', delimiter=',', converters={0: hex_to_int}, dtype=int)
    population = [participant for participant in population if participant[1] >= 0]
    # drop the unwanted 3rd column (blocks produced)
    population = [(participant[0], participant[1]) for participant in population]

    data = {}

    if num_federated_nodes > 0:
        for fp in federated_percs:
            num_federated_seats = int(fp * committee_size)
            probabilities = []
            print(f"committee_size = {committee_size}, iterations = {iterations}, num_participants = {num_participants}, num_federated_seats = {num_federated_seats}, num_federated = {num_federated_nodes}")
            for f in target_f:
                p_escape = driver(population, committee_size, f, iterations, num_participants, num_federated_seats, num_federated_nodes)
                probabilities.append(1 - p_escape)
            # convert probabilities to np.array, and record results in data
            data[f"{fp:.0%}"] = np.array(probabilities)
        colors = {f"{num_federated_seats:.0%}": color for num_federated_seats, color in zip(federated_percs, color_options)}
    else:
        participation_levels = [50, 100, 200, 1000, 2000]
        for p in participation_levels:
            probabilities = []
            for f in target_f:
                p_escape = driver(population, committee_size, 0, f, iterations, p, 0)
                probabilities.append(1 - p_escape)
            # convert probabilities to np.array, and record results in data
            data[f"{p}"] = np.array(probabilities)
        colors = {f"{p}": color for p, color in zip(participation_levels, color_options)}

    # Make a dense array of f-values for smooth plotting
    f_smooth = np.linspace(target_f.min(), target_f.max(), 300)

    plt.figure(figsize=(6, 6))
    plt.xticks(range(1, 51, 5))

    for label, p_values in data.items():
        # Use a gentle spline so we don’t overshoot near f=0
        from scipy.interpolate import PchipInterpolator
        interpolator = PchipInterpolator(target_f, p_values)
        p_smooth = interpolator(f_smooth)
        
        # Plot the original data as scatter points
        plt.scatter(target_f, p_values, color=colors[label], label=f"_nolabel_", alpha=0.7)
        # Plot the spline‐interpolated curve
        if num_federated_nodes > 0:
            plt.plot(f_smooth, p_smooth, color=colors[label], label=f"{label} federated seats")
        else:
            plt.plot(f_smooth, p_smooth, color=colors[label], label=f"{label} participants")

    plt.xlabel("f = number of concurrent faults")
    plt.ylabel("Probability of a committee that tolerates f faults")
    plt.ylim(0, 1.05)
    if num_federated_nodes > 0:
        plt.title(f"{num_participants} SPOs, {num_federated_nodes} federated nodes")
    else:
        plt.title(f"Inherent Risks")
    plt.legend()
    plt.grid(True)
    plt.tight_layout()
    plt.show()
    
def main(committee_size: int, num_participants: int, num_federated: int = 10):
    plotter(committee_size, num_participants, num_federated)

if __name__ == "__main__":
    # parse federated_perc and target_f from command line
    import sys
    if len(sys.argv) != 3:
        print("Usage: python sim_residual_risk.py <committee_size> <num_participants>")
        sys.exit(1) # error
    main(int(sys.argv[1]), int(sys.argv[2]))

