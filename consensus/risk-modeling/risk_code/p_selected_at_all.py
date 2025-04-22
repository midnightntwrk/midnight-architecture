import numpy as np
import matplotlib.pyplot as plt

# ----------------------------------------------------------
# 1. Example weights dataset (replace with your real data)
# ----------------------------------------------------------

def hex_to_int(hex_str):
    return int(hex_str, 16)

def random_participants(num_participants: int) -> list[int]:
    """
    Randomly select a committee from the population.
    """
    population = np.genfromtxt('consensus/risk-modeling/data/pooltool-cleaned.csv', delimiter=',', converters={0: hex_to_int}, dtype=int)
    population = [participant for participant in population if participant[1] >= 0]
    # drop the unwanted 3rd column (blocks produced)
    population = [(participant[0], participant[1]) for participant in population]
    ids, stakes = zip(*population)
    # lookup population tuple by id
    if any(id < 0 for id in ids):
        raise ValueError("Negative ids found in population")
    return [population[i] for i in np.random.choice(len(population), num_participants, replace=False).tolist()]

participants = random_participants(300)
W = sum(stake for _, stake in participants)
weights = sorted(np.array([stake for _, stake in participants]))

# Relative weights in [0,1]
rel_weights = weights / W
rel_weights = list(filter(lambda x: x < 1, rel_weights))

# Sort them so the probability curves look smooth
rel_weights_sorted = np.sort(rel_weights)


print(f'max weight: {max(rel_weights)}')
print(f'min weight: {min(rel_weights)}')
print(f'mean weight: {np.mean(rel_weights)}')
print(f'median weight: {np.median(rel_weights)}')
print(f'std weight: {np.std(rel_weights)}')
print(f'var weight: {np.var(rel_weights)}')


# ----------------------------------------------------------
# 2. Define the committee sizes to plot (the 4 "slices")
# ----------------------------------------------------------
k_values = [200, 300, 500]

# ----------------------------------------------------------
# 3. Plot probability vs. relative weight for each k
# ----------------------------------------------------------
plt.figure(figsize=(8, 6))

for k in k_values:
    # Probability that a participant with rel. weight f is chosen >= 1 time in a k-sized committee
    probs = 1 - (1 - rel_weights_sorted)**k
    
    plt.plot(rel_weights_sorted, probs, label=f'k = {k}')

# ----------------------------------------------------------
# 4. Formatting the plot
# ----------------------------------------------------------
plt.xlabel('Relative Weight (w_p / W)')
plt.ylabel('Probability of Being Chosen At Least Once')
plt.title('Probability vs. Relative Weight for Different Committee Sizes')
plt.legend()
plt.grid(True)

plt.show()