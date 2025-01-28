
---

## Defining the Function to Compute Federated Voting Power


- **Purpose:** The code calculates and visualizes the federated voting power needed to reduce a whale's voting power below a specified threshold.
- **Function:** `compute_federated_power` computes the required federated power based on the whale's stake, other SPOs' stake, and the threshold.
- **Visualization:** The plot shows how the required federated power changes as the whale's stake varies, with reference lines indicating critical thresholds.

---

### The Script

```python
import numpy as np
import matplotlib.pyplot as plt


def compute_federated_power(whale_real_stake, other_real_stake, threshold_voting_power):
    """
    Compute the federated voting power (F) needed to reduce a whale's voting power below a given threshold.

    Parameters:
    - whale_real_stake: The whale's real stake as a percentage of total real stake.
    - other_real_stake: The other SPOs' real stake as a percentage of total real stake.
    - threshold_voting_power: The threshold for the whale's effective voting power.

    Returns:
    - Federated voting power as a fraction of total voting power (0 to 1).
    """
    if whale_real_stake < threshold_voting_power:
        return 0  # No federated power needed if whale stake is below the threshold
    total_real_stake = whale_real_stake + other_real_stake
    whale_fraction = whale_real_stake / total_real_stake
    federated_power = 1 - (threshold_voting_power / 100) / whale_fraction
    return max(0, federated_power)  # Ensure F is non-negative
```

**Explanation:**

- **Purpose:** This function calculates the federated voting power needed to reduce a whale's voting power below a specified threshold.
- **Parameters:**
  - `whale_real_stake`: The whale's stake as a percentage of the total stake.
  - `other_real_stake`: The combined stake of other Stake Pool Operators (SPOs) as a percentage of the total stake.
  - `threshold_voting_power`: The threshold for the whale's effective voting power (in percentage).
- **Logic:**
  - If the whale's stake is already below the threshold, no federated power is needed, so the function returns `0`.
  - Otherwise, it calculates the total real stake by summing the whale's stake and the other SPOs' stake.
  - It then computes the whale's fraction of the total stake.
  - The federated power needed is calculated to ensure the whale's voting power is reduced below the threshold.
  - The function ensures the federated power is non-negative by returning the maximum of `0` and the calculated value.

---

### Defining Parameters

```python
threshold_voting_power = 33  # Whale voting power threshold (in %)
other_real_stake = 60  # Other SPOs' stake (in %)
whale_real_stake_range = np.linspace(10, 50, 100)  # Whale stake range from 10% to 50%
```

**Explanation:**

- **`threshold_voting_power`:** The threshold for the whale's voting power, set to 33%.
- **`other_real_stake`:** The combined stake of other SPOs, set to 60%.
- **`whale_real_stake_range`:** A range of whale stakes from 10% to 50%, generated using `numpy.linspace` to create 100 evenly spaced values.

---

### Computing Federated Power for Each Whale Real Stake

```python
federated_power_needed = [
    compute_federated_power(whale, other_real_stake, threshold_voting_power)
    for whale in whale_real_stake_range
]
```

**Explanation:**

- This list comprehension iterates over the `whale_real_stake_range` and computes the federated power needed for each whale stake using the `compute_federated_power` function.
- The result is a list of federated power values corresponding to each whale stake in the range.

---

### Converting to Percentages

```python
federated_power_needed_percent = [f * 100 for f in federated_power_needed]
```

**Explanation:**

- This list comprehension converts the federated power values (which are fractions) to percentages by multiplying each value by 100.

---

### Plotting the Graph

```python
plt.figure(figsize=(10, 6))
plt.plot(whale_real_stake_range, federated_power_needed_percent, label="Federated Power Needed", color="blue")
plt.axhline(40, color="red", linestyle="--", label="40% Federated Voting Power")
plt.axvline(threshold_voting_power, color="green", linestyle="--", label="33% Whale (Critical Threshold)")
plt.title("Federated Voting Power Needed to Eliminate Whale as SPOF", fontsize=14)
plt.xlabel("Whale Real Stake (% of Total Real Stake)", fontsize=12)
plt.ylabel("Federated Voting Power Needed (%)", fontsize=12)
plt.legend(fontsize=10)
plt.grid(alpha=0.3)
plt.tight_layout()
plt.show()
```

**Explanation:**

- **Creating the Plot:**
  - `plt.figure(figsize=(10, 6))`: Sets the size of the plot.
  - `plt.plot(...)`: Plots the federated power needed against the whale's real stake.
  - `plt.axhline(40, ...)`: Adds a horizontal line at 40% federated voting power.
  - `plt.axvline(threshold_voting_power, ...)`: Adds a vertical line at the 33% whale voting power threshold.
- **Adding Titles and Labels:**
  - `plt.title(...)`: Sets the title of the plot.
  - `plt.xlabel(...)`: Labels the x-axis.
  - `plt.ylabel(...)`: Labels the y-axis.
- **Adding Legend and Grid:**
  - `plt.legend(...)`: Adds a legend to the plot.
  - `plt.grid(alpha=0.3)`: Adds a grid with 30% transparency.
- **Displaying the Plot:**
  - `plt.tight_layout()`: Adjusts the layout to fit everything neatly.
  - `plt.show()`: Displays the plot.

---

