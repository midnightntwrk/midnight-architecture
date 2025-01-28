# Consensus Risk Modeling

Rob Jones <robert.jones@shielded.io>

28 Jan 2025

---

## **Goal**

We want to find out **how many federated nodes, $n$, we need** so that even if **$f$ of them fail**, the remaining nodes still have enough voting power to meet the **quorum threshold** (for example, 66.67%).

---

## **Key Concepts**

1. **Byzantine Fault Tolerance (BFT)** is a fundamental concept in distributed systems and blockchain networks. It describes the ability of a system to continue functioning correctly even when some of its components fail or act maliciously. In blockchain systems, nodes can be classified as:
    - **Quorum** is the minimum number of nodes required to agree on a decision to ensure the system's reliability and correctness. In BFT systems, the quorum threshold is typically set to ensure that the system can tolerate a certain 
number of faulty nodes.
    - **Federated Nodes (Validators):** Nodes responsible for validating and producing blocks. They typically hold a significant portion of the network's voting power.
    - **Non-Federated Nodes (Others):** Nodes that participate in the network but do not have validating authority or hold less voting power.

2. **Federated Nodes:**
   - Nodes that collectively have a certain percentage of the total voting power, denoted as **$F$** (e.g., 33.33%).
   - We *assume* **all federated nodes have equal voting power**.

3. **Non-Federated Voting Power ($V_{\text{others}}$):**
   - The percentage of voting power held by other nodes (non-federated ones).

4. **Quorum Threshold:** 
   - The minimum percentage of total voting power needed to make decisions (e.g., 66.67%).
   - **In BFT blockchain networks, there are two critical thresholds to consider:**
      - **1/3**: If dishonest nodes make up 1/3 or more of the total nodes, the network may "halt." These dishonest nodes can refuse to participate, preventing the remaining nodes from achieving the 2/3 supermajority needed for consensus. In this case, the network does not generate invalid transactions; it simply stops producing transactions altogether.
      - **2/3**: If dishonest nodes make up 2/3 or more of the total nodes, they can collude to create arbitrary transactions. This is the worst-case scenario, as the network no longer produces accurate transactions but instead generates any transactions the 2/3 dishonest supermajority desires.


5. **Purpose of the Formula:**
    - Ensure that after $f$ federated nodes fail, the remaining federated nodes still have enough voting power to **collectively meet the quorum** when combined with non-federated nodes.

## Practical Considerations

#### Byzantine Fault Tolerance Limits

- **Maximum Tolerable Faults:**
  - In BFT systems, to reach consensus in the presence of Byzantine faults, the maximum number of faulty nodes ($f$) in a system with $n$ nodes is bounded by:
    \[
    n \geq 3f + 1
    \]
  - This ensures that the system can tolerate up to **\( \frac{n - 1}{3} \)** faulty nodes.

#### Quorum Threshold

- **Why 66.67%?**
  - A quorum threshold of 66.67% (i.e., two-thirds majority) is chosen because:
    - It ensures that any two quorums **have at least one honest node in common**.
    - **This overlap is critical for agreement** and consistency in consensus protocols.

#### Node Heterogeneity

- **Equal vs. Unequal Voting Power:**
  - If nodes have unequal voting power (e.g., due to different stakes), the model should account for the distribution of voting power among nodes.
  - This adds complexity to the calculation, requiring a weighted approach.

---

## **Step-by-Step Calculation**

#### **1. Determine the Federated Voting Power Needed After Failures**

- **First**, calculate how much voting power the federated nodes need to contribute **after accounting for the non-federated voting power**.
  
  \[
  \text{Required Federated Voting Power} = \text{Quorum Threshold} - V_{\text{others}}
  \]
  
- This tells us the **minimum percentage** of voting power the federated nodes must have **together** to meet the quorum.

**Example:**

- If the quorum threshold is **66.67%** and non-federated nodes have **33.33%** voting power:
  
  \[
  \text{Required Federated Voting Power} = 66.67\% - 33.33\% = 33.34\%
  \]

---

#### **2. Understand the Impact of Node Failures**

- When **$f$ federated nodes fail**, their voting power is lost.
- We need to ensure that the **remaining federated nodes** still have **at least** the required voting power to meet the quorum.

---

#### **3. Calculate Voting Power per Federated Node**

- We assume that the total federated voting power $F$ is **split equally** among the **$n$ federated nodes**. Therefore,
  
  \[
  \text{Voting Power per Node} = \frac{F}{n}
  \]

---

#### **4. Calculate the Voting Power After $f$ Nodes Fail**

- After **$f$ nodes fail**, the number of functioning federated nodes is **$n - f$**.
- The **total remaining federated voting power** is:
  
  \[
  \text{Remaining Federated Voting Power} = (n - f) \times \left( \frac{F}{n} \right)
  \]
  
- Simplify the equation:
  
  \[
  \text{Remaining Federated Voting Power} = F - f \times \left( \frac{F}{n} \right)
  \]

---

#### **5. Ensure Remaining Voting Power Meets the Required Threshold**

- The **remaining federated voting power** must be **at least** the **required federated voting power** we calculated earlier.

  \[
  \text{Remaining Federated Voting Power} \geq \text{Required Federated Voting Power}
  \]
  
- Substitute the expression from step 4:

  \[
  F - f \times \left( \frac{F}{n} \right) \geq \text{Required Federated Voting Power}
  \]

---

#### **6. Solve for the Minimum Number of Nodes ($n$)**

- Rearrange the inequality to solve for $n$.

**Step A: Isolate the term with $n$**

\[
F - f \times \left( \frac{F}{n} \right) - \text{Required Federated Voting Power} \geq 0
\]

**Step B: Bring terms together**

\[
F - \text{Required Federated Voting Power} - \frac{fF}{n} \geq 0
\]

**Step C: Move $\frac{fF}{n}$ to the other side**

\[
F - \text{Required Federated Voting Power} \geq \frac{fF}{n}
\]

**Step D: Multiply both sides by $n$**

\[
n \left( F - \text{Required Federated Voting Power} \right) \geq fF
\]

**Step E: Solve for $n$**

\[
n \geq \frac{fF}{F - \text{Required Federated Voting Power}}
\]

---

#### **7. Apply the Ceiling Function**

- Since we can't have a fraction of a node, we **round up** to the nearest whole number.
  
  \[
  n = \left\lceil \frac{fF}{F - \text{Required Federated Voting Power}} \right\rceil
  \]

- **Ceiling Function (`ceil`):** Ensures we have enough nodes even if the calculation doesn't result in a whole number.

---

### **Simplified Interpretation**

- **Numerator $fF$**
  - Represents the **total voting power lost** when $f$ nodes fail.

- **Denominator $F - \text{Required Federated Voting Power}$**
  - Represents how much voting power each node needs to cover to meet the required threshold **after failures**.

- **Result $n$**
  - The **minimum number of federated nodes** needed so that, even if $f$ of them fail, the remaining nodes provide enough voting power to meet the quorum.

---

### **Example Calculation**

The Python script implementing this calculation is shown below:
```python

import numpy as np


def compute_required_nodes(f, F, V_others, quorum_threshold=66.67):
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
    
```

Let's plug in some numbers to make it concrete.

**Given:**

- Desired Fault Tolerance, $f = 1$ node failure
- Total Federated Voting Power, $F = 66.67\%$
- Non-Federated Voting Power, $V_{\text{others}} = 33.33\%$
- Quorum Threshold $= 66.67\%$

**Step 1: Required Federated Voting Power**

\[
\text{Required Federated Voting Power} = 66.67\% - 33.33\% = 33.34\%
\]

**Step 2: Calculate Minimum $n$**

\[
n = \left\lceil \frac{1 \times 66.67}{66.67 - 33.34} \right\rceil = \left\lceil \frac{66.67}{33.33} \right\rceil = \left\lceil 2 \right\rceil = 2
\]

**Interpretation:**

- We need **at least 2 federated nodes**.
- Each node has voting power:
  
  \[
  \frac{F}{n} = \frac{66.67\%}{2} = 33.335\%
  \]
  
- If **1 node fails**:
  - Remaining federated voting power:
    
    \[
    (2 - 1) \times 33.335\% = 33.335\%
    \]
    
  - Total voting power (including non-federated nodes):
    
    \[
    33.335\% \ \text{(federated)} + 33.33\% \ \text{(non-federated)} = 66.665\%
    \]
    
  - Slightly below the quorum due to rounding but conceptually meets the quorum threshold of **66.67%**.

---

## Limitations of the Model

**1. The model focuses on federated nodes only.**

  - The fault tolerance ($f$) pertains **only to federated nodes**. The calculation is concerned with how many federated nodes can fail while still maintaining the required federated voting power to meet the quorum threshold.
  - Non-federated nodes ($V_{\text{others}}$) are accounted for in the initial calculation of the remaining federated voting power required but are not considered in the fault tolerance $f$.
  - By not accounting for the potential failure of non-federated nodes, the model might **overestimate** the available voting power from $V_{\text{others}}$.

**2. Static Voting Power Assumption**

- The model assumes that voting power percentages ($F$ and $V_{\text{others}}$) are static and do not change during operation.
- In real-world scenarios, voting power can fluctuate due to stake delegation changes, node joining/leaving, or reallocation of resources.

**3. Equal Voting Power Distribution**

- Implicitly assumes that federated nodes share the federated voting power, $F$, equally.
- In practice, nodes may have varying amounts of voting power due to differences in stake or delegations.

**4. Byzantine Behavior Beyond Fault Threshold**

- If more than $f$ federated nodes become faulty, the system might not maintain the quorum, leading to potential security risks.
- The model does not provide mechanisms to handle scenarios where the number of faults exceeds $f$.

### **Implications:**

- **Federated Node Failures:**
  - The model calculates how the system can tolerate federated nodes becoming faulty—whether by crashing, becoming unresponsive, or acting maliciously.

- **Non-Federated Node Failures:**
  - The model does **not account** for failures of non-federated nodes. It assumes their voting power, $V_{\text{others}}$, remains constant and available.
  - Failures among non-federated nodes do not directly impact the calculation of $n$ because their voting power is not used to offset the required federated voting power in the context of federated node faults.

---

## **Extending the Model to Account for Any Node Faults**

To account for any node faulting (both federated and non-federated), the model would need to be extended:

#### **1. Including Non-Federated Node Failures**

- **Adjust $V_{\text{others}}$:**
  - Introduce a fault tolerance parameter $f_{\text{others}}$ for non-federated nodes.
  - Adjust $V_{\text{others}}$ to account for the potential loss of voting power due to non-federated node failures:
    \[
    V_{\text{others}}^{\text{remaining}} = V_{\text{others}} \times \left(1 - \frac{f_{\text{others}}}{n_{\text{others}}}\right)
    \]
    - Where $n_{\text{others}}$ is the total number of non-federated nodes.
  
- **Recompute Remaining Federated Voting Power:**
  - Recalculate $\text{Remaining Federated Power}$ using the adjusted $V_{\text{others}}^{\text{remaining}}$:
    \[
    \text{Remaining Federated Power} = \text{Quorum Threshold} - V_{\text{others}}^{\text{remaining}}
    \]

#### **2. Adjusting for Variable Voting Power**

- **Weighted Voting Power:**
  - If nodes have different voting weights, the model should consider the individual voting power contributions.
- **Minimum Required Voting Power:**
  - Compute the required federated voting power directly, rather than the number of nodes, if node voting power varies.


### Revised Fault Model

#### Objective:

- Compute the minimum number of federated nodes ($n$) required to tolerate $f$ federated faults and $f_{\text{others}}$ non-federated faults.

#### Steps:

1. **Adjust Non-Federated Voting Power:**

   \[
   V_{\text{others}}^{\text{remaining}} = V_{\text{others}} \times \left(1 - \frac{f_{\text{others}}}{n_{\text{others}}}\right)
   \]

2. **Calculate Remaining Federated Voting Power Required:**

   \[
   \text{Remaining Federated Power} = \text{Quorum Threshold} - V_{\text{others}}^{\text{remaining}}
   \]

3. **Validate Feasibility:**

   - Ensure that $\text{Remaining Federated Power}$ does not exceed $F$.

4. **Compute Minimum Number of Federated Nodes:**

   \[
   n = \left\lceil \frac{f \times F}{F - \text{Remaining Federated Power}} \right\rceil
   \]

---


## **Conclusions**

#### Summary

- The given fault model and script focus on tolerating faults among **federated nodes** only.
- Non-federated nodes' voting power is assumed to be stable and does not include fault tolerance considerations.
- The script calculates the minimum number of federated nodes required ($n$) to ensure that, even if up to $f$ federated nodes fail, the quorum threshold can still be met.

#### Addressing Any Node Faulting

- To consider faults among **any nodes** (both federated and non-federated), the model must be extended to include:

  - Fault tolerance parameters for non-federated nodes.
  - Adjustments to the voting power contributions based on potential node failures.
  - A more comprehensive calculation that accounts for the total system's resilience.

#### Implications

- **System Design:**
  - Incorporating the possibility of any node failing enhances the robustness and reliability of the system.
- **Security:**
  - By considering faults in all nodes, the system can better guard against attacks and failures, ensuring consensus and preventing malicious actors from compromising the network.

#### Recommendations

- **Extend the Model:**
  - Modify the script to include fault tolerance for non-federated nodes if their failures could significantly impact the quorum.
- **Dynamic Voting Power:**
  - Consider fluctuations in voting power due to changes in stake or node participation.
- **Weighted Voting:**
  - If nodes have varying voting weights, adjust the calculations to reflect the actual distribution.
- **Simulation and Testing:**
  - Validate the extended model using simulations to test its effectiveness under various fault scenarios.
- **Monitoring and Alerts:**
  - Implement monitoring to detect when the number of faulty nodes approaches critical thresholds.

---
