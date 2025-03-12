# %% [markdown]
# # Participation Distribution in Committee Selection
#
# ### Executive Summary
#
# In the following computer experiments, we aim to understand the
# distribution of selections in a committee when varying sizes of the
# participant pool of SPOs and the committee. We show that the
# "pigeonhole principle" helps us interpret the results and understand
# the finite distribution of the committee seats assigned to participants
# as a function of stake, group, and committee sizes.
#
# The experiment is designed to:
# - Sample without replacement a group of participants from the population
#   and
# - Calculate the stake weight for each participant, which is the stake
#   normalized over the group to sum to 1.
# - Assign a committee of the fixed group size based on the stake weight
#   of each using random selection with replacement.
# - Analyze the relationship and distribution of committee selection with
#   group size.
#
# We conducted the experiments with varying sizes (100, 200, ..., 500) of
# groups and committees. The results are visualized through plots of
# committee assignments where we vary the group size to see how the
# committee selection and seat count changes.
#
# The results show that some group members with smaller stake weights may
# not (ever?) get selected for committee seats. With repeated trials where
# a new committee is selected, called an *epoch*, and assuming nonzero
# stake weight, there is nonzero probability of selecting *any* participant
# in the long run. However, in the short term, there is a significant chance
# that some participants will not ever get selected, almost surely. This is
# a natural outcome of the selection process with a discrete and finite
# number of seats. This is a manifestation of this committee selection
# process as it currently stands.
#
# %%
# Load the required libraries

from participation_lib import (
    np,
    pd,
    plt,
    sns,
    load_data,
    get_stake_distribution,
    assign_commitee_plus,
    # simulate,
    plot_group_to_committee_index,
    plot_selection_count_vs_stake,
    plot_committee_selection_counts,
    plot_committee_selection_seat_cutoff,
)

# %%
# Load the Data: The population of registered SPOs

population = load_data("../data/pooltool-cleaned.csv")
population.info()

# %%
population.describe()

# %%
# Let's now sample a group of participants from the population
# and calculate the stake weight for each participant.

group_size = 100

group_stakes = get_stake_distribution(
    population,
    group_size=group_size,
    num_iter=1000,
    plot_it=True,
)
group_stakes

# %%
group_stakes.describe()

# %%
# Let's now assign a committee of the fixed group_size
# based on the stake weight of each

results = assign_commitee_plus(
    group_stakes,
    committee_size=group_size,
    num_iter=1000,
)

# %%
# Let's now create a plots of committee assignments where we vary
# the group size over {100, 200, 300, 400, 500} and see how the
# committee selection and seat count changes.

# Initialize Parameters:
# comm_sizes = [100]  # vary over committee size, k
# group_sizes = [100]  # vary over group size, n
comm_sizes = [100, 200, 300, 400, 500]  # vary over committee size, k
group_sizes = [100, 200, 300, 400, 500]  # vary over group size, n
num_iter = 1000  # Number of iterations for Monte Carlo simulation

# Note that the number of iterations here can be interpreted as the number
# of selection rounds for the committee, which we call an epoch.
# If we have a new epoch per day, then 1000 iterations is about 3 years.


# %%
def simulate(
    population: pd.DataFrame,
    comm_sizes: list,
    group_sizes: list,
    num_iter: int,
    plot_it: bool = False,
) -> pd.DataFrame:
    """Simulate the committee selection process for varying group sizes
    and committee sizes and return the results in a DataFrame.

    Args:
    - population: DataFrame containing the population of SPOs.
    - comm_sizes: list of committee sizes to simulate.
    - group_sizes: list of group sizes to simulate.
    - num_iter: int number of iterations for the Monte Carlo simulation.
    - plot_it: bool flag to plot the results. Default is False.

    Returns:
    - results_df: DataFrame containing the results of the simulation.

    """
    # Dictionary to hold simulation data for each (committee_size, group_size) pair.
    # For each pair, we compute a DataFrame of metrics (rows: e.g. "Distinct Voters",
    # "Committee Seats") with columns "mean" and "sd". Later we stack these so that
    # the row index becomes a MultiIndex (metric, statistic) and the DataFrame columns
    # become a MultiIndex over (committee_size, group_size).
    sim_dict = {}

    for comm_size in comm_sizes:
        print(f"\nCommittee Size = {comm_size}")

        for group_size in group_sizes:
            print(f"Group Size = {group_size}")

            group_stakes = get_stake_distribution(
                population,
                group_size=group_size,
                num_iter=num_iter,
                # plot_it=plot_it,  # Turn off
            )

            committee_results = assign_commitee_plus(
                group_stakes,
                committee_size=comm_size,
                num_iter=num_iter,
                plot_it=plot_it,
            )
            # Extract distinct voters metrics from the tuple
            distinct_voters_avg, distinct_voters_std = committee_results[
                "distinct_voters"
            ]

            # Compute statistics for committee seat counts
            seat_counts = np.array(committee_results["seat_counts"])
            committee_seat_mean = seat_counts.mean()
            committee_seat_std = seat_counts.std()

            # Build the metrics dictionaries for DataFrame construction
            mean_stats = {
                "Distinct Voters": distinct_voters_avg,
                "Committee Seats": committee_seat_mean,
            }
            sd_stats = {
                "Distinct Voters": distinct_voters_std,
                "Committee Seats": committee_seat_std,
            }

            # Create a DataFrame with columns for mean and std dev
            tmp_df = pd.DataFrame({"mean": mean_stats, "sd": sd_stats})
            # Stack to get a Series with MultiIndex (metric, statistic)
            sim_dict[(comm_size, group_size)] = tmp_df.stack()

    # Convert the dictionary into a DataFrame.
    sim_results_df = pd.DataFrame(sim_dict)

    # Create MultiIndex column labels in the desired string format.
    sim_results_df.columns = pd.MultiIndex.from_tuples(
        [
            (f"Committee Size = {cs}", f"Group Size = {gs}")
            for cs, gs in sim_results_df.columns
        ],
        names=["Committee Size", "Group Size"],
    )

    return sim_results_df


# %%
# Call the function
sim_results_df = simulate(
    population,
    comm_sizes,
    group_sizes,
    num_iter,
    plot_it=True,
)

# %%
# committee_seats_df = committee_seats_df.swaplevel(axis=1).sort_index(axis=1)

# %%
# Extract the data for plotting

col_index = sim_results_df.columns
commitee_sizes = [
    int(col.split("=")[1].strip()) for col in col_index.get_level_values(0).unique()
]
group_sizes = [
    int(col.split("=")[1].strip()) for col in col_index.get_level_values(1).unique()
]

# Examine the data for committee size = 100
committee_size = 100

committee_label = f"Committee Size = {committee_size}"
committee_voters = sim_results_df.loc["Distinct Voters", committee_label]
committee_seats = sim_results_df.loc["Committee Seats", committee_label]

# %%
# Distinct Voters
print(f"Number of distinct voters for {committee_label}:")
mean_values = committee_voters.loc["mean"]
std_dev_values = committee_voters.loc["sd"]

# Calculate the percentage of participants not selected for committee seats
not_selected_percentages = (1.0 - mean_values / group_sizes) * 100
not_selected_percentages.name = "Excluded (%)"

print(pd.concat([mean_values, std_dev_values, not_selected_percentages], axis=1))

# %%

# Create a DataFrame for easier plotting with seaborn
plot_data = pd.DataFrame(
    {
        "Group Size": group_sizes,
        "Percentage Excluded": not_selected_percentages,
        "Std Dev": std_dev_values,
    }
)
print(
    "Percentage of Group Participants Not Selected"
    f" for Committee Seats, k = {committee_size}:"
)

print(plot_data)

# %%
# Create upper and lower bounds for the error bands

def std_error(data, **kwargs):
    """Function that returns lower and upper error bounds"""
    return (
        data["Percentage Excluded"] - data["Std Dev"],
        data["Percentage Excluded"] + data["Std Dev"],
    )

# %%
# Plot the data with seaborn
plt.figure(figsize=(12, 8))
sns.set(style="whitegrid")

# Plot the main line without error bars
sns.lineplot(
    x="Group Size",
    y="Percentage Excluded",
    data=plot_data,
    errorbar=std_error,
    err_style="band",
    marker="o",
    color="b",
    label="Percentage Excluded",
)
# Add error bands using plt.errorbar
plt.errorbar(
    plot_data["Group Size"],
    plot_data["Percentage Excluded"],
    yerr=plot_data["Std Dev"],
    fmt="none",  # No connecting line
    ecolor="r",
    capsize=5,
    alpha=0.6,
    label="Error (±1 std dev)"
)
plt.xlabel("Group Size")
plt.ylabel("Percentage Excluded")
plt.title("Percentage of Group Participants Not Selected for Committee Seats"
          f"\n(Committee Seats k = {committee_size})")
plt.legend()
plt.grid(True)
plt.show()

# %%
