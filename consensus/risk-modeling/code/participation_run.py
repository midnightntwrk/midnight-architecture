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
    simulate,
    std_error,
    plot_group_to_committee_index,
    plot_selection_count_vs_stake,
    plot_committee_selection_counts,
    plot_committee_selection_seat_cutoff,
)

# %%
# Load the Data: The population of registered SPOs

population = load_data("../data/pooltool-cleaned.csv")

print(population.info())

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
print(group_stakes)

# %%
print(group_stakes.describe())

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
num_iter = 30  # Number of iterations for Monte Carlo simulation

# Note that the number of iterations here can be interpreted as the number
# of selection rounds for the committee, which we call an epoch.
# If we have a new epoch per day, then 1000 iterations is about 3 years.


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
# %%
# Plot the percentage of group participants excluded from a committee
# of a given size vs. different group sizes

fig, ax = plt.subplots(figsize=(12, 8))

sns.set(style="whitegrid")

for committee_size in commitee_sizes:
    committee_label = f"Committee Size = {committee_size}"
    committee_voters = sim_results_df.loc["Distinct Voters", committee_label]

    mean_values = committee_voters.loc["mean"]
    std_dev_values = committee_voters.loc["sd"]

    # Calculate the percentage of participants not selected for committee seats
    not_selected_percentages = (1.0 - mean_values / group_sizes) * 100
    not_selected_percentages.name = "Excluded (%)"

    # Create a DataFrame for easier plotting with seaborn
    plot_data = pd.DataFrame(
        {
            "Group Size": group_sizes,
            "Percentage Excluded": not_selected_percentages,
            "Std Dev": std_dev_values,
        }
    )

    # Plot the main line without error bars
    sns.lineplot(
        x="Group Size",
        y="Percentage Excluded",
        data=plot_data,
        marker="o",
        label=committee_label,
        ax=ax,
    )

ax.set_ylabel("Percentage Excluded")
ax.set_xlabel("Group Size")
ax.legend(title="Committee Size")
plt.title("Percentage of Group Participants Not Selected for Committee Seats")
plt.grid(True)
plt.show()

# %%
sim_results_df.loc["Distinct Voters", :]

# %%
# Plot the committee selection counts distribution
fig = plt.figure(figsize=(12, 8))

plot_data = sim_results_df.loc["Committee Seats"].loc["mean"]

for c, g in plot_data.index:

    y = plot_data.loc[(c, g)]
    x = y.index

    n_c = int(c.split("=")[1].strip())
    n_g = int(g.split("=")[1].strip())

    colors = sns.color_palette("tab20", len(plot_data.index))
    color_idx = list(plot_data.index).index((c, g))
    plt.bar(x, y, alpha=0.7, color=colors[color_idx], label=f"{n_c}, {n_g}")

plt.xlabel("Participant Index")
plt.ylabel("Committee Seat Count (average)")
plt.title("Committee Seat Count for Participants")
plt.legend(title="Committee Size, Group Size")
plt.xlim(0, 200)
plt.show()

# %%
# Distinct Voters
committee_voters = sim_results_df.loc["Distinct Voters"]

# Create a DataFrame row from the computed percentages
mean_values = committee_voters.loc["mean"]
std_dev_values = committee_voters.loc["sd"]

# Calculate the percentage of participants not selected for committee seats
print("Percentage of Group Participants Not Selected for Committee Seats:")
committee_participation = pd.concat([mean_values, std_dev_values], axis=1)
# committee_participation.columns = ["Mean", "Std Dev"]

print(committee_participation)

# %%
# Prepare the DataFrame for concatenation with the other simulation results
committee_participation = committee_participation.T
committee_participation.index = pd.MultiIndex.from_tuples(
    [("Committee Participation %", "mean"), ("Committee Participation %", "sd")]
)

# Concatenate this new row to the simulation results DataFrame
sim_results_df = pd.concat([sim_results_df, committee_participation], axis=0)

sim_results_df
# %%
# Save the results to an Excel file
output_file = "../data/participation_run_results.xlsx"
sim_results_df.to_excel(output_file)
print(f"Results saved to {output_file}")

# %%
