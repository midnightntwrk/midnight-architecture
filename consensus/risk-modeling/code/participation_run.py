# %% [markdown]
# # Participation Distribution in Committee Selection
#
# ### Executive Summary
#
# In the following computer experiments,
# we aim to understand the distribution of selections in a committee
# when varying sizes of the participant pool of SPOs and the committee.
# We show that the "pigeonhole principle" helps us interpret the results
# and understand the finite distribution of the committee seats assigned
# to participants as a function of stake, group, and committee sizes.
#
# The experiment is designed to:
# - Sample without replacement a group of participants from the population and
# - Calculate the stake weight for each participant, which is the stake normalized
#   over the group to sum to 1.
# - Assign a committee of the fixed group size based on the stake weight of each
#   using random selection with replacement.
# - Analyze the relationship and distribution of committee selection with group size.
#
# We conducted the experiments with varying sizes $(100, 200, ..., 500)$
# of groups and committees. The results are visualized through plots of committee
# assignments where we vary the group size to see how the committee selection and
# seat count changes.
#
# The results show that some group members with smaller stake weights may not (ever?)
# get selected for committee seats.
# With repeated trials where a new committee is selected, called an *epoch*,
# and assuming nonzero stake weight, there is nonzero probability of selecting *any*
# participant in the long run. However, in the short term, there is a significant chance
# that some participants will not ever get selected, almost surely.
# This is a natural outcome of the selection process
# with a discrete and finite number of seats. This is a manifestation of the
# this committee selection process as it currently stands.
#
# %%
# Load the required libraries

from participation_lib import (
    np,
    pd,
    plt,
    load_data,
    get_stake_distribution,
    assign_commitee,
    plot_group_to_committee_index,
    plot_selection_count_vs_stake,
    plot_committee_selection_counts,
    plot_committee_selection_seat_cutoff,
)
import seaborn as sns

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
    group_size=100,
    num_iter=1,
)
group_stakes

# %%
group_stakes.describe()

# %%
# Let's now assign a committee of the fixed group_size
# based on the stake weight of each

committee, seat_counts, first_zero_index = assign_commitee(
    group_stakes,
    committee_size=group_size,
    num_iter=1000,
)

# %%
print("Committee")  # Participants selected for the committee
print(committee)
print("\nSeat Counts")  # Number of times each participant is selected
print(seat_counts)
print("\nFirst Zero Index")  # Index where the seat count first goes to zero
print(first_zero_index)

# %%
# Let's now create a plots of committee assignments where we vary
# the group size over {100, 200, 300, 400, 500} and see how the
# committee selection and seat count changes.

# Initialize Parameters:
comm_sizes = [100, 200, 300, 400, 500]  # vary over committee size, k
group_sizes = [100, 200, 300, 400, 500]  # vary over group size, n
num_iter = 1000  # Number of iterations for Monte Carlo simulation
# Note that the number of iterations here can be interpreted as the number
# of selection rounds for the committee, which we call an epoch.
# If we have a new epoch per day, then 1000 iterations is about 3 years.

# Collect the selection count values
# for each group size, keyed by committee size
committee_seats = {}

# Initialize an array to store the first zero index
# for each committee size (row) and group size (columns)
first_zero_indices = np.zeros(
    (
        len(comm_sizes),
        len(group_sizes),
    )
)

# Initialize a DataFrame to store the seat count for each group size
selection_counts = {}

# %%
# Loop over the committee sizes
for i, committee_size in enumerate(comm_sizes):
    # Loop over the group sizes
    for j, group_size in enumerate(group_sizes):
        print(f"Group Size ...: {group_size} participants")
        print(f"Committee Size: {committee_size} seats")

        group_stakes = get_stake_distribution(
            population,
            group_size,
            num_iter=1,
            plot_it=False,
        )
        committee, seat_counts, first_zero_index = assign_commitee(
            group_stakes,
            committee_size=committee_size,
            num_iter=num_iter,
        )
        first_zero_indices[i][j] = first_zero_index
        selection_counts[f"Group Size = {group_size}"] = seat_counts

        plot_selection_count_vs_stake(
            group_stakes,
            committee,
            first_zero_index,
        )
    # Collect the selection frequencies in a DataFrame
    selection_counts = pd.DataFrame(selection_counts)
    committee_seats[f"Committee Size = {committee_size}"] = selection_counts

# %%
# I want to combine the selection counts for each committee size
# into a single DataFrame for easier analysis and plotting.
# Make committee size a new column in the DataFrame
committee_seats_df = pd.concat(
    committee_seats,
    axis=1,
)
committee_seats_df

# %%
# Plot the selection counts for each group size
plot_committee_selection_seat_cutoff(
    comm_sizes,
    committee_seats_df,
    first_zero_indices,
)

# The cutoff stake value is the stake weight of the participant where the
# committee seat count first goes to zero. This is the point where the
# pigeonhole principle applies, showing that some participants with smaller
# stake weights may not get selected for committee seats.
#
# This is expected due to the variation in
# stake weights. The pigeonhole principle helps us understand this
# uneven distribution of selections based on stake weights.

# %%
# Plot the selection counts for each group size with log scale
plot_committee_selection_seat_cutoff(
    comm_sizes,
    committee_seats_df,
    first_zero_indices,
    log_scale=True,
)
# With the log scale you can see that the distribution of committee seats
# is uneven, with some participants getting selected multiple times while
# others are not selected at all.
#

# %%
# committee_seats_df = committee_seats_df.swaplevel(axis=1).sort_index(axis=1)

# %%
# Finally plot a bar chart showing the percentage of group participants
# not selected for committee seats. The x-axis is the group size and the y-axis
# is the Committee Seats (relative frequency). For each group size, 100...500,
# the bars are grouped by committee size.

# Calculate the percentage of participants not selected for committee seats
not_selected_percentages = (1.0 - first_zero_indices / group_sizes) * 100

# Create a DataFrame for plotting
not_selected_df = pd.DataFrame(
    not_selected_percentages,
    index=comm_sizes,
    columns=group_sizes,
)

# %%
# Plot the line chart
not_selected_df.T.plot(kind="line", figsize=(12, 8), marker="o", colormap="viridis")
plt.title("Percentage of Group Participants Not Selected for Committee Seats")
plt.xlabel("Group Size")
plt.ylabel("Percentage Not Selected")
plt.xticks(rotation=0)
plt.legend(title="Committee Size", bbox_to_anchor=(1.05, 1), loc="upper left")
plt.grid(axis="y", linestyle="--", alpha=0.6)
plt.tight_layout()
plt.show()

# %%
# Plot the bar chart
not_selected_df.T.plot(kind="bar", figsize=(12, 8), colormap="viridis")
plt.title("Percentage of Group Participants Not Selected for Committee Seats")
plt.xlabel("Group Size")
plt.ylabel("Percentage Not Selected")
plt.xticks(rotation=0)
plt.legend(title="Committee Size", bbox_to_anchor=(1.05, 1), loc="upper left")
plt.grid(axis="y", linestyle="--", alpha=0.6)
plt.tight_layout()
plt.show()

# %%
# Create a heatmap to visualize the percentage of participants not selected
# for committee seats. This can provide a clear view of the distribution
# across different group sizes and committee sizes.

plt.figure(figsize=(12, 8))
sns.heatmap(
    not_selected_df,
    annot=True,
    fmt=".1f",
    cmap="viridis",
    cbar_kws={"label": "Percentage Not Selected"},
)
plt.title(
    "Heatmap of Percentage of Group Participants Not Selected for Committee Seats"
)
plt.xlabel("Group Size")
plt.ylabel("Committee Size")
plt.show()
# %%
