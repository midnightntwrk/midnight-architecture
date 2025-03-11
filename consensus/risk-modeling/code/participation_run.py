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

num_reps = 30  # is the number of repetitions for each group size
# used to average the number of distinct voters over the iterations

# Collect the selection count values
# for each group size, keyed by committee size
committee_seats = {}
distinct_voters = {}

# Initialize an array to store the first zero index
# for each committee size (row) and group size (columns)
first_zero_indices = np.zeros(
    (
        len(comm_sizes),
        len(group_sizes),
    )
)

# %%
# Loop over the committee sizes
for i, committee_size in enumerate(comm_sizes):
    # Loop over the group sizes
    selection_counts = {}
    distinct_voters_avg = {}
    distinct_voters_std = {}
    distinct_voters_lst = []  # for the given committee size

    for j, group_size in enumerate(group_sizes):

        group_label = f"Group Size = {group_size}"
        comm_label = f"Committee Size = {committee_size}"

        print(f"{group_label} participants")
        print(f"{comm_label} seats")

        distinct_voters_list = []

        # Average the number of distinct voters over the iterations
        for _ in range(num_reps):
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
                plot_it=False,
            )

            # Store the last seat counts for each group size
            selection_counts[group_label] = seat_counts

            # Count the number of distinct voters
            distinct_voters_lst.append(len(committee.index.unique()))

        # Average the number of distinct voters over the iterations
        distinct_voters_avg[group_label] = np.mean(distinct_voters_lst)

        # Standard deviation of the number of distinct voters
        distinct_voters_std[group_label] = np.std(distinct_voters_lst)

        plot_selection_count_vs_stake(
            group_stakes,
            committee,
            first_zero_index,
        )

        # Store the last first zero index
        first_zero_indices[i][j] = first_zero_index

    # Collect the selection frequencies in a DataFrame
    committee_seats[comm_label] = pd.DataFrame(selection_counts)
    distinct_voters[comm_label] = pd.DataFrame(
        [distinct_voters_avg, distinct_voters_std],
        index=["Mean", "Std Dev"],
    )

# %%
# Combine the selection counts for each committee size
# into a single DataFrame for easier analysis and plotting.

distinct_voters_df = pd.concat(distinct_voters, axis=1)
committee_seats_df = pd.concat(
    committee_seats,
    axis=1,
)
sim_results_df = pd.concat(
    [distinct_voters_df, committee_seats_df],
    keys=["Distinct Voters", "Committee Seats"],
)
sim_results_df

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
# Extract the data for plotting
committee_size = 300

df = distinct_voters_df[f"Committee Size = {committee_size}"]
group_sizes = [int(col.split("=")[1].strip()) for col in df.columns]
mean_values = df.loc["Mean"].values
std_dev_values = df.loc["Std Dev"].values

# Calculate the percentage of participants not selected for committee seats
not_selected_percentages = 100 * (1 - mean_values / group_sizes)

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

plot_data

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
