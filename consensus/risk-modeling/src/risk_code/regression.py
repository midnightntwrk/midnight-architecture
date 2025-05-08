# %%
# Let's now try to fit a curve to the selection frequency for each group size
# using a polynomial regression model.
#
# Initialize a dictionary to store the regression models for each group size
regression_models = {}

# Loop over the group sizes
for group_size in group_sizes:
    # Get the selection frequency for the given group size, replace=ing NaN values with zero
    y = np.nan_to_num(
        selection_frequencies[f"Group Size = {group_size}"].values, nan=0.0
    )

    # Get the number of participants
    x = np.arange(1, y.shape[0] + 1).reshape(-1, 1)
    # Create a polynomial regression model
    model = make_pipeline(
        SplineTransformer(n_knots=5, degree=5),
        LinearRegression(),
    )
    # Fit the model
    model.fit(x, y)
    # Store the model
    regression_models[f"Group Size = {group_size}"] = model


# %%
# Plot the regression models for each group size
# superimposed on the selection frequency plot

x = np.arange(1, 501).reshape(-1, 1)
plt.figure(figsize=(12, 8))

# Plot the actual selection frequencies
for group_size in group_sizes:

    plt.plot(
        selection_frequencies[f"Group Size = {group_size}"].values,
        marker=".",
        linestyle="-",
        label="Actual",
        alpha=0.6,
    )
    model = regression_models[f"Group Size = {group_size}"]
    y_pred = model.predict(x)
    plt.plot(x, y_pred, label="Fitted")

    plt.xlabel("Participant Number")
    plt.ylabel("Selection Frequency")
    plt.title(f"Selection Freq. Regression Function (group size {group_size})")
    plt.legend()
    plt.show()


# %%
