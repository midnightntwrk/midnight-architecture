 # Participation Distribution in Committee Selection

 ### Executive Summary

 In the following computer experiments, we aim to understand the
 distribution of selections in a committee when varying sizes of the
 participant pool of SPOs and the committee. We show that the
 "pigeonhole principle" helps us interpret the results and understand
 the finite distribution of the committee seats assigned to participants
 as a function of stake, group, and committee sizes.

 The experiment is designed to:
 - Sample without replacement a group of participants from the population
   and
 - Calculate the stake weight for each participant, which is the stake
   normalized over the group to sum to 1.
 - Assign a committee of the fixed group size based on the stake weight
   of each using random selection with replacement.
 - Analyze the relationship and distribution of committee selection with
   group size.

 We conducted the experiments with varying sizes (100, 200, ..., 500) of
 groups and committees. The results are visualized through plots of
 committee assignments where we vary the group size to see how the
 committee selection and seat count changes.

 The results show that some group members with smaller stake weights may
 not (ever?) get selected for committee seats. With repeated trials where
 a new committee is selected, called an *epoch*, and assuming nonzero
 stake weight, there is nonzero probability of selecting *any* participant
 in the long run. However, in the short term, there is a significant chance
 that some participants will not ever get selected, almost surely. This is
 a natural outcome of the selection process with a discrete and finite
 number of seats. This is a manifestation of this committee selection
 process as it currently stands.



```python
# %%

# Load the required libraries

from participation_lib import (
    np,
    pd,
    plt,
    sns,
    load_data,
    get_stake_distribution,
    assign_commitee,
    simulate,
    std_error,
    plot_group_to_committee_index,
    plot_selection_count_vs_stake,
    plot_committee_selection_counts,
    plot_committee_selection_seat_cutoff,
    plot_participation,
)
```


```python
# %%

# Load the Data: The population of registered SPOs

population = load_data("../data/pooltool-cleaned.csv")

print(population.info())
```

    <class 'pandas.core.frame.DataFrame'>
    RangeIndex: 3056 entries, 0 to 3055
    Data columns (total 3 columns):
     #   Column         Non-Null Count  Dtype  
    ---  ------         --------------  -----  
     0   id             3056 non-null   object 
     1   stake          3056 non-null   int64  
     2   stake_percent  3056 non-null   float64
    dtypes: float64(1), int64(1), object(1)
    memory usage: 71.8+ KB
    None



```python
# %%

population.describe()
```




<div>
<style scoped>
    .dataframe tbody tr th:only-of-type {
        vertical-align: middle;
    }

    .dataframe tbody tr th {
        vertical-align: top;
    }

    .dataframe thead th {
        text-align: right;
    }
</style>
<table border="1" class="dataframe">
  <thead>
    <tr style="text-align: right;">
      <th></th>
      <th>stake</th>
      <th>stake_percent</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <th>count</th>
      <td>3.056000e+03</td>
      <td>3056.000000</td>
    </tr>
    <tr>
      <th>mean</th>
      <td>7.305314e+06</td>
      <td>0.032723</td>
    </tr>
    <tr>
      <th>std</th>
      <td>1.648449e+07</td>
      <td>0.073839</td>
    </tr>
    <tr>
      <th>min</th>
      <td>0.000000e+00</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>25%</th>
      <td>5.265000e+02</td>
      <td>0.000002</td>
    </tr>
    <tr>
      <th>50%</th>
      <td>5.692500e+04</td>
      <td>0.000255</td>
    </tr>
    <tr>
      <th>75%</th>
      <td>3.282500e+06</td>
      <td>0.014703</td>
    </tr>
    <tr>
      <th>max</th>
      <td>1.054300e+08</td>
      <td>0.472250</td>
    </tr>
  </tbody>
</table>
</div>




```python
# %%

# Let's now sample a group of participants from the population
# and calculate the stake weight for each participant.

group_size = 100

group_stakes = get_stake_distribution(
    population,
    group_size=group_size,
    num_iter=100,
    plot_it=True,
)
print(group_stakes)
```


    
![png](output_4_0.png)
    


              stake  stake_weight
    0   71397500.00  8.753869e-02
    1   67897900.00  8.324792e-02
    2   64359600.00  7.890970e-02
    3   60630500.00  7.433754e-02
    4   55516400.00  6.806727e-02
    ..          ...           ...
    95        17.54  2.150536e-08
    96        10.50  1.287379e-08
    97         5.98  7.331929e-09
    98         3.50  4.291263e-09
    99         1.75  2.145631e-09
    
    [100 rows x 2 columns]



```python
# %%

print(group_stakes.describe())
```

                  stake  stake_weight
    count  1.000000e+02  1.000000e+02
    mean   8.156108e+06  1.000000e-02
    std    1.687489e+07  2.068988e-02
    min    1.750000e+00  2.145631e-09
    25%    1.981992e+03  2.430072e-06
    50%    1.456142e+05  1.785339e-04
    75%    5.105425e+06  6.259634e-03
    max    7.139750e+07  8.753869e-02



```python
# %%

# Let's now assign a committee of the fixed group_size
# based on the stake weight of each

results = assign_commitee(
    group_stakes,
    committee_size=group_size,
    num_iter=1,
    plot_it=True,
)
```


    
![png](output_6_0.png)
    



```python
# %%

# Let's now create a plots of committee assignments where we vary
# the group size over {100, 200, 300, 400, 500} and see how the
# committee selection and seat count changes.

# Initialize Parameters:
# comm_sizes = [100]  # vary over committee size, k
# group_sizes = [100]  # vary over group size, n
comm_sizes = range(200, 501, 100)  # vary over committee size, k
group_sizes = range(200, 501, 100)  # vary over group size, n
num_iter = 1  # Number of iterations for Monte Carlo simulation

# Note that the number of iterations here can be interpreted as the number
# of selection rounds for the committee, which we call an epoch.
# If we have a new epoch per day, then 1000 iterations is about 3 years.
```


```python
# %%

# Call the function
sim_results_df = simulate(
    population,
    comm_sizes,
    group_sizes,
    num_iter,
    plot_it=True,
)
```

    
    Committee Size = 200
    Group Size = 200



    
![png](output_8_1.png)
    


    Group Size = 300



    
![png](output_8_3.png)
    


    Group Size = 400



    
![png](output_8_5.png)
    


    Group Size = 500



    
![png](output_8_7.png)
    


    
    Committee Size = 300
    Group Size = 200



    
![png](output_8_9.png)
    


    Group Size = 300



    
![png](output_8_11.png)
    


    Group Size = 400



    
![png](output_8_13.png)
    


    Group Size = 500



    
![png](output_8_15.png)
    


    
    Committee Size = 400
    Group Size = 200



    
![png](output_8_17.png)
    


    Group Size = 300



    
![png](output_8_19.png)
    


    Group Size = 400



    
![png](output_8_21.png)
    


    Group Size = 500



    
![png](output_8_23.png)
    


    
    Committee Size = 500
    Group Size = 200



    
![png](output_8_25.png)
    


    Group Size = 300



    
![png](output_8_27.png)
    


    Group Size = 400



    
![png](output_8_29.png)
    


    Group Size = 500



    
![png](output_8_31.png)
    



```python
# %%

# Extract the data for plotting

col_index = sim_results_df.columns
commitee_sizes = [
    int(col.split("=")[1].strip()) for col in col_index.get_level_values(0).unique()
]
group_sizes = [
    int(col.split("=")[1].strip()) for col in col_index.get_level_values(1).unique()
]

# Plot the percentage of group participants not selected for committee seats
plot_participation(sim_results_df, commitee_sizes, group_sizes, num_iter)
```


    
![png](output_9_0.png)
    



```python
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
```


    
![png](output_10_0.png)
    



```python
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
```

    Percentage of Group Participants Not Selected for Committee Seats:
                                            mean   sd
    Committee Size       Group Size                  
    Committee Size = 200 Group Size = 200   52.0  0.0
                         Group Size = 300   64.0  0.0
                         Group Size = 400   80.0  0.0
                         Group Size = 500   92.0  0.0
    Committee Size = 300 Group Size = 200   57.0  0.0
                         Group Size = 300   75.0  0.0
                         Group Size = 400   84.0  0.0
                         Group Size = 500   99.0  0.0
    Committee Size = 400 Group Size = 200   58.0  0.0
                         Group Size = 300   76.0  0.0
                         Group Size = 400  103.0  0.0
                         Group Size = 500  121.0  0.0
    Committee Size = 500 Group Size = 200   65.0  0.0
                         Group Size = 300   81.0  0.0
                         Group Size = 400  101.0  0.0
                         Group Size = 500  127.0  0.0



```python
# %%

# Let's now create a plots of committee assignments where we vary
# the group size over {100, 200, 300, 400, 500} and see how the
# committee selection and seat count changes.

# Initialize Parameters:
# comm_sizes = [100]  # vary over committee size, k
# group_sizes = [100]  # vary over group size, n
comm_sizes = range(100, 1201, 100)  # vary over committee size, k
group_sizes = range(100, 1201, 100)  # vary over group size, n
num_iter = 100  # Number of iterations for Monte Carlo simulation

# Note that the number of iterations here can be interpreted as the number
# of selection rounds for the committee, which we call an epoch.
# If we have a new epoch per day, then 1000 iterations is about 3 years.
```


```python
# %%

# Call the function
sim_results_df = simulate(
    population,
    comm_sizes,
    group_sizes,
    num_iter,
    plot_it=True,
)
```

    
    Committee Size = 100
    Group Size = 100



    
![png](output_13_1.png)
    


    Group Size = 200



    
![png](output_13_3.png)
    


    Group Size = 300



    
![png](output_13_5.png)
    


    Group Size = 400



    
![png](output_13_7.png)
    


    Group Size = 500



    
![png](output_13_9.png)
    


    Group Size = 600



    
![png](output_13_11.png)
    


    Group Size = 700



    
![png](output_13_13.png)
    


    Group Size = 800



    
![png](output_13_15.png)
    


    Group Size = 900



    
![png](output_13_17.png)
    


    Group Size = 1000



    
![png](output_13_19.png)
    


    Group Size = 1100



    
![png](output_13_21.png)
    


    Group Size = 1200



    
![png](output_13_23.png)
    


    
    Committee Size = 200
    Group Size = 100



    
![png](output_13_25.png)
    


    Group Size = 200



    
![png](output_13_27.png)
    


    Group Size = 300



    
![png](output_13_29.png)
    


    Group Size = 400



    
![png](output_13_31.png)
    


    Group Size = 500



    
![png](output_13_33.png)
    


    Group Size = 600



    
![png](output_13_35.png)
    


    Group Size = 700



    
![png](output_13_37.png)
    


    Group Size = 800



    
![png](output_13_39.png)
    


    Group Size = 900



    
![png](output_13_41.png)
    


    Group Size = 1000



    
![png](output_13_43.png)
    


    Group Size = 1100



    
![png](output_13_45.png)
    


    Group Size = 1200



    
![png](output_13_47.png)
    


    
    Committee Size = 300
    Group Size = 100



    
![png](output_13_49.png)
    


    Group Size = 200



    
![png](output_13_51.png)
    


    Group Size = 300



    
![png](output_13_53.png)
    


    Group Size = 400



    
![png](output_13_55.png)
    


    Group Size = 500



    
![png](output_13_57.png)
    


    Group Size = 600



    
![png](output_13_59.png)
    


    Group Size = 700



    
![png](output_13_61.png)
    


    Group Size = 800



    
![png](output_13_63.png)
    


    Group Size = 900



    
![png](output_13_65.png)
    


    Group Size = 1000



    
![png](output_13_67.png)
    


    Group Size = 1100



    
![png](output_13_69.png)
    


    Group Size = 1200



    
![png](output_13_71.png)
    


    
    Committee Size = 400
    Group Size = 100



    
![png](output_13_73.png)
    


    Group Size = 200



    
![png](output_13_75.png)
    


    Group Size = 300



    
![png](output_13_77.png)
    


    Group Size = 400



    
![png](output_13_79.png)
    


    Group Size = 500



    
![png](output_13_81.png)
    


    Group Size = 600



    
![png](output_13_83.png)
    


    Group Size = 700



    
![png](output_13_85.png)
    


    Group Size = 800



    
![png](output_13_87.png)
    


    Group Size = 900



    
![png](output_13_89.png)
    


    Group Size = 1000



    
![png](output_13_91.png)
    


    Group Size = 1100



    
![png](output_13_93.png)
    


    Group Size = 1200



    
![png](output_13_95.png)
    


    
    Committee Size = 500
    Group Size = 100



    
![png](output_13_97.png)
    


    Group Size = 200



    
![png](output_13_99.png)
    


    Group Size = 300



    
![png](output_13_101.png)
    


    Group Size = 400



    
![png](output_13_103.png)
    


    Group Size = 500



    
![png](output_13_105.png)
    


    Group Size = 600



    
![png](output_13_107.png)
    


    Group Size = 700



    
![png](output_13_109.png)
    


    Group Size = 800



    
![png](output_13_111.png)
    


    Group Size = 900



    
![png](output_13_113.png)
    


    Group Size = 1000



    
![png](output_13_115.png)
    


    Group Size = 1100



    
![png](output_13_117.png)
    


    Group Size = 1200



    
![png](output_13_119.png)
    


    
    Committee Size = 600
    Group Size = 100



    
![png](output_13_121.png)
    


    Group Size = 200



    
![png](output_13_123.png)
    


    Group Size = 300



    
![png](output_13_125.png)
    


    Group Size = 400



    
![png](output_13_127.png)
    


    Group Size = 500



    
![png](output_13_129.png)
    


    Group Size = 600



    
![png](output_13_131.png)
    


    Group Size = 700



    
![png](output_13_133.png)
    


    Group Size = 800



    
![png](output_13_135.png)
    


    Group Size = 900



    
![png](output_13_137.png)
    


    Group Size = 1000



    
![png](output_13_139.png)
    


    Group Size = 1100



    
![png](output_13_141.png)
    


    Group Size = 1200



    
![png](output_13_143.png)
    


    
    Committee Size = 700
    Group Size = 100



    
![png](output_13_145.png)
    


    Group Size = 200



    
![png](output_13_147.png)
    


    Group Size = 300



    
![png](output_13_149.png)
    


    Group Size = 400



    
![png](output_13_151.png)
    


    Group Size = 500



    
![png](output_13_153.png)
    


    Group Size = 600



    
![png](output_13_155.png)
    


    Group Size = 700



    
![png](output_13_157.png)
    


    Group Size = 800



    
![png](output_13_159.png)
    


    Group Size = 900



    
![png](output_13_161.png)
    


    Group Size = 1000



    
![png](output_13_163.png)
    


    Group Size = 1100



    
![png](output_13_165.png)
    


    Group Size = 1200



    
![png](output_13_167.png)
    


    
    Committee Size = 800
    Group Size = 100



    
![png](output_13_169.png)
    


    Group Size = 200



    
![png](output_13_171.png)
    


    Group Size = 300



    
![png](output_13_173.png)
    


    Group Size = 400



    
![png](output_13_175.png)
    


    Group Size = 500



    
![png](output_13_177.png)
    


    Group Size = 600



    
![png](output_13_179.png)
    


    Group Size = 700



    
![png](output_13_181.png)
    


    Group Size = 800



    
![png](output_13_183.png)
    


    Group Size = 900



    
![png](output_13_185.png)
    


    Group Size = 1000



    
![png](output_13_187.png)
    


    Group Size = 1100



    
![png](output_13_189.png)
    


    Group Size = 1200



    
![png](output_13_191.png)
    


    
    Committee Size = 900
    Group Size = 100



    
![png](output_13_193.png)
    


    Group Size = 200



    
![png](output_13_195.png)
    


    Group Size = 300



    
![png](output_13_197.png)
    


    Group Size = 400



    
![png](output_13_199.png)
    


    Group Size = 500



    
![png](output_13_201.png)
    


    Group Size = 600



    
![png](output_13_203.png)
    


    Group Size = 700



    
![png](output_13_205.png)
    


    Group Size = 800



    
![png](output_13_207.png)
    


    Group Size = 900



    
![png](output_13_209.png)
    


    Group Size = 1000



    
![png](output_13_211.png)
    


    Group Size = 1100



    
![png](output_13_213.png)
    


    Group Size = 1200



    
![png](output_13_215.png)
    


    
    Committee Size = 1000
    Group Size = 100



    
![png](output_13_217.png)
    


    Group Size = 200



    
![png](output_13_219.png)
    


    Group Size = 300



    
![png](output_13_221.png)
    


    Group Size = 400



    
![png](output_13_223.png)
    


    Group Size = 500



    
![png](output_13_225.png)
    


    Group Size = 600



    
![png](output_13_227.png)
    


    Group Size = 700



    
![png](output_13_229.png)
    


    Group Size = 800



    
![png](output_13_231.png)
    


    Group Size = 900



    
![png](output_13_233.png)
    


    Group Size = 1000



    
![png](output_13_235.png)
    


    Group Size = 1100



    
![png](output_13_237.png)
    


    Group Size = 1200



    
![png](output_13_239.png)
    


    
    Committee Size = 1100
    Group Size = 100



    
![png](output_13_241.png)
    


    Group Size = 200



    
![png](output_13_243.png)
    


    Group Size = 300



    
![png](output_13_245.png)
    


    Group Size = 400



    
![png](output_13_247.png)
    


    Group Size = 500



    
![png](output_13_249.png)
    


    Group Size = 600



    
![png](output_13_251.png)
    


    Group Size = 700



    
![png](output_13_253.png)
    


    Group Size = 800



    
![png](output_13_255.png)
    


    Group Size = 900



    
![png](output_13_257.png)
    


    Group Size = 1000



    
![png](output_13_259.png)
    


    Group Size = 1100



    
![png](output_13_261.png)
    


    Group Size = 1200



    
![png](output_13_263.png)
    


    
    Committee Size = 1200
    Group Size = 100



    
![png](output_13_265.png)
    


    Group Size = 200



    
![png](output_13_267.png)
    


    Group Size = 300



    
![png](output_13_269.png)
    


    Group Size = 400



    
![png](output_13_271.png)
    


    Group Size = 500



    
![png](output_13_273.png)
    


    Group Size = 600



    
![png](output_13_275.png)
    


    Group Size = 700



    
![png](output_13_277.png)
    


    Group Size = 800



    
![png](output_13_279.png)
    


    Group Size = 900



    
![png](output_13_281.png)
    


    Group Size = 1000



    
![png](output_13_283.png)
    


    Group Size = 1100



    
![png](output_13_285.png)
    


    Group Size = 1200



    
![png](output_13_287.png)
    



```python
# %%

# Extract the data for plotting

col_index = sim_results_df.columns
commitee_sizes = [
    int(col.split("=")[1].strip()) for col in col_index.get_level_values(0).unique()
]
group_sizes = [
    int(col.split("=")[1].strip()) for col in col_index.get_level_values(1).unique()
]

# Plot the percentage of group participants not selected for committee seats
plot_participation(sim_results_df, commitee_sizes, group_sizes, num_iter)
```


    
![png](output_14_0.png)
    



```python
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
```

    /usr/local/lib/python3.11/site-packages/IPython/core/pylabtools.py:170: UserWarning: Creating legend with loc="best" can be slow with large amounts of data.
      fig.canvas.print_figure(bytes_io, **kw)



    
![png](output_15_1.png)
    



```python
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
```

    Percentage of Group Participants Not Selected for Committee Seats:
                                               mean        sd
    Committee Size        Group Size                         
    Committee Size = 100  Group Size = 100    25.91  2.025315
                          Group Size = 200    40.26   2.55194
                          Group Size = 300    50.18  3.191802
                          Group Size = 400    57.87  3.306524
                          Group Size = 500    62.37  3.110161
    ...                                         ...       ...
    Committee Size = 1200 Group Size = 800   223.17  5.921241
                          Group Size = 900   244.46   6.25527
                          Group Size = 1000  261.56  5.846914
                          Group Size = 1100  279.83  6.926839
                          Group Size = 1200   298.7  7.054786
    
    [144 rows x 2 columns]



```python
# %%

# Prepare the DataFrame for concatenation with the other simulation results
committee_participation = committee_participation.T
committee_participation.index = pd.MultiIndex.from_tuples(
    [("Committee Participation %", "mean"), ("Committee Participation %", "sd")]
)

# Concatenate this new row to the simulation results DataFrame
sim_results_df = pd.concat([sim_results_df, committee_participation], axis=0)

sim_results_df
```




<div>
<style scoped>
    .dataframe tbody tr th:only-of-type {
        vertical-align: middle;
    }

    .dataframe tbody tr th {
        vertical-align: top;
    }

    .dataframe thead tr th {
        text-align: left;
    }
</style>
<table border="1" class="dataframe">
  <thead>
    <tr>
      <th></th>
      <th>Committee Size</th>
      <th colspan="10" halign="left">Committee Size = 100</th>
      <th>...</th>
      <th colspan="10" halign="left">Committee Size = 1200</th>
    </tr>
    <tr>
      <th></th>
      <th>Group Size</th>
      <th>Group Size = 100</th>
      <th>Group Size = 200</th>
      <th>Group Size = 300</th>
      <th>Group Size = 400</th>
      <th>Group Size = 500</th>
      <th>Group Size = 600</th>
      <th>Group Size = 700</th>
      <th>Group Size = 800</th>
      <th>Group Size = 900</th>
      <th>Group Size = 1000</th>
      <th>...</th>
      <th>Group Size = 300</th>
      <th>Group Size = 400</th>
      <th>Group Size = 500</th>
      <th>Group Size = 600</th>
      <th>Group Size = 700</th>
      <th>Group Size = 800</th>
      <th>Group Size = 900</th>
      <th>Group Size = 1000</th>
      <th>Group Size = 1100</th>
      <th>Group Size = 1200</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <th rowspan="2" valign="top">Distinct Voters</th>
      <th>mean</th>
      <td>25.91</td>
      <td>40.26</td>
      <td>50.18</td>
      <td>57.87</td>
      <td>62.37</td>
      <td>67.58</td>
      <td>70.66</td>
      <td>73.86</td>
      <td>75.84</td>
      <td>77.15</td>
      <td>...</td>
      <td>106.02</td>
      <td>131.7</td>
      <td>156.54</td>
      <td>179.34</td>
      <td>201.49</td>
      <td>223.17</td>
      <td>244.46</td>
      <td>261.56</td>
      <td>279.83</td>
      <td>298.7</td>
    </tr>
    <tr>
      <th>sd</th>
      <td>2.025315</td>
      <td>2.55194</td>
      <td>3.191802</td>
      <td>3.306524</td>
      <td>3.110161</td>
      <td>3.672002</td>
      <td>3.663932</td>
      <td>3.487177</td>
      <td>3.801894</td>
      <td>3.235352</td>
      <td>...</td>
      <td>4.14</td>
      <td>4.670118</td>
      <td>5.485289</td>
      <td>5.680176</td>
      <td>5.356295</td>
      <td>5.921241</td>
      <td>6.25527</td>
      <td>5.846914</td>
      <td>6.926839</td>
      <td>7.054786</td>
    </tr>
    <tr>
      <th>Committee Seats</th>
      <th>mean</th>
      <td>0     9.41
1     9.02
2     7.95
3     7.48
4 ...</td>
      <td>0      4.96
1      4.66
2      4.39
3      4.6...</td>
      <td>0      3.52
1      3.26
2      2.93
3      2.8...</td>
      <td>0      2.38
1      2.25
2      2.13
3      2.2...</td>
      <td>0      1.99
1      1.92
2      2.09
3      1.7...</td>
      <td>0      1.61
1      1.70
2      1.44
3      1.7...</td>
      <td>0      1.52
1      1.54
2      1.34
3      1.2...</td>
      <td>0      1.09
1      1.12
2      1.17
3      1.1...</td>
      <td>0      1.02
1      1.10
2      0.94
3      1.0...</td>
      <td>0      1.14
1      0.77
2      0.93
3      1.0...</td>
      <td>...</td>
      <td>0      40.01
1      37.14
2      35.08
3      ...</td>
      <td>0      30.26
1      28.63
2      27.42
3      ...</td>
      <td>0      24.62
1      21.44
2      22.21
3      ...</td>
      <td>0      20.25
1      19.13
2      18.96
3      ...</td>
      <td>0      18.26
1      16.15
2      15.52
3      ...</td>
      <td>0      15.72
1      14.02
2      13.68
3      ...</td>
      <td>0      13.70
1      12.88
2      12.31
3      ...</td>
      <td>0      13.71
1      11.20
2      11.49
3      ...</td>
      <td>0       11.90
1       10.62
2        9.77
3   ...</td>
      <td>0       10.77
1        9.28
2        9.51
3   ...</td>
    </tr>
    <tr>
      <th rowspan="2" valign="top">Committee Participation %</th>
      <th>mean</th>
      <td>25.91</td>
      <td>40.26</td>
      <td>50.18</td>
      <td>57.87</td>
      <td>62.37</td>
      <td>67.58</td>
      <td>70.66</td>
      <td>73.86</td>
      <td>75.84</td>
      <td>77.15</td>
      <td>...</td>
      <td>106.02</td>
      <td>131.7</td>
      <td>156.54</td>
      <td>179.34</td>
      <td>201.49</td>
      <td>223.17</td>
      <td>244.46</td>
      <td>261.56</td>
      <td>279.83</td>
      <td>298.7</td>
    </tr>
    <tr>
      <th>sd</th>
      <td>2.025315</td>
      <td>2.55194</td>
      <td>3.191802</td>
      <td>3.306524</td>
      <td>3.110161</td>
      <td>3.672002</td>
      <td>3.663932</td>
      <td>3.487177</td>
      <td>3.801894</td>
      <td>3.235352</td>
      <td>...</td>
      <td>4.14</td>
      <td>4.670118</td>
      <td>5.485289</td>
      <td>5.680176</td>
      <td>5.356295</td>
      <td>5.921241</td>
      <td>6.25527</td>
      <td>5.846914</td>
      <td>6.926839</td>
      <td>7.054786</td>
    </tr>
  </tbody>
</table>
<p>5 rows × 144 columns</p>
</div>




```python
# %%

# Save the results to an Excel file
output_file = "../data/participation_run_results.xlsx"
sim_results_df.to_excel(output_file)
print(f"Results saved to {output_file}")
```

    Results saved to ../data/participation_run_results.xlsx

