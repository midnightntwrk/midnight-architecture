 # Participation Distribution in Committee Selection

 ### Executive Summary

 In the following computer experiments,
 we aim to understand the distribution of selections in a committee
 when varying sizes of the participant pool of SPOs and the committee.
 We show that the "pigeonhole principle" helps us interpret the results
 and understand the finite distribution of the committee seats assigned
 to participants as a function of stake, group, and committee sizes.

 The experiment is designed to:
 - Sample without replacement a group of participants from the population and
 - Calculate the stake weight for each participant, which is the stake normalized
   over the group to sum to 1.
 - Assign a committee of the fixed group size based on the stake weight of each
   using random selection with replacement.
 - Analyze the relationship and distribution of committee selection with group size.

 We conducted the experiments with varying sizes $(100, 200, 300, ..., 800)$
 of groups and committees. The results are visualized through plots of committee
 assignments where we vary the group size to see how the committee selection and
 seat count changes.

 The results show that some group members with smaller stake weights may not (ever?)
 get selected for committee seats.
 With repeated trials where a new committee is selected, called an *epoch*,
 and assuming nonzero stake weight, there is nonzero probability of selecting *any*
 participant in the long run. However, in the short term, there is a significant chance
 that some participants will not ever get selected, almost surely.
 This is a natural outcome of the selection process
 with a discrete and finite number of seats. This is a manifestation of the
 this committee selection process as it currently stands.



```python
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
```


```python
# %%

# Load the Data: The population of registered SPOs

population = load_data("../data/pooltool-cleaned.csv")
population.info()
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
    num_iter=1000,
    plot_it=True,
)
group_stakes
```


    
![png](output_4_0.png)
    





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
      <th>stake_weight</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <th>0</th>
      <td>7.250552e+07</td>
      <td>9.187861e-02</td>
    </tr>
    <tr>
      <th>1</th>
      <td>6.841225e+07</td>
      <td>8.669164e-02</td>
    </tr>
    <tr>
      <th>2</th>
      <td>6.467127e+07</td>
      <td>8.195109e-02</td>
    </tr>
    <tr>
      <th>3</th>
      <td>5.973343e+07</td>
      <td>7.569388e-02</td>
    </tr>
    <tr>
      <th>4</th>
      <td>5.455255e+07</td>
      <td>6.912870e-02</td>
    </tr>
    <tr>
      <th>...</th>
      <td>...</td>
      <td>...</td>
    </tr>
    <tr>
      <th>95</th>
      <td>1.949900e+01</td>
      <td>2.470903e-08</td>
    </tr>
    <tr>
      <th>96</th>
      <td>1.151700e+01</td>
      <td>1.459428e-08</td>
    </tr>
    <tr>
      <th>97</th>
      <td>6.368000e+00</td>
      <td>8.069496e-09</td>
    </tr>
    <tr>
      <th>98</th>
      <td>3.539000e+00</td>
      <td>4.484602e-09</td>
    </tr>
    <tr>
      <th>99</th>
      <td>1.706000e+00</td>
      <td>2.161834e-09</td>
    </tr>
  </tbody>
</table>
<p>100 rows × 2 columns</p>
</div>




```python
# %%

group_stakes.describe()
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
      <th>stake_weight</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <th>count</th>
      <td>1.000000e+02</td>
      <td>1.000000e+02</td>
    </tr>
    <tr>
      <th>mean</th>
      <td>7.891447e+06</td>
      <td>1.000000e-02</td>
    </tr>
    <tr>
      <th>std</th>
      <td>1.662034e+07</td>
      <td>2.106120e-02</td>
    </tr>
    <tr>
      <th>min</th>
      <td>1.706000e+00</td>
      <td>2.161834e-09</td>
    </tr>
    <tr>
      <th>25%</th>
      <td>1.886276e+03</td>
      <td>2.390279e-06</td>
    </tr>
    <tr>
      <th>50%</th>
      <td>1.532795e+05</td>
      <td>1.942350e-04</td>
    </tr>
    <tr>
      <th>75%</th>
      <td>4.771583e+06</td>
      <td>6.046524e-03</td>
    </tr>
    <tr>
      <th>max</th>
      <td>7.250552e+07</td>
      <td>9.187861e-02</td>
    </tr>
  </tbody>
</table>
</div>




```python
# %%

# Let's now assign a committee of the fixed group_size
# based on the stake weight of each

committee, seat_counts, first_zero_index = assign_commitee(
    group_stakes,
    committee_size=group_size,
    num_iter=1000,
)
```


    
![png](output_6_0.png)
    



```python
# %%

print("Committee")  # Participants selected for the committee
print(committee)
print("\nSeat Counts")  # Number of times each participant is selected
print(seat_counts)
print("\nFirst Zero Index")  # Index where the seat count first goes to zero
print(first_zero_index)
```

    Committee
              stake  stake_weight
    1   68412250.00      0.086692
    6   44320150.00      0.056162
    24   5272658.06      0.006681
    2   64671270.00      0.081951
    0   72505520.00      0.091879
    ..          ...           ...
    24   5272658.06      0.006681
    3   59733430.00      0.075694
    7   39975470.00      0.050657
    4   54552550.00      0.069129
    24   5272658.06      0.006681
    
    [100 rows x 2 columns]
    
    Seat Counts
    0     0.09152
    1     0.08581
    2     0.08115
    3     0.07591
    4     0.06956
           ...   
    72    0.00000
    68    0.00000
    65    0.00000
    63    0.00000
    99    0.00000
    Name: relative frequency, Length: 100, dtype: float64
    
    First Zero Index
    69



```python
# %%

# Let's now create a plots of committee assignments where we vary
# the group size over {100, 200, 300, 400, 500} and see how the
# committee selection and seat count changes.

# Initialize Parameters:
comm_sizes = [100, 200, 300, 400, 500]  # vary over committee size, k
group_sizes = [
    100,
    200,
    300,
    400,
    500,
    600,
    700,
    800,
]  # vary over group size, n
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
```


```python
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
```

    Group Size ...: 100 participants
    Committee Size: 100 seats



    
![png](output_9_1.png)
    



    
![png](output_9_2.png)
    


    Group Size ...: 200 participants
    Committee Size: 100 seats



    
![png](output_9_4.png)
    



    
![png](output_9_5.png)
    


    Group Size ...: 300 participants
    Committee Size: 100 seats



    
![png](output_9_7.png)
    



    
![png](output_9_8.png)
    


    Group Size ...: 400 participants
    Committee Size: 100 seats



    
![png](output_9_10.png)
    



    
![png](output_9_11.png)
    


    Group Size ...: 500 participants
    Committee Size: 100 seats



    
![png](output_9_13.png)
    



    
![png](output_9_14.png)
    


    Group Size ...: 600 participants
    Committee Size: 100 seats



    
![png](output_9_16.png)
    



    
![png](output_9_17.png)
    


    Group Size ...: 700 participants
    Committee Size: 100 seats



    
![png](output_9_19.png)
    



    
![png](output_9_20.png)
    


    Group Size ...: 800 participants
    Committee Size: 100 seats



    
![png](output_9_22.png)
    



    
![png](output_9_23.png)
    


    Group Size ...: 100 participants
    Committee Size: 200 seats



    
![png](output_9_25.png)
    



    
![png](output_9_26.png)
    


    Group Size ...: 200 participants
    Committee Size: 200 seats



    
![png](output_9_28.png)
    



    
![png](output_9_29.png)
    


    Group Size ...: 300 participants
    Committee Size: 200 seats



    
![png](output_9_31.png)
    



    
![png](output_9_32.png)
    


    Group Size ...: 400 participants
    Committee Size: 200 seats



    
![png](output_9_34.png)
    



    
![png](output_9_35.png)
    


    Group Size ...: 500 participants
    Committee Size: 200 seats



    
![png](output_9_37.png)
    



    
![png](output_9_38.png)
    


    Group Size ...: 600 participants
    Committee Size: 200 seats



    
![png](output_9_40.png)
    



    
![png](output_9_41.png)
    


    Group Size ...: 700 participants
    Committee Size: 200 seats



    
![png](output_9_43.png)
    



    
![png](output_9_44.png)
    


    Group Size ...: 800 participants
    Committee Size: 200 seats



    
![png](output_9_46.png)
    



    
![png](output_9_47.png)
    


    Group Size ...: 100 participants
    Committee Size: 300 seats



    
![png](output_9_49.png)
    



    
![png](output_9_50.png)
    


    Group Size ...: 200 participants
    Committee Size: 300 seats



    
![png](output_9_52.png)
    



    
![png](output_9_53.png)
    


    Group Size ...: 300 participants
    Committee Size: 300 seats



    
![png](output_9_55.png)
    



    
![png](output_9_56.png)
    


    Group Size ...: 400 participants
    Committee Size: 300 seats



    
![png](output_9_58.png)
    



    
![png](output_9_59.png)
    


    Group Size ...: 500 participants
    Committee Size: 300 seats



    
![png](output_9_61.png)
    



    
![png](output_9_62.png)
    


    Group Size ...: 600 participants
    Committee Size: 300 seats



    
![png](output_9_64.png)
    



    
![png](output_9_65.png)
    


    Group Size ...: 700 participants
    Committee Size: 300 seats



    
![png](output_9_67.png)
    



    
![png](output_9_68.png)
    


    Group Size ...: 800 participants
    Committee Size: 300 seats



    
![png](output_9_70.png)
    



    
![png](output_9_71.png)
    


    Group Size ...: 100 participants
    Committee Size: 400 seats



    
![png](output_9_73.png)
    



    
![png](output_9_74.png)
    


    Group Size ...: 200 participants
    Committee Size: 400 seats



    
![png](output_9_76.png)
    



    
![png](output_9_77.png)
    


    Group Size ...: 300 participants
    Committee Size: 400 seats



    
![png](output_9_79.png)
    



    
![png](output_9_80.png)
    


    Group Size ...: 400 participants
    Committee Size: 400 seats



    
![png](output_9_82.png)
    



    
![png](output_9_83.png)
    


    Group Size ...: 500 participants
    Committee Size: 400 seats



    
![png](output_9_85.png)
    



    
![png](output_9_86.png)
    


    Group Size ...: 600 participants
    Committee Size: 400 seats



    
![png](output_9_88.png)
    



    
![png](output_9_89.png)
    


    Group Size ...: 700 participants
    Committee Size: 400 seats



    
![png](output_9_91.png)
    



    
![png](output_9_92.png)
    


    Group Size ...: 800 participants
    Committee Size: 400 seats



    
![png](output_9_94.png)
    



    
![png](output_9_95.png)
    


    Group Size ...: 100 participants
    Committee Size: 500 seats



    
![png](output_9_97.png)
    



    
![png](output_9_98.png)
    


    Group Size ...: 200 participants
    Committee Size: 500 seats



    
![png](output_9_100.png)
    



    
![png](output_9_101.png)
    


    Group Size ...: 300 participants
    Committee Size: 500 seats



    
![png](output_9_103.png)
    



    
![png](output_9_104.png)
    


    Group Size ...: 400 participants
    Committee Size: 500 seats



    
![png](output_9_106.png)
    



    
![png](output_9_107.png)
    


    Group Size ...: 500 participants
    Committee Size: 500 seats



    
![png](output_9_109.png)
    



    
![png](output_9_110.png)
    


    Group Size ...: 600 participants
    Committee Size: 500 seats



    
![png](output_9_112.png)
    



    
![png](output_9_113.png)
    


    Group Size ...: 700 participants
    Committee Size: 500 seats



    
![png](output_9_115.png)
    



    
![png](output_9_116.png)
    


    Group Size ...: 800 participants
    Committee Size: 500 seats



    
![png](output_9_118.png)
    



    
![png](output_9_119.png)
    



```python
# %%

# I want to combine the selection counts for each committee size
# into a single DataFrame for easier analysis and plotting.
# Make committee size a new column in the DataFrame
committee_seats_df = pd.concat(
    committee_seats,
    axis=1,
)
committee_seats_df
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
      <th colspan="8" halign="left">Committee Size = 100</th>
      <th colspan="2" halign="left">Committee Size = 200</th>
      <th>...</th>
      <th colspan="2" halign="left">Committee Size = 400</th>
      <th colspan="8" halign="left">Committee Size = 500</th>
    </tr>
    <tr>
      <th></th>
      <th>Group Size = 100</th>
      <th>Group Size = 200</th>
      <th>Group Size = 300</th>
      <th>Group Size = 400</th>
      <th>Group Size = 500</th>
      <th>Group Size = 600</th>
      <th>Group Size = 700</th>
      <th>Group Size = 800</th>
      <th>Group Size = 100</th>
      <th>Group Size = 200</th>
      <th>...</th>
      <th>Group Size = 700</th>
      <th>Group Size = 800</th>
      <th>Group Size = 100</th>
      <th>Group Size = 200</th>
      <th>Group Size = 300</th>
      <th>Group Size = 400</th>
      <th>Group Size = 500</th>
      <th>Group Size = 600</th>
      <th>Group Size = 700</th>
      <th>Group Size = 800</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <th>0</th>
      <td>0.08757</td>
      <td>0.043200</td>
      <td>0.040625</td>
      <td>0.026810</td>
      <td>0.018830</td>
      <td>0.015130</td>
      <td>0.016680</td>
      <td>0.011470</td>
      <td>0.071170</td>
      <td>0.046437</td>
      <td>...</td>
      <td>0.013800</td>
      <td>0.012996</td>
      <td>0.093502</td>
      <td>0.046058</td>
      <td>0.033262</td>
      <td>0.023990</td>
      <td>0.017010</td>
      <td>0.016038</td>
      <td>0.013800</td>
      <td>0.012996</td>
    </tr>
    <tr>
      <th>1</th>
      <td>0.08796</td>
      <td>0.042655</td>
      <td>0.029030</td>
      <td>0.025680</td>
      <td>0.018080</td>
      <td>0.015380</td>
      <td>0.011895</td>
      <td>0.011845</td>
      <td>0.069837</td>
      <td>0.045970</td>
      <td>...</td>
      <td>0.013242</td>
      <td>0.012174</td>
      <td>0.092302</td>
      <td>0.044934</td>
      <td>0.032242</td>
      <td>0.023464</td>
      <td>0.016884</td>
      <td>0.015796</td>
      <td>0.013242</td>
      <td>0.012174</td>
    </tr>
    <tr>
      <th>2</th>
      <td>0.08623</td>
      <td>0.041585</td>
      <td>0.029060</td>
      <td>0.025565</td>
      <td>0.018515</td>
      <td>0.015390</td>
      <td>0.012240</td>
      <td>0.011585</td>
      <td>0.068637</td>
      <td>0.046003</td>
      <td>...</td>
      <td>0.013082</td>
      <td>0.012356</td>
      <td>0.092222</td>
      <td>0.044570</td>
      <td>0.032260</td>
      <td>0.023024</td>
      <td>0.016370</td>
      <td>0.015764</td>
      <td>0.013082</td>
      <td>0.012356</td>
    </tr>
    <tr>
      <th>3</th>
      <td>0.08575</td>
      <td>0.041100</td>
      <td>0.027050</td>
      <td>0.025270</td>
      <td>0.017825</td>
      <td>0.015835</td>
      <td>0.011910</td>
      <td>0.011380</td>
      <td>0.067917</td>
      <td>0.045767</td>
      <td>...</td>
      <td>0.013126</td>
      <td>0.012472</td>
      <td>0.079798</td>
      <td>0.044686</td>
      <td>0.031870</td>
      <td>0.023178</td>
      <td>0.016324</td>
      <td>0.015916</td>
      <td>0.013126</td>
      <td>0.012472</td>
    </tr>
    <tr>
      <th>4</th>
      <td>0.08662</td>
      <td>0.039510</td>
      <td>0.027585</td>
      <td>0.024540</td>
      <td>0.018140</td>
      <td>0.015455</td>
      <td>0.011295</td>
      <td>0.011550</td>
      <td>0.068020</td>
      <td>0.045420</td>
      <td>...</td>
      <td>0.012796</td>
      <td>0.012618</td>
      <td>0.065576</td>
      <td>0.044846</td>
      <td>0.031668</td>
      <td>0.023638</td>
      <td>0.016462</td>
      <td>0.015060</td>
      <td>0.012796</td>
      <td>0.012618</td>
    </tr>
    <tr>
      <th>...</th>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
      <td>...</td>
    </tr>
    <tr>
      <th>795</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>...</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>796</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>...</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>797</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>...</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>798</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>...</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>799</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>...</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
  </tbody>
</table>
<p>800 rows × 40 columns</p>
</div>




```python
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
```


    <Figure size 1600x800 with 0 Axes>



    
![png](output_11_1.png)
    



    <Figure size 1600x800 with 0 Axes>



    
![png](output_11_3.png)
    



    <Figure size 1600x800 with 0 Axes>



    
![png](output_11_5.png)
    



    <Figure size 1600x800 with 0 Axes>



    
![png](output_11_7.png)
    



    <Figure size 1600x800 with 0 Axes>



    
![png](output_11_9.png)
    



```python
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
```


    <Figure size 1600x800 with 0 Axes>



    
![png](output_12_1.png)
    



    <Figure size 1600x800 with 0 Axes>



    
![png](output_12_3.png)
    



    <Figure size 1600x800 with 0 Axes>



    
![png](output_12_5.png)
    



    <Figure size 1600x800 with 0 Axes>



    
![png](output_12_7.png)
    



    <Figure size 1600x800 with 0 Axes>



    
![png](output_12_9.png)
    



```python
# %%

# committee_seats_df = committee_seats_df.swaplevel(axis=1).sort_index(axis=1)
```


```python
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
```


```python
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
```


    
![png](output_15_0.png)
    



```python
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
```


    
![png](output_16_0.png)
    



```python
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
```


    
![png](output_17_0.png)
    



```python
# %%

# Save data to an Excel file

data = {}
data["committee_seats"] = committee_seats_df
data["first_zero_indices"] = pd.DataFrame(
    first_zero_indices,
    index=comm_sizes,
    columns=group_sizes,
)
data["not_selected_percentages"] = not_selected_df

with pd.ExcelWriter("../data/sim_results_data.xlsx") as writer:
    for sheet_name, df in data.items():
        df.to_excel(writer, sheet_name=sheet_name)
```


```python
# %%

# Model the number of distinct voters for various group sizes
# with committee size k = 400

committee_size = 400
distinct_voters = {}
distinct_voters_std = {}
n_iters = 100

# Loop over the group sizes
for group_size in group_sizes:
    print(f"Group Size ...: {group_size} participants")
    print(f"Committee Size: {committee_size} seats")

    distinct_voters_list = []

    for _ in range(n_iters):
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

        # Count the number of distinct voters
        distinct_voters_list.append(len(committee.index.unique()))

    # Average the number of distinct voters over the iterations
    distinct_voters[group_size] = np.mean(distinct_voters_list)
    # Standard deviation of the number of distinct voters
    distinct_voters_std[group_size] = np.std(distinct_voters_list)

# Create a DataFrame for plotting
distinct_voters_df = pd.DataFrame(
    list(distinct_voters.items()),
    columns=["Group Size", "Distinct Voters"],
)
distinct_voters_df["Std Dev"] = distinct_voters_df["Group Size"].map(distinct_voters_std)
```

    Group Size ...: 100 participants
    Committee Size: 400 seats
    Group Size ...: 200 participants
    Committee Size: 400 seats
    Group Size ...: 300 participants
    Committee Size: 400 seats
    Group Size ...: 400 participants
    Committee Size: 400 seats
    Group Size ...: 500 participants
    Committee Size: 400 seats
    Group Size ...: 600 participants
    Committee Size: 400 seats
    Group Size ...: 700 participants
    Committee Size: 400 seats
    Group Size ...: 800 participants
    Committee Size: 400 seats



```python
# %%

# Plot the number of distinct voters for each group size with error bars
plt.figure(figsize=(12, 8))
sns.lineplot(data=distinct_voters_df, x="Group Size", y="Distinct Voters", marker="o")

# Add error bars
plt.errorbar(
    distinct_voters_df["Group Size"],
    distinct_voters_df["Distinct Voters"],
    yerr=distinct_voters_df["Std Dev"],
    fmt="o",
    ecolor="r",
    capsize=5,
)

# Add the actual values next to each data point with more offset
for i in range(distinct_voters_df.shape[0]):
    plt.text(
        distinct_voters_df["Group Size"][i] - 5,  # Offset horizontally
        distinct_voters_df["Distinct Voters"][i],  # Offset vertically
        f"{distinct_voters_df['Distinct Voters'][i]}",
        horizontalalignment="right",
        size="medium",
        color="black",
        weight="semibold",
    )

plt.title(
    "Average Number of Distinct Voters for Various Group Sizes (Committee Size = 400)"
)
plt.xlabel("Group Size")
plt.ylabel("Average Number of Distinct Voters")
plt.grid(axis="y", linestyle="--", alpha=0.6)
plt.tight_layout()
plt.show()
```


    
![png](output_20_0.png)
    

