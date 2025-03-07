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

 We conducted the experiments with varying sizes $(100, 200, ..., 500)$
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
    group_size=100,
    num_iter=1,
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
      <td>74560000.0</td>
      <td>7.017396e-02</td>
    </tr>
    <tr>
      <th>1</th>
      <td>70000000.0</td>
      <td>6.588221e-02</td>
    </tr>
    <tr>
      <th>2</th>
      <td>70000000.0</td>
      <td>6.588221e-02</td>
    </tr>
    <tr>
      <th>3</th>
      <td>70000000.0</td>
      <td>6.588221e-02</td>
    </tr>
    <tr>
      <th>4</th>
      <td>64730000.0</td>
      <td>6.092222e-02</td>
    </tr>
    <tr>
      <th>...</th>
      <td>...</td>
      <td>...</td>
    </tr>
    <tr>
      <th>95</th>
      <td>23.0</td>
      <td>2.164701e-08</td>
    </tr>
    <tr>
      <th>96</th>
      <td>18.0</td>
      <td>1.694114e-08</td>
    </tr>
    <tr>
      <th>97</th>
      <td>8.0</td>
      <td>7.529395e-09</td>
    </tr>
    <tr>
      <th>98</th>
      <td>2.0</td>
      <td>1.882349e-09</td>
    </tr>
    <tr>
      <th>99</th>
      <td>1.0</td>
      <td>9.411744e-10</td>
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
      <td>1.062502e+07</td>
      <td>1.000000e-02</td>
    </tr>
    <tr>
      <th>std</th>
      <td>2.114452e+07</td>
      <td>1.990068e-02</td>
    </tr>
    <tr>
      <th>min</th>
      <td>1.000000e+00</td>
      <td>9.411744e-10</td>
    </tr>
    <tr>
      <th>25%</th>
      <td>2.867500e+03</td>
      <td>2.698818e-06</td>
    </tr>
    <tr>
      <th>50%</th>
      <td>2.037500e+05</td>
      <td>1.917643e-04</td>
    </tr>
    <tr>
      <th>75%</th>
      <td>5.882500e+06</td>
      <td>5.536458e-03</td>
    </tr>
    <tr>
      <th>max</th>
      <td>7.456000e+07</td>
      <td>7.017396e-02</td>
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
    12  34980000.0      0.032922
    7   63890000.0      0.060132
    8   62190000.0      0.058532
    19  13650000.0      0.012847
    5   64660000.0      0.060856
    ..         ...           ...
    6   64330000.0      0.060546
    11  51710000.0      0.048668
    8   62190000.0      0.058532
    2   70000000.0      0.065882
    5   64660000.0      0.060856
    
    [100 rows x 2 columns]
    
    Seat Counts
    0     0.06903
    3     0.06596
    2     0.06533
    1     0.06508
    6     0.06199
           ...   
    69    0.00000
    68    0.00000
    66    0.00000
    64    0.00000
    99    0.00000
    Name: relative frequency, Length: 100, dtype: float64
    
    First Zero Index
    66



```python
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
    


    Group Size ...: 100 participants
    Committee Size: 200 seats



    
![png](output_9_16.png)
    



    
![png](output_9_17.png)
    


    Group Size ...: 200 participants
    Committee Size: 200 seats



    
![png](output_9_19.png)
    



    
![png](output_9_20.png)
    


    Group Size ...: 300 participants
    Committee Size: 200 seats



    
![png](output_9_22.png)
    



    
![png](output_9_23.png)
    


    Group Size ...: 400 participants
    Committee Size: 200 seats



    
![png](output_9_25.png)
    



    
![png](output_9_26.png)
    


    Group Size ...: 500 participants
    Committee Size: 200 seats



    
![png](output_9_28.png)
    



    
![png](output_9_29.png)
    


    Group Size ...: 100 participants
    Committee Size: 300 seats



    
![png](output_9_31.png)
    



    
![png](output_9_32.png)
    


    Group Size ...: 200 participants
    Committee Size: 300 seats



    
![png](output_9_34.png)
    



    
![png](output_9_35.png)
    


    Group Size ...: 300 participants
    Committee Size: 300 seats



    
![png](output_9_37.png)
    



    
![png](output_9_38.png)
    


    Group Size ...: 400 participants
    Committee Size: 300 seats



    
![png](output_9_40.png)
    



    
![png](output_9_41.png)
    


    Group Size ...: 500 participants
    Committee Size: 300 seats



    
![png](output_9_43.png)
    



    
![png](output_9_44.png)
    


    Group Size ...: 100 participants
    Committee Size: 400 seats



    
![png](output_9_46.png)
    



    
![png](output_9_47.png)
    


    Group Size ...: 200 participants
    Committee Size: 400 seats



    
![png](output_9_49.png)
    



    
![png](output_9_50.png)
    


    Group Size ...: 300 participants
    Committee Size: 400 seats



    
![png](output_9_52.png)
    



    
![png](output_9_53.png)
    


    Group Size ...: 400 participants
    Committee Size: 400 seats



    
![png](output_9_55.png)
    



    
![png](output_9_56.png)
    


    Group Size ...: 500 participants
    Committee Size: 400 seats



    
![png](output_9_58.png)
    



    
![png](output_9_59.png)
    


    Group Size ...: 100 participants
    Committee Size: 500 seats



    
![png](output_9_61.png)
    



    
![png](output_9_62.png)
    


    Group Size ...: 200 participants
    Committee Size: 500 seats



    
![png](output_9_64.png)
    



    
![png](output_9_65.png)
    


    Group Size ...: 300 participants
    Committee Size: 500 seats



    
![png](output_9_67.png)
    



    
![png](output_9_68.png)
    


    Group Size ...: 400 participants
    Committee Size: 500 seats



    
![png](output_9_70.png)
    



    
![png](output_9_71.png)
    


    Group Size ...: 500 participants
    Committee Size: 500 seats



    
![png](output_9_73.png)
    



    
![png](output_9_74.png)
    



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
      <th colspan="5" halign="left">Committee Size = 100</th>
      <th colspan="5" halign="left">Committee Size = 200</th>
      <th>...</th>
      <th colspan="5" halign="left">Committee Size = 400</th>
      <th colspan="5" halign="left">Committee Size = 500</th>
    </tr>
    <tr>
      <th></th>
      <th>Group Size = 100</th>
      <th>Group Size = 200</th>
      <th>Group Size = 300</th>
      <th>Group Size = 400</th>
      <th>Group Size = 500</th>
      <th>Group Size = 100</th>
      <th>Group Size = 200</th>
      <th>Group Size = 300</th>
      <th>Group Size = 400</th>
      <th>Group Size = 500</th>
      <th>...</th>
      <th>Group Size = 100</th>
      <th>Group Size = 200</th>
      <th>Group Size = 300</th>
      <th>Group Size = 400</th>
      <th>Group Size = 500</th>
      <th>Group Size = 100</th>
      <th>Group Size = 200</th>
      <th>Group Size = 300</th>
      <th>Group Size = 400</th>
      <th>Group Size = 500</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <th>0</th>
      <td>0.067845</td>
      <td>0.059950</td>
      <td>0.033845</td>
      <td>0.02261</td>
      <td>0.016740</td>
      <td>0.110023</td>
      <td>0.058183</td>
      <td>0.032363</td>
      <td>0.024580</td>
      <td>0.019247</td>
      <td>...</td>
      <td>0.098936</td>
      <td>0.042228</td>
      <td>0.031282</td>
      <td>0.022488</td>
      <td>0.016358</td>
      <td>0.098936</td>
      <td>0.042228</td>
      <td>0.031282</td>
      <td>0.022488</td>
      <td>0.016358</td>
    </tr>
    <tr>
      <th>1</th>
      <td>0.068715</td>
      <td>0.058495</td>
      <td>0.033610</td>
      <td>0.02243</td>
      <td>0.016370</td>
      <td>0.108877</td>
      <td>0.057353</td>
      <td>0.031813</td>
      <td>0.024490</td>
      <td>0.019043</td>
      <td>...</td>
      <td>0.093620</td>
      <td>0.041044</td>
      <td>0.031380</td>
      <td>0.022328</td>
      <td>0.016434</td>
      <td>0.093620</td>
      <td>0.041044</td>
      <td>0.031380</td>
      <td>0.022328</td>
      <td>0.016434</td>
    </tr>
    <tr>
      <th>2</th>
      <td>0.067155</td>
      <td>0.057850</td>
      <td>0.033825</td>
      <td>0.02232</td>
      <td>0.016395</td>
      <td>0.091033</td>
      <td>0.057610</td>
      <td>0.031537</td>
      <td>0.023550</td>
      <td>0.019190</td>
      <td>...</td>
      <td>0.093920</td>
      <td>0.040756</td>
      <td>0.031458</td>
      <td>0.022052</td>
      <td>0.016206</td>
      <td>0.093920</td>
      <td>0.040756</td>
      <td>0.031458</td>
      <td>0.022052</td>
      <td>0.016206</td>
    </tr>
    <tr>
      <th>3</th>
      <td>0.067555</td>
      <td>0.058080</td>
      <td>0.033280</td>
      <td>0.02143</td>
      <td>0.016020</td>
      <td>0.085087</td>
      <td>0.057087</td>
      <td>0.030130</td>
      <td>0.024257</td>
      <td>0.018683</td>
      <td>...</td>
      <td>0.093074</td>
      <td>0.040992</td>
      <td>0.030788</td>
      <td>0.021814</td>
      <td>0.015854</td>
      <td>0.093074</td>
      <td>0.040992</td>
      <td>0.030788</td>
      <td>0.021814</td>
      <td>0.015854</td>
    </tr>
    <tr>
      <th>4</th>
      <td>0.066210</td>
      <td>0.048815</td>
      <td>0.033235</td>
      <td>0.02139</td>
      <td>0.016050</td>
      <td>0.078980</td>
      <td>0.058020</td>
      <td>0.029650</td>
      <td>0.023930</td>
      <td>0.018703</td>
      <td>...</td>
      <td>0.064470</td>
      <td>0.040954</td>
      <td>0.031078</td>
      <td>0.020330</td>
      <td>0.016032</td>
      <td>0.064470</td>
      <td>0.040954</td>
      <td>0.031078</td>
      <td>0.020330</td>
      <td>0.016032</td>
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
      <th>495</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>...</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>496</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>...</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>497</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>...</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>498</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>...</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
    <tr>
      <th>499</th>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>...</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>NaN</td>
      <td>0.000000</td>
    </tr>
  </tbody>
</table>
<p>500 rows × 25 columns</p>
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
    


### Appendix: Computer Code


```python
#!/usr/bin/env python
# coding: utf-8

"""
Module: participation_lib

This module performs risk modeling for participation distribution in a
consensus mechanism. It includes functions to load and normalize SPO data,
sample participants based on their stake, and perform Monte Carlo simulations
to analyze the committee seat selection process based on stake weight. The
module also demonstrates the uneven distribution of selections based on stake
weights and the finite committee.

Functions:
- sample_group: Uniformly sample from a population of participants without replacement.
- get_stake_distribution: Collect and plot the stake distribution for a sample group.
- assign_commitee: Assign participants to a committee using random selection based on stake weight.
- plot_group_to_committee_index: Scatter plot of group participant index vs. seat selection index.
- plot_committee_selection_counts: Plot the committee selection counts for varying group sizes.
- plot_selection_count_vs_stake: Plot the seat assignment count vs. stake for a committee.

Author: Rob Jones <robert.jones@shield.io>
Date: 5 Mar 2025

"""

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from data import load_data


def sample_group(
    population: pd.DataFrame,
    group_size: int = 300,
) -> pd.DataFrame:
    """
    Uniformly sample from a population of participlants without replacement.
    Only samples groups with nonzero stake is returned.

    Args:
    - population: DataFrame containing the population.
    - group_size: Number of samples to draw.

    Returns:
    - sample: DataFrame of sample of size `group_size` (n).

    """
    sample = population[population.stake > 0].sample(
        group_size,
        replace=False,
    )
    sample["stake_weight"] = sample.stake / sample.stake.sum()
    # Sort by stake weight in descending order
    sample = sample.sort_values("stake_weight", ascending=False)
    return sample


def get_stake_distribution(
    population: pd.DataFrame,
    group_size: int = 300,
    num_iter: int = 1,
    plot_it: bool = True,
    figsize: tuple[int, int] = (16, 8),
) -> pd.DataFrame:
    """ """
    # Let's collect the sample participants.stake.values
    # for every participant in the given sample group size.
    # Average them if num_iter > 1.

    # Initialize an array to store the sum of stakes for each participant
    stakes = np.zeros(group_size)
    for n in range(num_iter):
        participants = sample_group(population, group_size)
        # Add the stakes of the current iteration to the stake_sums array
        stakes += participants.stake.values

    if num_iter > 1:
        # Calculate the average stakes
        stakes = pd.DataFrame(stakes / num_iter, columns=["stake"])
    else:
        stakes = pd.DataFrame(stakes, columns=["stake"])

    min_stake = stakes.stake.min()
    max_stake = stakes.stake.max()

    if plot_it:
        # Plot the stake for each participant number 1 to group_size
        plt.figure(figsize=figsize)
        plt.plot(
            stakes.stake.values,
            marker=".",
            linestyle="-",
            alpha=1,
            color="red",  # Color for the average curve
            linewidth=2,
            markersize=3,
            label="Average Stake",
        )

        # Draw a horizontal line at maximum stake value
        plt.axhline(
            y=max_stake,
            color="blue",
            linestyle="--",
            alpha=0.6,
            label=f"Max. Stake = {max_stake}",
        )

        # Draw a horizontal line at minimum stake value
        plt.axhline(
            y=min_stake,
            color="green",
            linestyle="--",
            alpha=0.6,
            label=f"Min. Stake = {min_stake}",
        )

        plt.legend()
        plt.title(f"Stake for each Participant (1 to {group_size})")
        plt.xlabel("Participant Number")
        plt.ylabel("Stake")
        plt.show()

    # Add the stake weight column to the DataFrame
    stakes["stake_weight"] = stakes.stake / stakes.stake.sum()

    return stakes


def assign_commitee(
    group: pd.DataFrame,
    committee_size: int = 300,
    alpha: float = 0.0,
    num_iter: int = 1000,
    figsize: tuple[int, int] = (16, 8),
) -> tuple[pd.DataFrame, pd.Series, int]:
    """
    Assumes participants in a given group of size group_size are assigned to
    a committee using random selection with replacement based on their stake
    weight. The committee has a fixed size equal to the group_size. As such,
    partipants with larger stake-weight will occupy multiple committee seats.
    We perform Monte Carlo simulation of multiplle committee selections, thus
    repeated for the given number of iterations.

    Args:
    - group: DataFrame containing the group of participants, assumed size n.
    - committee_size: Size of the committee (k).
    - alpha: Probability of uniform random sampling in a mixture model.
    - num_iter: Number of iterations for Monte Carlo simulation.
    - figsize: Size of the figure.

    Returns:
    - committee: DataFrame containing the committee members.
    - seat_counts: Series containing the committee seat relative frequency.
    - first_zero_index: Index where the seat count first goes to zero.

    """
    group_size = group.shape[0]  # size n

    # Initialize an array to store the number of
    # committee seats per participant
    seat_counts = pd.Series(
        np.zeros(group_size, dtype="int64"),
        name="relative frequency",
    )

    for n in range(num_iter):
        #
        # Select a committee based on the stake weight of each
        # participant stake holder.
        #
        committee = group.sample(
            n=committee_size,
            weights="stake_weight",
            replace=True,
        )

        # Count the number of times each participant is selected
        # for a committee seat
        participant_counts = committee.index.value_counts()

        # Reindex participant_counts to match sum_counts index
        # and fill missing values with 0
        participant_counts = participant_counts.reindex(
            seat_counts.index,
            fill_value=0,
        )

        # Add the counts to the sum_counts array
        seat_counts += participant_counts

    # Normalize the sum_counts by total sum of counts
    seat_counts /= seat_counts.sum()

    # Sort the sum_counts in descending order
    seat_counts.sort_values(ascending=False, inplace=True)

    # Get the index of sum_counts where the value is first zero
    first_zero_index = group.index[: -seat_counts[seat_counts == 0.0].shape[0]].max()

    # Let's plot both group and sum_counts with two y-axes,
    # one for each
    fig, ax1 = plt.subplots(figsize=figsize)
    ax2 = ax1.twinx()
    ax1.plot(seat_counts.values, color="blue", label="Committee Seat Frequency")
    ax2.plot(group.stake_weight.values, color="red", label="Group Stake Weight")
    ax1.set_ylabel("Committee Seats (relative frequency)")
    ax2.set_ylabel("Stake Weight")
    ax1.set_xlabel("Participant Index")
    ax1.legend(loc="upper center")
    ax2.legend(loc="upper right")
    plt.title(
        f"Committee Participation per Stake Weight\n"
        f"Committee Size k = {committee_size}\n"
        f"Participation Group Size n = {group_size}",
        fontsize="medium",
    )
    plt.axhline(y=0, color="gray", linestyle="--", alpha=0.6)
    # Draw vertical line where the committee seat count first goes to zero
    plt.axvline(x=first_zero_index, color="green", linestyle="--")
    # Print the value of this first_zero_index along the center of the
    # vertical line
    plt.text(
        first_zero_index,
        ax2.get_ylim()[1] / 2.0,
        f"First Zero Index = {first_zero_index}",
        rotation=0,
        verticalalignment="center",
        horizontalalignment="center",
        color="green",
        backgroundcolor="white",
    )
    plt.show()

    return committee, seat_counts, first_zero_index


def plot_group_to_committee_index(
    seat_counts: pd.Series,
    figsize: tuple[int, int] = (6, 6),
):
    """
    A simple scatter plot of the two series indexes
    to see how they align.

    Args:
    - seat_counts: Series containing the committee seat counts
      indexed by participant index.
    - figsize: Size of the figure.

    """
    plt.figure(figsize=figsize)
    plt.scatter(
        np.arange(len(seat_counts)),
        seat_counts.index,
        marker=".",
        color="green",
    )
    plt.xlabel("Group Participant Index")
    plt.ylabel("Seat Selection Participant Index")
    plt.title("Seat Selection Index vs. Participant Index")
    plt.legend()
    plt.show()


# Plot the selection counts for each group size
def plot_committee_selection_counts(
    committee_size: int,
    selection_counts: pd.DataFrame,
    first_zero_indices: np.ndarray,
    log_scale: bool = True,
    figsize: tuple[int, int] = (16, 8),
):
    """
    Plot the committee selection counts for varying group sizes.

    Args:
    - committee_size: Size of the committee (k).
    - selection_counts: DataFrame containing the committee seat relative frequency.
    - first_zero_indices: Array containing the first zero index for each group size.
    - log_scale: Boolean flag to set the y-axis to log scale.
    - figsize: Size of the figure.

    """
    plt.figure(figsize=figsize)
    selection_counts.plot(
        marker="",
        linestyle="-",
        linewidth=1,
        alpha=0.9,
    )
    for i, cutoff in enumerate(first_zero_indices):
        plt.axvline(
            x=cutoff,
            color=plt.gca().lines[i].get_color(),
            linestyle="--",
            linewidth=1,
            alpha=0.6,
        )
        # Print the value of this cutoff value
        # along the center of the vertical line
        plt.text(
            cutoff,
            plt.gca().get_ylim()[1] / 2.0,
            f"{int(cutoff)}",
            rotation=0,
            verticalalignment="center",
            horizontalalignment="center",
            color=plt.gca().lines[i].get_color(),
            backgroundcolor="white",
            fontsize="medium",
        )
        if log_scale:
            plt.yscale("log")

    plt.legend(fontsize="small")
    plt.xlabel("Participant Index", fontsize="small")
    plt.ylabel("Committee Seat Frequency", fontsize="small")
    plt.title(
        f"Committee Participation from Varying Group Sizes\n"
        f"Committee Size k = {committee_size}",
        fontsize="medium",
    )
    plt.show()


def plot_selection_count_vs_stake(
    group_stakes: pd.DataFrame,
    committee_seats: pd.DataFrame,
    first_zero_index: int,
    figsize: tuple[int, int] = (16, 8),
):
    """
    Plot the seat assignment count vs. stake for a committee
    of a given size.

    Args:
    - group_stakes: DataFrame containing the stake weight of each participant.
    - committee_seats: DataFrame containing the committee members.
    - first_zero_index: Index where the seat count first goes to zero.
    - figsize: Size of the figure.

    """
    committee_size = committee_seats.shape[0]
    group_size = group_stakes.shape[0]
    cutoff = group_stakes.loc[first_zero_index, "stake_weight"]

    # Count the number of seats each participant has in the committee
    participant_counts = committee_seats.index.value_counts()
    assert participant_counts.index.is_unique

    # Align committee_members with participant_counts
    committee_members = group_stakes.loc[participant_counts.index].sort_values(
        by="stake_weight", ascending=False
    )

    x = committee_members.stake_weight.values
    y = participant_counts.values

    # Plot selection seat count vs. stake
    plt.figure(figsize=figsize)
    plt.plot(
        x,
        y,
        marker=".",
        linestyle="-",
        alpha=0.8,
    )
    plt.gca().invert_xaxis()
    plt.xlabel("Participant Stake Weight")
    plt.ylabel("Participant Seat Counts")
    plt.title(
        "Committee Participation per Stake Weight\n"
        f"Committee Size k = {committee_size}\n"
        f"Participation Group Size n = {group_size}",
        fontsize="medium",
    )
    plt.axvline(
        x=cutoff,
        color="gray",
        linestyle="--",
        linewidth=1,
        alpha=0.6,
    )
    # Print the value of this cutoff value along the center of the vertical line
    plt.text(
        cutoff,
        plt.gca().get_ylim()[1] / 2.0,
        f"Cutoff stake weight = {int(cutoff)}",
        rotation=0,
        verticalalignment="center",
        horizontalalignment="right",
        color="black",
        backgroundcolor="white",
        fontsize="medium",
    )
    plt.show()


def plot_committee_selection_seat_cutoff(
    committee_sizes: list,
    committee_seats_df: pd.DataFrame,
    first_zero_indices: np.ndarray,
    log_scale: bool = False,
):
    """
    Plot the committee selection counts for each group size.

    Args:
    - committee_sizes: list of committee sizes
    - committee_seats_df: DataFrame of committee selection counts
    - first_zero_indices: array of first zero indices
    - log_scale: whether to use log scale for the plot

    Returns:
    - None

    """
    # Loop over the committee sizes
    for i, committee_size in enumerate(
        committee_seats_df.columns.get_level_values(0).unique()
    ):
        plot_committee_selection_counts(
            committee_size=committee_sizes[i],
            selection_counts=committee_seats_df[committee_size],
            first_zero_indices=first_zero_indices[i],
            log_scale=log_scale,
        )
```
