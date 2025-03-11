# Consensus Risk Modeling
This folder holds scripts, data, and analyses concerning consensus risks.  It includes models of current and exploratory consensus models for Midnight.


## Dependencies
- `requirements.txt`
- `Pipfile`

Install the dependencies using:
```bash
pipenv install
```

## Structure
```bash
├── README.md
└── requirements.txt
├── Pipfile
├── Pipfile.lock
├── code/
├── data/
├── docs/
```

## Quick Start

#### Finality Risk Analysis

This analysis is performed primarily by the module:

`finality_risk_paper.py`

which provided the simulation results for the 
Committee Selection Risks paper by Jon Rossie.
The working paper can be found [here on Confluence](https://shielded.atlassian.net/wiki/spaces/MN/pages/27930168/Ariadne+Review+Analysis?atlOrigin=eyJpIjoiM2QzYmY2OGM5MzE5NDVmNzkzNTMzY2I0N2U5ZTAzMGYiLCJwIjoiY29uZmx1ZW5jZS1jaGF0cy1pbnQifQ).

Execute this module from the command line as follows: 

```bash
python finality_risk_paper.py <committee_size> <num_participants> [<num_federated>]
```
where:
    `<committee_size>` is the number of participants in the committee.
    `<num_participants>` is the number of participants in the population.
    `<num_federated>` is the number of federated nodes.

If `<num_federated>` is omitted, it defaults to `10`
Example: `python finality_risk_paper.py 300 1000 10`
Example: `python finality_risk_paper.py 300 1000`

#### Committee Participation

This analysis aims to understand the distribution of selections in a committee when varying sizes of the participant pool of SPOs and the committee. We show that the "pigeonhole principle" helps us  interpret the results and understand the finite distribution of the committee seats assigned to participants as a function of stake, group, and committee sizes.

The experiment is designed to:
- Sample without replacement a group of participants from the population.
- Calculate the stake weight for each participant, which is the stake normalized over the group to sum to 1.
- Assign a committee of the fixed group size based on the stake weight of each using random selection with replacement.
- Analyze the relationship and distribution of committee selection with group size.

We conducted the experiments with varying sizes (100, 200, ..., 500) of groups and committees.  The results are visualized through plots of committee assignments where we vary the group size to see how the committee selection and seat count changes.

The results show that some group members with smaller stake weights may not (ever?) get selected for committee seats. With repeated trials where a new committee is selected, called an *epoch*, and assuming nonzero stake weight, there is nonzero probability of selecting *any* participant in the long run. However, in the short term, there is a significant chance that some participants will not ever get selected, almost surely. This is a natural outcome of the selection process with a discrete and finite number of seats. This is a manifestation of the this committee selection process as it currently stands.

**Usage:**
The code comprises two modules:
- `participation_lib.py` library of functions used
- `participation_run.py` script to execute the simulations and visualizations

Simulation results can be found in the following:
- `code/participation_run.ipynb` 
- `docs/participation_run/`  which includes markdown, html, and png figures.