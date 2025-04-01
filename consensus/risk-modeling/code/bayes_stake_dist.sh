#!/bin/bash
# Script to execute the participation_gen.py script
# with various parameters for committee size, group size, and stake.

./bayes_stake_dist.py \
    --committee-size 350 \
    --group-size 100 200 300 400 500 600 \
    --stake-size 10 100 1_000 10_000 100_000 1_000_000 10_000_000 100_000_000 \
    --seed 123 \
    --verbose

echo "Participation generation completed."
