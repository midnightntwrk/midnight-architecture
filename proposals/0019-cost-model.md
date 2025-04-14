# Proposal 0019: Cost Model

This proposal suggests methodology for building the ledger's cost model, as
well as a first draft of the parameters to gather, and how to evaluate their
accuracy.

## Problem Statement

The ledger must charge for transactions to deter denial of service attacks.
There is a tension that encourages these prices to be as accurate as possible:

- A practical desire to keep transaction fees low
- A security requirement to not under-charge

This is further complicated by the variety of different host systems that may
run a node, and there being a number of unrelated 'costs' that need to be
balanced.

## Proposed Changes

This proposal suggests a cost model split between I/O cost and CPU cost. Each
of these come with subtleties, that we will go into. Further, we distinguish
the cost of *validating* and *applying* transactions, each is its own
independent bucket to capture costs under. This not only matches measurements
better, but also allows us to take advantage of the commutative nature of
validation.

### I/O Cost

We wish to track 5 I/O dimensions:

1. Static reads (DB reads that can be executed ahead of time). Measured in
   number of 4k block reads.
2. Dynamic reads (DB reads that must be executed at run-time). Measured in
   number of 4k block reads.
3. Storage (DB writes of fresh, persistent data). Measured in bytes of disk
   utilization caused.
4. Churn (DB *overwrites*, that is, writes that replace prior data). Measured in
   bytes of disk utilization modified.
5. Network/consensus usage (transaction size). Measured in bytes.

Note that first 4 can be tricky to measure precisely. We will generally adopt a
simplified model on how the database translates into disk accesses when
estimating these, refining this model should be a future work.

This model will not be specified here, but will instead be closely coupled to
our storage solution, using the graph structure of the storage tree as a proxy
for disk I/O.

Note also that we assume all reads are random, and all writes are sequential.
This is also a simplification, but maps reasonably onto practice. To support
this model, we therefore further need benchmarks of *batched* random reads (for
the static reads), *sequential* random reads (for the dynamic reads), and
sequential writes, ideally as performed by a sufficiently large model database.
Note that these only account for the *time* aspect of this, while the latter
three measurement (including churn, which *temporarily* increases storage
requirements) measure in part something unrelated to latency.

### Compute Cost 

Compute cost is naively simply a measure of how long one of the computations
takes. It is complicated by some operations being able to take advantage of
parallelism, and some not.

Ideally, Midnight should be able to fully parallelise its operations regardless
of atomic parts being parallelisable, by parallelising transactions themselves.
This is unlikely to be the case at launch, however, as this requires building
up commutative buckets of transactions for the application phase, which is not
a solved problem.

Instead, we assume that the *validation* phase is parallelised, and that the
*application* phase is sequential. Further, this document assumes that the only
operation that is individually parallelised is proof verification, which only
occurs in the validation phase. Effectively, this means that we can *treat
everything as if it were single-threaded*, because it either *is* (for
application), or the multi-threading is at the macro-level (for validation).

Therefore, our compute costs are simply *single-threaded* benchmarks.

### What is costed

For both storage and compute, the following candidates are either measured or
manually derived from the storage model:

- All [../apis-and-common-types/onchain-runtime/README.md](onchain VM) instructions
    - Executed against random inputs, of varying sizes where the instruction has an input-size dependency
    - Where instructions apply to different data types, each potential input data type is costed separately
- Proof verification (measured as a linear function of public input length)
- A constant and/or linear overhead per:
    - Intent
    - Dust action (separately for each type)
    - Contract action (separately for each type)
    - Zswap input/output/transient
    - Unshielded input/output

Where curves are measured, a linear regression on at least 10 points is performed.

### Where and how things are measured

In order to enable hardware-level decentralisation of Midnight, the cost model
should not be greatly biased in favour of any specific ISA, or hardware
manufacturer. This is not to say we have no requirements -- this document does
not suggest supporting old hardware, and in particular suggests that I/O
measurements should assume an NVMe SSD.

In order to achieve this, we suggest at least four benchmark machines, evenly
split across `aarch64` and `x86_64`:

- An AMD Ryzen machine
- An Intel machine
- An Apple silicon Mac
- An ARM processor Linux machine (snapdragon cloud machine? raspberry pi?)

Each would be clamped to a single core when running benchmarks.

Note that this should be treated as a basket of reference machines, which may
be modified with time, and in practice initial work may use developer's
machines while the 'official' basket is being determined.

The measurements themselves should be automated and easy to re-run / reproduce
(up to measurement error).

For the CPU performance measurements, values are normalized around proof
verification time, as this is expected to be the dominant cost. The normalized
compute weights are then averaged between the different machines, and these
averages are used as the 'bare' costs.

For I/O performance measurements, the raw numbers are instead averaged, as it
is less reasonable to set minimum performance requirements for an SSD than for
a CPU.

For each measurement dimension, the maximum deviation in both negative and
positive direction from the average thus derived is also tracked. This
highlights both potential points of attack (in the negative direction), as well
as potential points where users overpay (in the positive direction).

### Weighting fees and limits

Some ground assumptions:

- We want to target a block time of 6s
- We want *application* and *verification* of a fresh block to have a budget of at most 1s 
- We require 4 CPU cores

We will assume that verification and then application are optimally pipelined:
Work to fetch the data needed for the application phase beings during the
verification phase, and the compute never exceeds the data that has been
fetched. As proof verification is assumed to dominate, this is likely to be true.

Therefore, we have the 1s budget essentially independently for I/O *reads* and
for compute. I/O *writes* have more leniency, as they don't need to fit within
this budget. These are far more likely to be limited by a concern about disk
storage than speed however -- constantly writing will fill up any disk very
quickly. As a result, we want an overall limit on bytes *written* per block.
For *churn* this can be a fair bit higher, as we can rely on eventually being
able to forget this.

Finally, for *dynamic* reads, these will be counted twice: Once as an I/O
operation, as they are still reads to fit within the read budget, and once as a
*compute* operation, as they also block compute.

Concretely, this means that:
- The model will provide an estimated number of 4k reads, both static and
  dynamic, of a transaction, both for the validity check, and for application.
- The static reads are multiplied with the benchmark for batched reads to get a
  time estimate.
- The dynamic reads are multiplied with the benchmark for sequential reads to
  get a time estimate.
- The sum of both estimates for all transactions in a block is subject to a
  limit of 1s.

For writes:

- The model will provide an estimate for the number of bytes written and
  churned in a transaction.
- There is a per block limit set for these, with churned bytes weighted
  fractionally.
- Suggested initial limits (subject to discussion): 20kB writes per block, with
  churn counting weighted 10%.

For transaction size:

- The model provides the transaction size.
- There is a per block limit set for these.
- Suggested initial limits: 200kB.

Finally, for compute, the model provides a normalized compute cost, both for
transaction validty, and for transaciton application. The validity cost is
divided by the number of CPU cores required, as it is assumed to be done in
parallel, and the weighted sum is then scaled by the real performance of the
*weakest* baseline machine to give a synthetic compute time. The cost of
dynamic reads is added to this, as compute will be blocked on these. This
synthetic compute time is limited to 1 second per block.

The fees to be paid (per transaction) are calculated as the sum of:
- The *maximum* of:
    - (Scaled) total synthetic I/O read time, normalized to the limit of 1s
    - (Scaled) total synthetic compute time, normalized to the limit of 1s
    - (Scaled) total block usage, normalized to the limit
- (Scaled) total synthetic I/O bytes written, normalized to the limit

These are all *scaled* -- their values are not used directly, but first
compared with recent *block utilization*, targeting 50% utilization in every
category. This scaling in each of the four dimensions uses the (exponentially
weighted) average of the last day's (unscaled) block fullness data in the same
dimension, and determines the scaled value based on the fee adjustment curve,
increasing the value if it's over 0.5, decreasing it otherwise.

The maximum of the first three values is in composite (summed for all
transaction in a block) the 'block utilization rate', and is scaled by one fee
factor. The final value is the 'block storage rate', and is scaled by a
separate factor. Both modifiable ledger parameters. Initially, it is suggested
they both be set to 10 Dust (implying that 20 Dust is sufficient to fully
saturate a block). This is hard to judge correctly, except that:

- 1/10th of this limit is likely around the cost of a basic transaction, and
  should therefore be affordable
- The question then becomes: How little Night should a user own for their Dust
  to, at cap, be able to transact at all?
- 0.1 Dust seems a reasonable optimistic compromise: Not a lot, but not a
  trivial amount either.

## Desired Result

The network to neither fall over at the first breeze, nor lie unused due to
prohibitive cost.
