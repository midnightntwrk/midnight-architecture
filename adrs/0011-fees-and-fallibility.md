# 11. Fees and Fallibility

## Status

proposed

| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | 2023-05-17                                                                                                                       |
| deciders  | Thomas Kerber, Jon Rossie |
| informed  | Kent Dybvig, Joseph Denman |
---

## Context and Problem Statement

We need to charge fees for transactions to protect against DoS attacks. It is
desirable for the cost of operations to be *predictable*, both to ensure that
transactions do not fail due to insufficient fees being available, and to
ensure that users do not pay more than they expected.

Expensive-to-validate transactions need to pay fees *before* executing some of
their processing, which might lead to such transactions failing, despite paying
their fees. We want to avoid this as far as possible.

## Decision Drivers

* We must prevent DoS attacks
* Users should not pay for failed transactions (when possible)
* Users should be able to accurately estimate how much they will pay for successful transactions 

This decision influences, and is influenced by, the choice of on-chain
language. It is made *before* this is finalized, but with a direction in mind.

## Considered Options

We consider two dimensions of options:

### Fee predictability

#### Option 1. Gas-based

Users pay an execution budget up-front, and are refunded any remaining budget
after a successful transaction. This is what is used by Ethereum.

Advantages:
* Simple, familiar model
* You only pay for what you use (in successful transactions)
Disadvantages:
* Incentivizes overpaying to not risk transaction failure
* Total loss of fees if a transaction fails for any reason (see Transaction Structure section)
* We would need to implement a refund mechanism with Zswap

#### Option 2. Computed cost upper bound

Conceptually very similar to 1., but with a on-chain language that lets you
calculate cost upper bounds. That is, you always know a cost which will not be
exceeded. You pay this cost every time, and do not get refunded.

Advantages:
* No transaction failures due to fees
* Highly predictable transaction cost
* No need for runtime book-keeping
Disadvantages:
* You pay for computation you may not use
  * The *network* has to budget for computation it may not use
* Total loss of fees if a transaction fails due to state invalidity (see Transaction Structure section)
* Could be replaced with Option 1 for the same language and cost users less fees in practice.

#### Option 3. Computed cost on declared state size bounds

Conceptually an evolution of 2., but refining the cost to computed over
assertions on a contract's state size. For instance, asserting that a data
structure has less than `2^10` entries, and basing cost calculations on that.

Advantages:
* No transaction failures due to fees
* Highly predictable transaction cost
* Fee payment closer to what is actually used than 2.
* No need for runtime book-keeping
Disadvantages:
* Still some level of inbuilt overpayment
* Total loss of fees if a transaction fails due to state invalidity (see Transaction Structure section)
* Option 1 still has lower fees in practice.

### Transaction Structure

#### Option 1. All-or-nothing

A transaction either succeeds, or it does nothing.

Advantages:
* Users do not pay for failing transactions.
* Transaction behaviour is very predictable.
Disadvantages:
* Transaction execution needs to be severely limited to prevent DoS attacks.

#### Option 2. Fee payment, then contracts

A transaction first covers its fees, then attempts to execute contract calls.
If these fail, the fee payment persists regardless. This is the setting of
Ethereum.

Advantages:
* No (theoretical) limit on contract execution budgets
Disadvantages:
* Fee payment will always be forfeit if a transaction fails for any reason
* Transaction behaviour is much less predictable, as any condition that could
  cause a transaction to fail may lead to loss of funds.

#### Option 3. Guaranteed / fallible

A transaction is split into two sections: Guaranteed execution and fallible
execution. The guaranteed execution section covers the fees for both, but also
has a limited (in the same sense as Option 1) budget for use in contract
execution. The transaction is applied in two atomic steps, first applying the
guaranteed part, then applying the fallible part.

Advantages:
* Many contracts will not need a fallible part, inheriting the advantages of Option 1.
* No (theoretical) limit on contract execution budgets, although high-budget
  contracts may inherit the disadvantages of Option 2.
* Interplays well with predictable fees Option 3: The checks of state size
  assertions can be performed in the guaranteed section.
* Allows contract authors to front-load limited state assertions into the
  guaranteed section, to ensure that the fallible sections cannot fail in
  practice. 
Disadvantages:
* Fee payments will still be forfeit if a fallible part fails.
* Predictability of transaction behaviour depends on contract design.
* Contracts have to draw the line between guaranteed/fallible interaction; how
  is this exposed to the developer?

#### Option 4. Multi-stage

As Option 3, with with `n` stages, each stage paying the fees for the next
(except the first stage, which pays for the first two in exchange for limited
budget).

Advantages:
* Generalizes Option 3.
Disadvantages:
* No clear practical benefit over Option 3.
* Further complicates programming model.

## Decision Outcome

Guaranteed / fallible with declared cost with an upper bound on state size.
Combined, these give us transactions that have highly predictable fees and
behave very predictably if contracts are implemented to take advantage of the
design. With poor transaction design, this will behave more like the
"fee-payments then contracts" with "computed cost upper bounds" options.

## Validation

We should implement an example application that deliberately exceeds reasonable
"guaranteed" execution bounds, and shows the different failure modes dependant
on contract design.
