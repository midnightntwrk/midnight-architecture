# Properties of Midnight Transactions

At this time, we do not have formal security proofs for Midnight's behaviour.
However, this document strives to *state* theorems we expect to hold about
Midnight transactions, and to provide an argument for why we believe these to
be true.

## Balance Preservation

> **Theorem 1 (Balance Preservation).** A transaction does not modify the total
> amount of funds in the system, with the following exceptions:
> - Contract *mint* operations create a corresponding amount of funds in a
>   token type specific to that contract.
> - Dust balances are *not* preserved.
> - Transactions with a net positive balance will be paid into the treasury.

Importantly, the total in balance preservation is between the utxo sets, and
the unshielded token balances held by contracts. This holds for both unshielded
and shielded tokens, but is not observable for the shielded ones.

*Correctness Argument.* The transaction balancing check tests that transactions
are positive value, which excess value going to the treasury. Therefore, it is
sufficient to show that the value of a transaction is accurate, and not counted
incorrectly at any point. This is provided by the following enforced checks:

- The unshielded balance computation ensuring that the sum of inputs minus the
  sum of outputs is positive
  - This matching exactly to inputs that are removed from the state, and
    outputs that are added to the state ensuring this correctly reflects movement
    in the state
  - Contract inputs being subtracted from the balance, and contract outputs
    being added to the balance, exactly matching the delta to the contract
    balances
- As each check is enforced on a per-intent basis, regardless of the
  combination of intents that succeeds, the applied changes must be balanced.
- For the shielded portion, for (visible) contract balances, as for unshielded
  contract balances.
- For the shielded portion, a similar argument to applying inputs and outputs
  applies.
  - In this case, the check is replaced with the opening of the Pedersen
    commitment to the expected balance.
  - The integrity and correctness of this commitment is provided by the
    zero-knowledge proof.
  - The impossibility to interfere between different token types, is given by
    the hardness of discrete logarithm.
  - The impossibility to interfere with the `Intent` Pedersen commitment is
    given by the Fiat-Shamir transform, guaranteeing the use of the generator,
    and the hardness of discrete logarith.

## Binding

> **Theorem 2 (Transaction Binding).** A transaction, once assembled, can only
> be disassembled by the user that first assembled it. No part of the
> transaction can be meaningfully used in another transaction, without
> including all other parts with it.

## Infragility

> **Theorem 3 (Infragility).** For a *defensively created* transaction `t`, a
> malicious user cannot cause `t` to fail by merging a malicious transaction
> `m` with `t`, except for the following ways:
> - If the malicious user could replicate the failure by first getting a
>   malicious transaction `m'` accepted, and then applying `t`.
> - If, while `merge(m, t)` fails, `t` itself may still subsequently succeed.

By *defensively created*, this theorem explicitly means that the segment IDs of
the intents in `t` count from `1`; that is, for some natural `n`, all intents
`0 < m < n` are present in `t`. This prevents a malicious user from
'frontrunning' any of the intents in `t`, preventing a class of relatively
acceptable failures.

## Causality

> **Theorem 4 (Causality).** If a transaction includes a contract call from `A`
> to `B`, then `A` succeeding must imply `B` succeeding.

## Self-determination

> **Theorem 5 (Self-determination).**
> 1. A user cannot spend the funds of another user. No contract can spend funds
>    of a user.
> 2. A contract can only be modified according to the rules of the contract.
