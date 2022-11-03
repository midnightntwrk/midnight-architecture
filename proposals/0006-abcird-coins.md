# Proposal 0006: Coins in Abcird

Smart contracts need to interact with the native currency. What does this actually look like?

# Problem Statement
Any smart contract language worth its salt can talk about tokens native to the
smart contract platform. For instance, in Ethereum, any call has a value
attached to it, which is crucial for a smart contract to receive and send funds.
In Midnight, this is complicated by two factors:
* We do not have an account-based native currency, but a private UTXO-like one.
* We have multiple native currencies.

# Proposed Changes

This proposal is primarily to, aside from having support for `claim_zswap_note`
and `claim_zswap_nullifier` kernel calls discussed in the [Micro ADT Language
Proposal](./0004-micro-adt-language.md), and private queries to create new ZSwap
inputs/outputs as hinted at in the [Transaction Structure
Proposal](./0005-transaction-structure.md), leave most coin handling to Abcird
user-space, and specifically to a standard library built in it.

This has the immediate advantage of requiring no changes to our computational
model, except the development of a small standard library for handling coins. It
has the disadvantage of making bad contract design easy: A contract can simply
ignore coins it is sent, effectively burning them. Over time, it is likely that
we will greatly strengthen static analysis of contracts storing and processing
coins they receive.

## The Types: `CoinInfo` & co.

At the core of handling coins are the `CoinInfo` and `QualifiedCoinInfo` types,
defined as follows:

```
struct CoinInfo {
  nonce: ZSwapNonce;
  color: Field;
  value: Field;
}

struct QualifiedCoinInfo {
  nonce: ZSwapNonce;
  color: Field;
  value: Field;
  pk: Either<ZSwapCoinPublicKey, ContractAddress>;
  mt_index: Field;
}
```

The `nonce` and `mt_index` components are technical parts. `color` differentiates
between the different coin colors, and `value` gives its value.  Both are bounded
by `2^64`. We assume at least one predefined constant for `color`,
`MIDNIGHT_VALUE_TOKEN`, and a function
`circuit contract_color(addr: ContractAddress): Field` for deriving colors from
contract addresses in a collision-resistant way.

## General Flow

Transition functions should receive `CoinInfo` values as inputs, and test that
they match their desired properties: That they have sufficient `value`, and are
of the right `color`. If this is the case, the transition function should run a
`receive_coin(...)` library function on the `CoinInfo`, which enforces some
validity criteria, and runs `claim_note` for a note computed from it, and the
result of `self`.

Then, the `CoinInfo` is either directly spend via the `[partial_]spend_immediate(...)`
library function, or stored in the contract's state via `insert_coin`,
`write_coin`, or `push_front_coin`. These are variants of `insert`, `write`, and
`push_front` for containers over `QualifiedCoinInfo` that accept `CoinInfo`
instead of its larger cousin. This allows the public oracle to fill in the gaps,
including the volatile Merkle tree index. These can later be retrieved, and
spent with a `[partial_]spend_coin(...)` library call (this will fail if done in the same transaction!).
`partial_spend_coin` and `partial_spend_immediate` will also produce a new
`CoinInfo` that can be treated as a pre-validated additional input coin.

## The Basics: `{claim,create}_zswap_{note,nullifier}`, and `mint` calls

`claim_zswap_{note,nullifier}` link a note or nullifier in the same transaction to this contract call, ensuring:
* For `claim_zswap_note`, that the same note isn't used in multiple calls
* For `claim_zswap_nullifier`, that the spending of the nullifier was authorised by the calling contract

By contrast, `create_zswap_{note,nullifier}` are private queries that instruct
the transaction assembly to add new parts to the transaction under construction.
* For `create_zswap_note(ci: CoinInfo, pk: Either<ZSwapPublicKey,
  ContractAddress>)` a new ZSwap Output is created from the coin info and the
  target `pk`.
* For `create_zswap_nullifier(ci: QualifiedCoinInfo)`, a new ZSwap Input is
  created from the given coin.

`mint(x)` is an odd-one out. It changes the balancing equation of the
transaction, counting as if an additional input with value `x` and color
`contract_color(self())` were present.

## The Composites: Library for receiving, sending, and minting funds.

* `receive_coin(ci: CoinInfo): Void`
  Checks if `ci` is valid, and runs `claim_zswap_note(ci, self())`
* `spend_immediate(ci: CoinInfo, pk: Either<ZSwapPublicKey, ContractAddress>): CoinInfo`
  * Runs `create_zswap_nullifier(ci')` for `ci' = ci /
    { pk = self(); mt_index = 0; }`. This gets recognised as a spend from within
    the existing transaction.
  * Samples a new `nonce` and `ci'' = ci / { nonce = nonce; }` runs `create_zswap_note(ci'', pk)`
  * Runs `claim_zswap_note(compute_note(ci'', pk))`.
  * Returns `ci'`
* `partial_spend_immediate(ci: CoinInfo, pk: Either<ZSwapPublicKey, ContractAddress>, val: Field): WithChange<CoinInfo>`
  * As in `spend_immediate`, except that `ci'' = ci / {nonce = nonce; value = val; }`
  * Asserts `val <= ci.value`
  * Also samples `nonce'`, and `ci''' = ci / { nonce = nonce'; val = ci.value - val; }`
  * Runs `create_zswap_note(ci''', self())` and `claim_zswap_note(compute_note(ci''', self()))`.
  * Returns `ci'', ci'''`
* `spend_coin(ci: QualifiedCoinInfo, pk: Either<ZSwapPublicKey, ContractAddress>): CoinInfo`
  As in `spend_immediate`, but with `ci' = ci`.
* `partial_spend_coin(ci: QualifiedCoinInfo, pk: Either<ZSwapPublicKey, ContractAddress>, val: Field): WithChange<CoinInfo>`
  As in `partial_spend_immediate`, but with `ci' = ci`.

# Desired Result
It should be possible to write contracts that privately or publicly hold native currencies.
