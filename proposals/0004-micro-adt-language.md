# Proposal 0004: Micro ADT language

This proposal suggests a language to adopt for public oracle states and queries
for the 2022 workshop. This should be treated as a minimum viable language,
with all intentions to extend this in future.



This is a template for writing new Midnight Architecture Proposals.  We want
this template to be lightweight, so that it does not impede the process of
capturing the proposals, and we to evolve this template over the time, as we
figure out the process of proposing changes to our architecture.

# Problem Statement

In light of [ADR-0005](../adrs/0005-public-oracle-language-direction.md)
settling on the use of ADTs for public oracle queries, there is a need to
settle on which ADTs to support, and how these should be presented in three
sides:

* TypeScript
* Ledger
* Abcird

This proposal focuses on the ledger and Abcird sides, and aims for the Abcird
side to use a subset of TypeScript making it suitable from that side as well.

# Proposed Changes

I propose supporting the following ADTs and public oracle queries:

ADTs, where `1 < n <= 64` is a size parameter, and `T`, `K`, and `V` are
*either* Abcird types, *or* opaque serialized data (from the ledger's point of
view).
* `Counter`
* `Cell<T>`
* `Set<T>`
* `Map<K, V>`
* `List<T>`
* `[Historic]MerkleTree<n, T>` (The difference between a `HistoricMerkleTree`
  and a `MerkleTree` is that the former permits proofs against past states,
  while the latter does not)

A contract's state would consist of a mapping of strings to ADTs, and a
contract's state's type consist of a mapping of strings to ADT types.

I propose supporting the following queries, where `field` is a key in the
contract:
* `reset_to_default(field)`
* `Counter`
  * `read(field) -> int`
  * `less_than(field, threshold: int) -> boolean`
  * `increment(field, amount: uint)`
  * `decrement(field, amount: uint)`
* `Cell<T>`:
  * `read(field) -> T`
  * `write(field, value: T)`
* `Set<T>`:
  * `is_empty(field) -> boolean`
  * `size(field) -> uint`
  * `member(field, elem: T) -> boolean`
  * `insert(field, elem: T)`
  * `remove(field, elem: T)`
* `Map<K, V>`:
  * `is_empty(field) -> boolean`
  * `size(field) -> uint`
  * `member(field, key: K) -> boolean`
  * `lookup(field, key: K) -> Maybe<V>`
  * `insert(field, key: K, value: V)`
  * `insert_default(field, key: K)`
  * `remove(field, key: K)`
* `List<T>`:
  * `head(field) -> Maybe<T>`
  * `pop_front(field)`
  * `push_front(field, value: T)`
  * `length(field) -> uint`
* `[Historic]MerkleTree<n, T>`
  * `check_root(field, root: MerkleTreeDigest) -> boolean`
  * `is_full(field) -> boolean`
  * `insert(field, item: T)`
  * `insert_index(field, item: T, index: uint)`
  * `insert_index_default(field, index: uint)`
  * (in private queries only) `index_last_inserted(field) -> uint`
  * (in private queries only) `path_to_index(field, index: uint) -> MerklePath<n>`
  * (in private queries only) `find_element(field, elem: T) -> Maybe<MerklePath<n>>`
* `HistoricMerkleTree<n, T>`
  * `reset_history(field)`
* Kernel
  * `claim_zswap_nullifier(nul: Nullifier)`
  * `claim_zswap_note(note: Note)`
  * `claim_contract_call(addr: ContractAddress, entry_point: Bytes, comm: HomomorphicCommitment)`
  * `mint(amount: uint)`

The ledger would own the data representation of queries, query types, ADTs,
and ADT types.

In Abcird, these will be exposed on a high-level by a) declaring a contract's
`Ledger` type (as a typescript object type of ADT types), and b) allowing calls
to this, though a `ledger` pseudo-variable (as `statement` external calls), or
through a `local.ledger` pseudo-variable (as `witness` external calls):

```
struct Foo {
  bar: Bytes<32>;
  baz: Boolean;
}
type Ledger = {
  field1: Map<Field, Foo>;
  field2: HistoricMerkleTree<10, Foo>;
  field3: Cell<Boolean>;
}

circuit foo() {
  ledger.field3.write(ledger.field1.lookup(5).baz);
  ledger.field2.check_root(
    merkle_path_root(
      local.ledger.field2.find_element(
        local.ledger.field1.lookup(3))));
}
```

Some syntactic sugar is desirable but optional:
* `x = y; => x.write(y);`
* `y => y.read()` (in expression contexts)
* `x[y] = z; => x.insert(y, z); OR x.insert_index(y, z);` (Depending on if `x`
  is a `Map` or `[Historic]MerkleTree`)
* `x[y] => x.lookup(y)` (in expression contexts)
* `x += y; OR x -= y; => x.increment(y); OR x.decrement(y);`

On the Abcird side, non-Abcird types stored in ADTs would be represented as
`Opaque<TypeScriptType>`, which the typescript side would instead see as just
`TypeScriptType`. Such types **must** implement a canonical serialization
format, which is used to represent them on the ledger side, as well as being
used to derive their on-the-wire representation in ZKIR.

# Desired Result

We can start implementing real public oracles for Abcird/Lares.
