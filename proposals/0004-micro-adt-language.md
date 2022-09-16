# Proposal 0004: Micro ADT language

This proposal suggests a language to adopt for public oracle states and queries
for the 2022 workshop. This should be treated as a minimum viable language,
with all intentions to extend this in future.

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

Note: All ADTs and queries should be taken as a *preliminary specification*.
Expect changes, but for now, they should serve to work against, not just as a
sketch of what could be!

I propose supporting the following ADTs and public oracle queries:

ADTs, where `0 < n <= 64` is a size parameter, and `T`, `K`, and `V` are
*either* Abcird types, *or* opaque serialized data (from the ledger's point of
view).
* `Counter`
* `Cell<T>`
* `Set<T>`
* `Map<K, V>`
* `List<T>`
* `[Historic]MerkleTree<n, T>` (The difference between a `HistoricMerkleTree`
  and a `MerkleTree` is that the former permits proofs against past states—as
  is the case in Zcash; this is desirable in cases where the Merkle tree is
  monotonically growing—while the latter does not)

A contract's state would consist of a mapping of strings to ADTs, and a
contract's state's type consist of a mapping of strings to ADT types.

I propose that each ADT has a default value which it is initialized to, and can
be reset to at any time. This default value should be:
* 0 for `Counter`
* The natural empty collection for `Set<T>`, `Map<K, V>`, `List<T>`, `[Historic]MerkleTree<n, T>`
* The default of `T` for `Cell<T>`
  * For `T` being an Abcird type, this should the value represented by all in-memory zeroes.
  * For `T` being a serialized TypeScript type, this should be an empty
    bitstring (note that the TypeScript side needs to be careful with
    deserialization anyway, as no structure can be enforced on-chain).

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
* `HistoricMerkleTree<n, T>`
  * `reset_history(field)`
* Kernel
  * `claim_zswap_nullifier(nul: Nullifier)`
  * `claim_zswap_note(note: Note)`
  * `claim_contract_call(addr: ContractAddress, entry_point: Bytes, comm: HomomorphicCommitment)`
  * `mint(amount: uint)`

A number of operations that are *not* public oracle queries should be available
on an API level, either for access by dApps, or to expose directly as *private*
oracle queries. These are:

* Iterators over `List<T>`, `Map<K, V>`, and `Set<T>`. Note that due to the
  nature of Merkle trees, their content is cryptographically hidden and can't
  be iterated over.
* In `[Historic]MerkleTree<n, T>`s:
  * `index_last_inserted(field) -> uint`
  * `path_to_index(field, index: uint) -> MerklePath<n>`
  * `find_element(field, elem: T) -> Maybe<MerklePath<n>>`

The ledger would own the data representation of queries, query types, ADTs,
and ADT types.

In Abcird, these will be exposed on a high-level by a) declaring a contract's
`Ledger` type (as a typescript object type of ADT types), and b) allowing calls
to this, though a `ledger` pseudo-variable (as `statement` external calls), or
(potentially, pending discussions on private oracle structure) a `local.ledger`
pseudo-variable (as `witness` external calls).
Finally, an `initialize` circuit (though in practice this need not be compiled)
captures the calls made to initialize the ledger state from its default, for
instance, by setting administrative keys.

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
  ledger.field3.write(ledger.field1.lookup(5).value.baz);
  ledger.field2.check_root(
    merkle_path_root(
      local.ledger.field2.find_element(
        local.ledger.field1.lookup(3))));
}

circuit initialize() {
  ledger.field3.write(true);
}
```

Note that the `ledger.field.operation(arguments)` notation is likely
syntactic sugar for something like `ledger$operation("field", arguments)`,
which corresponds to the query `operation("field", arguments)`, with `ledger`
vs (the potential) `local.ledger` distinguishing if this query is a public oracle or private
oracle query.

Some additional syntactic sugar is desirable but optional:
* `x = y; => x.write(y);`
* `y => y.read()` (in expression contexts)
* `x[y] = z; => x.insert(y, z); OR x.insert_index(y, z);` (Depending on if `x`
  is a `Map` or `[Historic]MerkleTree`)
* `x[y] => let r = x.lookup(y) in assert "primitive map access failed" r.is_some; r.value` (in expression contexts—yes, this is messy because of the `Maybe`, and needs more work)
* `x += y; OR x -= y; => x.increment(y); OR x.decrement(y);`

On the Abcird side, non-Abcird types stored in ADTs would be represented as
`Opaque<TypeScriptType>`, which the typescript side would instead see as just
`TypeScriptType`. Such types **must** implement a canonical serialization
format, which is used to represent them on the ledger side, as well as being
used to derive their on-the-wire representation in ZKIR.

# Desired Result

We can start implementing real public oracles for Abcird/Lares.
