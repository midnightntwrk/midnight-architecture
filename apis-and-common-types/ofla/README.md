# $f(a) = O(|f| \log |a|)$ (Ofla)

This document describes the Ofla program format, as represented in JavaScript,
on-the-wire binary, and in prime fields for proof verification. It further
describes the data structures stored in Ofla, and how they may be represented,
and argues the primary theorem, stated in the title of the document.

This document superceeds the [Micro ADT Language](../../proposals/0004-micro-adt-language.md).

__Status__: Draft

__Version__: 1.0

## Data types

This document will make use of the [Field-Aligned
Binary](../field-aligned-binary) format, and data types represented in it.  This
document defines the `OflaProgram` and `OflaAdt` data formats, and defines
execution of `OflaProgram`s on `OflaAdt`s.

### ADTs

The `OflaAdt` data type is defined as a disjoint union of the following types:
* `Null`: a missing or unit value, it's sole value being `null`.
* `Cell`: memory cell containing a single FAB `Value`
* `Pair`: memory cell containing a pair of Ofla ADTs.
* `Set`: set of FAB values.
* `Map`: key-value map from FAB values to Ofla ADTs.
* `Array(n)` for `n <= 32`: fixed-length array of Ofla ADTs
* `BoundedMerkleTree(n)` for `n <= 32`: depth-`n` Merkle tree of FAB values.
* `SortedMerkleTree`: an ordered Merkle tree of arbitrary depth of FAB values.

Note that Ofla ADTs appear only in positions where they are *readable*, and where they are not used for indexing.

#### Merklization

ADTs may be Merklized as a node whose first child is a tag identifying the type, and whose second is:
* `Null`: A blank leaf.
* `Cell`: A leaf in a Merkle tree.
* `Pair`: A node in a Merkle tree.
* `Set`: A `SortedMerkleTree` of the set.
* `Map`: Like a `SortedMerkleTree` of key-value `Pair`s, if this were to accept Ofla ADTs.
* `Array(n)`: Like a `BoundedMerkleTree(ceil(log(n)))` of the same fields, if this were to accept Ofla ADTs.
* `BoundedMerkleTree(n)` and `SortedMerkleTree` as themselves.

#### On-the-wire representation

TODO

#### Composite ADTs

We will want to present some ADTs that can easily be constructed from the above separately:
* `List`
* `HistoricMerkleTree(n)`
* others?

Where possible with a small, constant number of operation to construct new
datatypes, useful for users, from existing ones, these should be implemented as
a language feature rather than an Ofla ADT.

### Programs

On `OflaProgram` is a sequence of `OflaOp`s. Each `OflaOp`
consists of an opcode, potentially followed by a number of arguments depending
on the specific opcode. For read operations, the operation may return a result
of some length. `OflaProgram`s can be run in two modes: evaluating and
verifying. In verifying mode, operation results are expected as arguments, and
are checked for correctness instead of being output.

`OflaPrograms` run on a stack machine with a stack of
`OflaAdt`s, guaranteed to have exactly one item on the stack to start. Each
`OflaOp` has a fixed effect on the stack, which will be written as `-{a, b} +{c,
d}`: consuming items `a` and `b` being at the top of the stack (with `a` above
`b`), and replacing them with `c` and `d` (with `d` above `c`). The number of
values here is just an example. We write `[a]` to refer to the value stored in
`a`, and `[[a]]` to refer to the FAB value stored in the `Cell` at `[a]`.

| Name     | Opcode | Stack             | Arguments      | Results        | Description |
| :---     | -----: | :-----            | -------------: | -------------: | ----------- |
| `noop`   |   `00` | `-{}     +{}`     |              - |              - | nothing |
| `dup`    |   `01` | `-{a}    +{a, a}` |              - |              - | duplicates `a` |
| `copy`   |   `02` | `-{a}    +{b}`    |              - |              - | sets `[b] := [a]` |
| `move`   |   `03` | `-{a, b} +{}`     |              - |              - | sets `[a] := [b]` |
| `pop`    |   `04` | `-{a}    +{}`     |              - |              - | removes `a` |
| `swap`   |   `05` | `-{a, b} +{b, a}` |              - |              - | swaps the top two items on the stack |
| `branch` |   `06` | `-{a}    +{}`     |      `n: uint` |              - | if `[a]` is non-empty, skip `n` operations. The skipped operations *must* have a net-zero effect on the stack. |
| `read`   |   `07` | `-{a}    +{}`     |              - |     `[a]: Adt` | returns `[a]` |
| `write`  |   `08` | `-{}     +{a}`    |     `[a]: Adt` |              - | sets `[a]` |
| `add`    |   `09` | `-{a}    +{b}`    |       `c: Adt` |              - | sets `[b] := [a] + c`, where addition is defined below |
| `sub`    |   `0a` | `-{a}    +{b}`    |       `c: Adt` |              - | sets `[b] := [a] - c`, where subtraction is defined below |
| `lt`     |   `0b` | `-{a, b} +{c}`    |              - |              - | sets `[c] := [a] < [b]` |
| `eq`     |   `0c` | `-{a, b} +{c}`    |              - |              - | sets `[c] := [a] == [b]` |
| `type`   |   `0d` | `-{a}    +{b}`    |              - |              - | sets `[b] := typeof([a])` |
| `size`   |   `0e` | `-{a}    +{b}`    |              - |              - | sets `[b] := size([a])` |
| `member` |   `0f` | `-{a, b} +{c}`    |              - |              - | sets `[c] := has_key([a], [b])` |
| `idx`    |   `10` | `-{a}    +{b}`    |     `c: [Adt]` |              - | sets `[b] := fold_left(c, [a], lambda adt val: adt.get(val))` |
| `dyidx`  |   `11` | `-{a, b} +{c}`    |              - |              - | sets `[c] := [a].get([b])` |
| `new`    |   `12` | `-{a}    +{b}`    |              - |              - | sets `[b] := new typeof([a])` |
| `null`   |   `13` | `-{}     +{a}`    |              - |              - | sets `[a] := null` |
| `and`    |   `14` | `-{a, b} +{c}`    |              - |              - | sets `[c] := [a] & [b]` |
| `or`     |   `15` | `-{a, b} +{c}`    |              - |              - | sets `[c] := [a] | [b]` |
| `neg`    |   `16` | `-{a}    +{b}`    |              - |              - | sets `[b] := ![a]` |
| `log`    |   `17` | `-{a}     +{}`    |              - |              - | outputs `[a]` as an event |

In the description above, the following short-hand notations were used. Where
not specified, result values are placed in a `Cell`, and encoded as FAB values.

* `a + b`, `a - b`, or `a < b` (collectively `a op b`), for applying `op` on
  the contents of `Cell`s `a` and `b`, interpreted as 64-bit unsigned integers,
  with alignment `b8`.
* `a == b` for checking two `Cell`s for equality, at least one of which must
  contain at most 64 bytes of data (sum of all FAB atoms).
* `a & b`, `a | b`, `!a` are processed as boolean and, or, and not over the
  contents of `Cell`s `a` and maybe `b`. These must encode 1 or 0.
* `typeof(a)` returns a tag representing the type of an ADT:
  * `Cell`: 0
  * `Null`: 1
  * `Pair`: 2
  * `Set`: 3
  * `Map`: 4
  * `Array(n)`: 5 + n * 32
  * `BoundedMerkleTree(n)`: 6 + n * 32
  * `SortedMerkleTree`: 7
* `size(a)` returns the number of non-null entries is a `Set` or `Map`, `n` for
  an `Array(n)` or `BoundedMerkleTree(n)`.
* `has_key(a, b)` returns if `b` is in the `Set` `a`, or `b` is a key to a
  non-null value in the `Map` `a`.
* `new ty` creates a new instance of an ADT according to the tag `ty` (as
  returned by `typeof`):
  * `Cell`: Containing the empty value.
  * `Null`: `null`
  * `Pair`: A pair of `Null`s
  * `Set`: The empty set
  * `Map`: The empty map
  * `Array(n)`: An array on `n` `Null`s
  * `BoundedMerkleTree(n)`: A blank Merkle tree
  * `SortedMerkleTree`: A blank Merkle tree
* `a.get(b)` retrieves the sub-item indexed with `b`. For different `a`:
  * `a: Pair`, if `b == 0`, return the first item, if `b == 1`, the second.
  * `a: Map`, the value stored at the key `b`
  * `a: Array(n)`, the value at the index `b` < n

Creating new map entries, or removing existing entries is done by indexing to
them, and setting them to or from `null`. See examples below.

State shapes:

```
Midnight = Vector<zswap: ZSwap, contract: Lares>
ZSwap = Vector<commitments: MerkleTree<32>, nullifiers: Set<Nullifier>, past_roots: Set<Field>>
Lares = Map<ContractAddress, Contract>
Contract = Vector<contract_state: Any, operations: Map<Bytes, VerifierKey>>

Context = Vector<block_context: BlockContext, self: ContractAddress, new_commitment_indicies: Map<CoinInfo, Field>>
BlockContext = Vector<parent: Maybe<BlockContext>, dirty_rand: Bytes<32>, time_hint: Unsigned Integer<64>>

ContractWithContext = Vector<contract_state: Any, operations: Map<Bytes, VerifierKey>, context: Context>
```

When contract calls are processed, they start with a stack with a single `ContractWithContext`.

Ex. say we have (cells implicit)

```
ledger {
  foo: Foo,
  bar: Map[Bar, Baz],
}
```

Examples:
* `[dup, idx 1 <bar lit>, incr 1]` for `ledger.bar[<bar lit>].increment(1)`
* `[dup, idx 1 <bar lit>, write <baz lit>, move]` for `ledger.bar[<bar lit>] = <baz lit>`
* `[dup, idx 1 <bar lit>, null, move]` for `ledger.bar.remove(<bar lit>)`
