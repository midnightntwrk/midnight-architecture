# $f(a) = \Theta(\sum_{i \in f} c(i))$ (Teci)

This document describes the Teci program format, as represented in JavaScript,
on-the-wire binary, and in prime fields for proof verification. It further
describes the data structures stored in Teci, and how they may be represented,
and argues the primary theorem, stated in the title of the document.

This document superceeds the [Micro ADT Language](../../proposals/0004-micro-adt-language.md).

__Status__: Draft

__Version__: 1.0

## Data types

This document will make use of the [Field-Aligned
Binary](../field-aligned-binary) format, and data types represented in it.  This
document defines the `TeciProgram` and `TeciAdt` data formats, and defines
execution of `TeciProgram`s on `TeciAdt`s.

### ADTs

The `TeciAdt` data type is defined as a disjoint union of the following types:
* `Null`: a missing or unit value, it's sole value being `null`.
* `Cell`: memory cell containing a single FAB `Value`
* `Pair`: memory cell containing a pair of Teci ADTs.
* `Set`: set of FAB values.
* `Map`: key-value map from FAB values to Teci ADTs.
* `Array(n)` for `n <= 32`: fixed-length array of Teci ADTs
* `BoundedMerkleTree(n)` for `n <= 32`: depth-`n` Merkle tree of FAB values.
* `SortedMerkleTree`: an ordered Merkle tree of arbitrary depth of FAB values.

Note that Teci ADTs appear only in positions where they are *readable*, and where they are not used for indexing.

#### Merklization

ADTs may be Merklized as a node whose first child is a tag identifying the type, and whose second is:
* `Null`: A blank leaf.
* `Cell`: A leaf in a Merkle tree.
* `Pair`: A node in a Merkle tree.
* `Set`: A `SortedMerkleTree` of the set.
* `Map`: Like a `SortedMerkleTree` of key-value `Pair`s, if this were to accept Teci ADTs.
* `Array(n)`: Like a `BoundedMerkleTree(ceil(log(n)))` of the same fields, if this were to accept Teci ADTs.
* `BoundedMerkleTree(n)` and `SortedMerkleTree` as themselves.

#### On-the-wire representation

TODO -- We probably want to represent `Cell`s just as their FAB Value
representation, because of how common they are. Curiousity: We need their
aligned variants for proof verification, but not for transaction application.
How does that affect things?

#### Composite ADTs

We will want to present some ADTs that can easily be constructed from the above separately:
* `List`
* `HistoricMerkleTree(n)`
* others?

Where possible with a small, constant number of operation to construct new
datatypes, useful for users, from existing ones, these should be implemented as
a language feature rather than an Teci ADT.

### Programs

On `TeciProgram` is a sequence of `TeciOp`s. Each `TeciOp`
consists of an opcode, potentially followed by a number of arguments depending
on the specific opcode. For read operations, the operation may return a result
of some length. `TeciProgram`s can be run in two modes: evaluating and
verifying. In verifying mode, operation results are expected as arguments, and
are checked for correctness instead of being output.

`TeciPrograms` run on a stack machine with a stack of
`TeciAdt`s, guaranteed to have exactly one item on the stack to start. Each
`TeciOp` has a fixed effect on the stack, which will be written as `-{a, b} +{c,
d}`: consuming items `a` and `b` being at the top of the stack (with `a` above
`b`), and replacing them with `c` and `d` (with `d` above `c`). The number of
values here is just an example. We write `[a]` to refer to the value stored in
`a`, and `[[a]]` to refer to the FAB value stored in the `Cell` at `[a]`.

| Name     | Opcode | Stack                   | Arguments               | Results        | $\Theta$  | Description |
| :---     | -----: | :-----                  | ----------------------: | -------------: | --------: | ----------- |
| `noop`   |   `00` | `-{}        +{}`        |                       - |              - |       `1` | nothing |
| `dup`    |   `01` | `-{a}       +{a, a}`    |                       - |              - |       `1` | duplicates `a` |
| `copy`   |   `02` | `-{a}       +{b}`       |                       - |              - |       `1` | sets `[b] := [a]` |
| `move`   |   `03` | `-{a, b}    +{}`        |                       - |              - |       `1` | sets `[a] := [b]` |
| `pop`    |   `04` | `-{a}       +{}`        |                       - |              - |       `1` | removes `a` |
| `swap`   |   `05` | `-{a, b}    +{b, a}`    |                       - |              - |       `1` | swaps the top two items on the stack |
| `swap2`  |   `06` | `-{a, b, c} +{c, b, a}` |                       - |              - |       `1` | swaps the top item with one two-down on the stack |
| `branch` |   `07` | `-{a}       +{}`        |               `n: uint` |              - |       `1` | if `[a]` is non-empty, skip `n` operations. The skipped operations *must* have a net-zero effect on the stack. |
| `read`   |   `08` | `-{a}       +{}`        |                       - |     `[a]: Adt` |   `\|[a]\|` | returns `[a]` |
| `write`  |   `09` | `-{}        +{a}`       |              `[a]: Adt` |              - |   `\|[a]\|` | sets `[a]` |
| `add`    |   `0a` | `-{a}       +{b}`       |                `c: Adt` |              - |       `1` | sets `[b] := [a] + c`, where addition is defined below |
| `sub`    |   `0b` | `-{a}       +{b}`       |                `c: Adt` |              - |       `1` | sets `[b] := [a] - c`, where subtraction is defined below |
| `lt`     |   `0c` | `-{a, b}    +{c}`       |                       - |              - |       `1` | sets `[c] := [a] < [b]` |
| `eq`     |   `0d` | `-{a, b}    +{c}`       |                       - |              - |       `1` | sets `[c] := [a] == [b]` |
| `type`   |   `0e` | `-{a}       +{b}`       |                       - |              - |       `1` | sets `[b] := typeof([a])` |
| `size`   |   `0f` | `-{a}       +{b}`       |                       - |              - |       `1` | sets `[b] := size([a])` |
| `member` |   `10` | `-{a, b}    +{c}`       |             `d: uint>0` |              - |       `d` | sets `[c] := has_key([a], [b], d)` |
| `idx`    |   `11` | `-{a}       +{b}`       | `c: [Adt], d: [uint>0]` |              - | `\|c\| + d` |sets `[b] := fold_left(zip(c, d), [a], lambda adt d val: adt.get(val, d))` |
| `dyidx`  |   `12` | `-{a, b}    +{c}`       |             `d: uint>0` |              - |       `d` | sets `[c] := [a].get([b], d)` |
| `new`    |   `13` | `-{a}       +{b}`       |                       - |              - |       `1` | sets `[b] := new typeof([a])` |
| `and`    |   `15` | `-{a, b}    +{c}`       |                       - |              - |       `1` | sets `[c] := [a] & [b]` |
| `or`     |   `16` | `-{a, b}    +{c}`       |                       - |              - |       `1` | sets `[c] := [a] \| [b]` |
| `neg`    |   `17` | `-{a}       +{b}`       |                       - |              - |       `1` | sets `[b] := ![a]` |
| `log`    |   `18` | `-{a}       +{}`        |                       - |              - |       `1` | outputs `[a]` as an event |
| `root`   |   `19` | `-{a}       +{b}`       |                       - |              - |       `1` | sets `[b] := root([a])` |
| `ins`    |   `1a` | `-{a, b}    +{}`        |             `d: uint>0` |              - |       `d` | sets `[a] := insert([a], [b], d)` |
| `inskey` |   `1b` | `-{a, b, c} +{}`        |             `d: uint>0` |              - |       `d` | sets `[a] := insert_key([a], [b], [c], d)` |
| `rem`    |   `1c` | `-{a, b}    +{}`        |             `d: uint>0` |              - |       `d` | sets `[a] := remove([a], [b], d)` |

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
* `has_key(a, b, d)` returns if `b` is in the `Set` `a`, or `b` is a key to a
  non-null value in the `Map` `a`. If the set or map has more than $2^d$
  entries, the operation fails.
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
* `a.get(b, d)` retrieves the sub-item indexed with `b`. For different `a`:
  * `a: Pair`, if `b == 0`, return the first item, if `b == 1`, the second.
  * `a: Map`, the value stored at the key `b`; fails if $\mathrm{size}(a) > 2^d$.
  * `a: Array(n)`, the value at the index `b` < n
* `root(a)` outputs the Merkle-tree root of the `BoundedMerkleTree(n)` or
  `SortedMerkleTree` `a`.
* `insert(a, b, d)`, inserts the value `b` into the `Set`, `SortedMerkleTree`, or `MerkleTree[n]` `a`.
  * If `a` is a `Set` or `SortedMerkleTree`, and $\mathrm{size}(a) > 2^d$, this operation fails.
  * If `a` is a `MekrleTree[n]`, and $n > d$, this operation fails.
* `insert_key(a, b, c, d)`, inserts the value `c` into a map `Map` `a` at key `b`,
  or a `BoundedMerkleTree` `a` at index `b`. Fails if $\mathrm{size}(a) > 2^d$.
* `remove(a, b, d)`, depending on the type of `a`:
  * `Set`: removes the value `b`, fails if $\mathrm{size}(a) > 2^d$.
  * `Map`: removes the entry with key `b`, fails if $\mathrm{size}(a) > 2^d$.
  * `BoundedMerkleTree(n)`: zeroes the index `b`, fails if $n > d$
  * `SortedMerkleTree`: removes the value `b`, fails if $\mathrm{size}(a) > 2^d$.

## Use in Midnight

### State shapes

```
Midnight = Array<zswap: ZSwap, contract: Lares, _, _>
ZSwap = Array<commitments: MerkleTree<32>, nullifiers: Set<Nullifier>, past_roots: Set<Field>>
Lares = Map<ContractAddress, Contract>
Contract = Array<contract_state: Any, operations: Map<Bytes, VerifierKey>, _>

Context = Array<block_context: BlockContext, self: ContractAddress, new_commitment_indicies: Map<CoinInfo, Field>>
BlockContext = Array<parent: Maybe<BlockContext>, dirty_rand: Bytes<32>, time_hint: Unsigned Integer<64>>

MidnightWithContext = Array<zswap: ZSwap, contract: Lares, context: BlockContext, new_commitment_indicies: Map<CoinInfo, Field>>
ContractWithContext = Array<contract_state: Any, operations: Map<Bytes, VerifierKey>, context: Context>
```

NOTE: This is incomplete! Missing coin claims / subcall claims

When contract calls are processed, they start with a stack with a single `ContractWithContext`.

### Examples

Say we have (cells implicit)

```
ledger {
  foo: Foo,
  bar: Map[Bar, Baz],
}
```

* `[dup, idx 1 <bar lit> 0 <heuristic size of ledger.bar>, incr 1]` for `ledger.bar[<bar lit>].increment(1)`
* `[dup, idx 1 0, write <bar lit>, write <baz lit>, ins <heuristic size of ledger.bar>]` for `ledger.bar[<bar lit>] = <baz lit>`
* `[dup, idx 1 0, write <bar lit>, rem <heuristic size of ledger.bar>]` for `ledger.bar.remove(<bar lit>)`

### The ledger as Teci

We can represent all non-verification operations in Midnight through as Teci
programs. The entire history of state changes can be seen as a single valid
Teci program.

* ZSwap spends as: `[dup, idx 0 2, root, read <root>, dup, idx 0 1, dup, write <nullifier>, dup, swap2, swap, member, read 1, ins, write <ciphertext>, log]` (note: will actually need to involve contract address for claiming?)
* ZSwap outputs as: `[dup, idx 0 1, write <commitment>, ins]` (note: will actually need to involve contract address for claiming?)
* Contract deploys as `[dup, idx 1, write <addr>, write <deploy state>, ins]`
* Contract calls as as something more complicated to set up the context (its possible, but not pretty)

Maybe instructions to make these easier/more compact? Especially the contract call + bring over execution context?

### Fees and fee payments

Teci will have a _free execution budget_ dependent on transaction size.
Each Teci instruction $i$ will be associated with a cost $c(i)$, which follows
the asymptotics listed in the table above. Contracts rejected during this free
execution budget are not charged, however contracts rejected after free
execution _are_ charged their entire cost, with the fee payment ZSwap offer
still being applied. A side effect of this: The fee payment ZSwap offer can
only include coins addressed to a contract if the transaction falls entirely
within the free execution budget.

Contracts are executed up to the
free execution budget, and must at this point be sufficient to validate the fee
payment ZSwap offer. After this, fee payment is taken, 

## Questions

* Register-based machine instead? Some issues:
  * Will makes many instructions >1 byte
  * How to have all state modification be a single executing a program? Where
    is the root state pointer kept while operating on a contract state?
* Idea: Stack machine with *2* stacks, each op has 3 bitflags on which stack a particular input/output uses.
  * Leaves 32 operations representable in one byte
  * Easier to use one stack as scratch space (construct what we want to write),
    and the other as target (construct where we want to write it) than using
    swaps and swap2s.
