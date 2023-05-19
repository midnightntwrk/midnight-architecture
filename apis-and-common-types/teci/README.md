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
* `Null`: An empty value.
* `Cell`: memory cell containing a single FAB `Value`
* `Map`: key-value map from FAB values to Teci ADTs.
* `Array(n)` for `n <= 15`: fixed-length array of Teci ADTs
* `BoundedMerkleTree(n)` for `0 < n <= 32`: depth-`n` Merkle tree of FAB values.

Note: we will want to add in a future version:
* `SortedMerkleTree`: an ordered Merkle tree of arbitrary depth of FAB values.

Note that Teci ADTs appear only in positions where they are *readable*, and where they are not used for indexing.

#### Merklization

ADTs may be Merklized (as a separate, base-16 Merkle-Patricia trie, *not* as a binary Merkle tree) as a node whose first child is a tag identifying the type, and whose remaining are:
* `Null`: blank
* `Cell`: A single leaf.
* `Map`: Trees of key-value pairs `(k, v)`, where the path is `0x[H*(k)]`, and the value is stored in its Merklized form at the node, for `H*` being `persistent_hash`, but with the following modification: If the first nibble of the result is zero, it will be replaced with the first non-zero nibble occurring in the result (e.g. `0x00050a...` becomes `0x50050a...`).
* `Array(n)`: As the entries of the array.
* `BoundedMerkleTree(n)` TODO

#### On-the-wire representation

The on-the-wire representations make use of [FAB](../field-aligned-binary/)
representations. We represent both *ADTs*, and *programs*.

##### ADT representation

The first byte `b` of the ADT distinguishes its type, and how it is further
processed. In binary, MSB first, `b = xyab cddd`.

* `xy != 11` encodes a `Cell`, represented as its on-the-wire FAB value.
* `xya = 110` encodes a `BoundedMerkleTree([bcddd] + 1)`. It is followed by:
  * An unsigned integer length `n`
  * `n` times, in sorted order:
    * An unsigned integer index `i`
    * A 32-byte hash value `h`
* `xyab = 1110` encodes an `Array([cddd])`. It is followed by `[cddd]`
  encodings of on-the-wire ADT representations.
* `xyab cddd = 1111 0000` encodes `Null`
* `xyab cddd = 1111 0001` encodes a `Map`. It is followed by:
  * An unsigned integer length `n`
  * `n` times, in sorted order:
    * A FAB value `key`
    * An ADT `value`

Unsigned integers are represented as themselves if they are <128, otherwise
follow the following correspondence (as integers with flags in FAB, but without
the flags):

```
0aaa aaaa                     ~ [a]
1aaa aaaa 0bbb bbbb           ~ [a] + [b] << 7
1aaa aaaa 1bbb bbbb 0ccc cccc ~ [a] + [b] << 7 + [c] << 14
1--- ---- 1--- ---- 1--- ---- reserved
```

##### Program representations

A program is encoded by encoding its sequence of instructions in order.
An instruction is encoded by a single byte of its opcode, followed by encoding
its arguments (if any), followed by encoding its results (if any).

In the below, the following data may appear as arguments or results:
* `uint` (>0 or not)
* `bool`
* `Adt`
* Lists of the above / lists of pairs of the above

All `uint`s are logarithmic sizes, and will be represented by a single byte.
Where a `bool` is immediately followed by a `uint`, these will also be
represented as a single byte, with the MSB indicating if the `bool` is true,
with the remaining bits encoding an integer <128. An `Adt` is encoded as above.
A list is encoded as a single byte indicating the length, followed by its
content.

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
values here is just an example. Teci ADTs are _immutable_ from the perspective
of Teci programs: A value on the stack cannot be changed, but it can be
replaced with a modified version of the same value. We write `[a]` to refer to
the FAB value stored in the `Cell` `a`. Due to the ubiquity of it, we write
"sets `[a] := ...`" for "create `a` as a new `Cell` containing `...`".

| Name     | Opcode | Stack                      | Arguments                       | Results        | $\Theta$    | Description |
| :---     | -----: | :-----                     | ------------------------------: | -------------: | ----------: | ----------- |
| `noop`   |   `00` | `-{}          +{}`         |                               - |              - |         `1` | nothing |
| `dup`    |   `01` | `-{x*, a}     +{a, x*, a}` |                       `n: uint` |              - |         `1` | duplicates `a`, where `x*` are `n` stack items |
| `pop`    |   `04` | `-{a}         +{}`         |                               - |              - |         `1` | removes `a` |
| `swap`   |   `05` | `-{a, x*, b}  +{b, x*, a}` |                       `n: uint` |              - |         `1` | swaps two stack items, which `n` items `x*` between them |
| `branch` |   `06` | `-{a}         +{}`         |                       `n: uint` |              - |         `1` | if `[a]` is not the empty value, skip `n` operations. The skipped operations *must* have a net-zero effect on the stack. |
| `read`   |   `07` | `-{a}         +{}`         |                               - |     `[a]: Fab` |   `\|[a]\|` | returns `[a]` |
| `write`  |   `08` | `-{}          +{a}`        |                      `[a]: Fab` |              - |   `\|[a]\|` | sets `[a] := [a])` |
| `add`    |   `09` | `-{a}         +{b}`        |                        `c: Fab` |              - |         `1` | sets `[b] := [a] + c`, where addition is defined below |
| `sub`    |   `0a` | `-{a}         +{b}`        |                        `c: Fab` |              - |         `1` | sets `[b] := [a] - c`, where subtraction is defined below |
| `lt`     |   `0b` | `-{a, b}      +{c}`        |                               - |              - |         `1` | sets `[c] := [a] < [b]` |
| `eq`     |   `0c` | `-{a, b}      +{c}`        |                               - |              - |         `1` | sets `[c] := [a] == [b]` |
| `type`   |   `0d` | `-{a}         +{b}`        |                               - |              - |         `1` | sets `[b] := typeof(a)` |
| `size`   |   `0e` | `-{a}         +{b}`        |                               - |              - |         `1` | sets `[b] := size(a)` |
| `member` |   `0f` | `-{a, b}      +{c}`        |                     `d: uint>0` |              - |         `d` | sets `[c] := has_key(a, b, d)` |
| `idx`    |   `10` | `-{a}         +{b}`        | `c: [Fab], d: [(bool, uint>0)]` |              - | `\|c\| + d` | sets `b := fold_left(zip(c, d), a, lambda adt (cached, d) val: adt.get(val, cached, d))` |
| `dyidx`  |   `11` | `-{a, b}      +{c}`        |       `cached: bool, d: uint>0` |              - |         `d` | sets `c := a.get([b], cached, d)` |
| `new`    |   `12` | `-{a}         +{b}`        |                               - |              - |         `1` | sets `b := new [a]` |
| `and`    |   `13` | `-{a, b}      +{c}`        |                               - |              - |         `1` | sets `[c] := [a] & [b]` |
| `or`     |   `14` | `-{a, b}      +{c}`        |                               - |              - |         `1` | sets `[c] := [a] \| [b]` |
| `neg`    |   `15` | `-{a}         +{b}`        |                               - |              - |         `1` | sets `[b] := ![a]` |
| `log`    |   `16` | `-{a}         +{}`         |                               - |              - |         `1` | outputs `a` as an event |
| `root`   |   `17` | `-{a}         +{b}`        |                               - |              - |         `1` | sets `[b] := root(a)` |
| `ins`    |   `18` | `-{a, b}      +{c}`        |                     `d: uint>0` |              - |         `d` | sets `c := insert(a, [b], d)` |
| `inskey` |   `19` | `-{a, b, c}   +{d}`        |                     `d: uint>0` |              - |         `d` | sets `d := insert_key(a, [b], c, d)` |
| `rem`    |   `1a` | `-{a, b}      +{c}`        |                     `d: uint>0` |              - |         `d` | sets `a := remove(a, [b], d)` |

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
  * `Map`: 2
  * `Array(n)`: 3 + n * 32
  * `BoundedMerkleTree(n)`: 4 + n * 32
* `size(a)` returns the number of non-null entries is a `Map`, `n` for
  an `Array(n)` or `BoundedMerkleTree(n)`.
* `has_key(a, b, d)` returns `true` if `b` is a key to a non-null value in the
  `Map` `a`. If the map has more than $2^d$ entries, the operation fails.
* `new ty` creates a new instance of an ADT according to the tag `ty` (as
  returned by `typeof`):
  * `Cell`: Containing the empty value.
  * `Null`: `null`
  * `Map`: The empty map
  * `Array(n)`: An array on `n` `Null`s
  * `BoundedMerkleTree(n)`: A blank Merkle tree
* `a.get(b, cached, d)` retrieves the sub-item indexed with `b`. If the
  sub-item is *not* loaded in memory, *and* `cached` is `true`, this command
  fails. For different `a`:
  * `a: Pair`, if `b == 0`, return the first item, if `b == 1`, the second.
  * `a: Map`, the value stored at the key `b`; fails if $\mathrm{size}(a) > 2^d$.
  * `a: Array(n)`, the value at the index `b` < n
* `root(a)` outputs the Merkle-tree root of the `BoundedMerkleTree(n)` or
  `SortedMerkleTree` `a`.
* `insert(a, b, d)`, inserts the value `b` into the `Map` (with an empty `Cell` element), `SortedMerkleTree`, or `MerkleTree[n]` `a`.
  * If `a` is a `Map` or `SortedMerkleTree`, and $\mathrm{size}(a) > 2^d$, this operation fails.
  * If `a` is a `MekrleTree[n]`, and $n > d$, this operation fails.
* `insert_key(a, b, c, d)`, inserts the value `c` into a map `Map` `a` at key `b`,
  or a `BoundedMerkleTree` `a` at index `b`. Fails if $\mathrm{size}(a) > 2^d$.
* `remove(a, b, d)`, depending on the type of `a`:
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
