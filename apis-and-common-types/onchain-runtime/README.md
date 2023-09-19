# On-chain Runtime

This document describes the onchain program format, as represented in JavaScript,
on-the-wire binary, and in prime fields for proof verification. It further
describes the data structures stored in onchain, and how they may be represented,
and argues the primary theorem, stated in the title of the document.

This document superceeds the [Micro ADT Language](../../proposals/0004-micro-adt-language.md).

__Status__: Draft

__Version__: 1.0

## Data types

This document will make use of the [Field-Aligned
Binary](../field-aligned-binary) format, and data types represented in it.  This
document defines the `Program` and `StateValue` data formats, and defines
execution of `Program`s on `StateValue`s.

### Values

The `StateValue` data type is defined as a disjoint union of the following types:
* `Null`: An empty value.
* `Cell`: memory cell containing a single FAB `AlignedValue`
* `Map`: key-value map from FAB `AlignedValue`s to state values.
* `Array(n)` for `n <= 15`: fixed-length array of state values
* `BoundedMerkleTree(n)` for `0 < n <= 32`: depth-`n` Merkle tree of leaf hash values.

Note: we will want to add in a future version:
* `SortedMerkleTree`: an ordered Merkle tree of arbitrary depth of FAB values.

Note that state values appear only in positions where they are *readable*, and where they are not used for indexing.

#### Merklization

A state value may be Merklized (as a separate, base-16 Merkle-Patricia trie, *not* as a binary Merkle tree) as a node whose first child is a tag identifying the type, and whose remaining are:
* `Null`: blank
* `Cell`: A single leaf.
* `Map`: Trees of key-value pairs `(k, v)`, where the path is `0x[H*(k)]`, and the value is stored in its Merklized form at the node, for `H*` being `persistent_hash`, but with the following modification: If the first nibble of the result is zero, it will be replaced with the first non-zero nibble occurring in the result (e.g. `0x00050a...` becomes `0x50050a...`).
* `Array(n)`: As the entries of the array.
* `BoundedMerkleTree(n)` as itself

#### On-the-wire representation

The on-the-wire representations make use of [FAB](../field-aligned-binary/)
representations. We represent both *state value*, and *programs*.

##### State value representation

###### In Binary

The first byte `b` of the state value distinguishes its type, and how it is further
processed. In binary, MSB first, `b = xyab cddd`.

* `xy != 11` encodes a `Cell`, represented as its on-the-wire FAB value.
* `xya = 110` encodes a `BoundedMerkleTree([bcddd] + 1)`. It is followed by:
  * An unsigned integer length `n`
  * `n` times, in sorted order:
    * An unsigned integer index `i`
    * A 32-byte hash value `h`
* `xyab = 1110` encodes an `Array([cddd])`. It is followed by `[cddd]`
  encodings of on-the-wire state value representations.
* `xyab cddd = 1111 0000` encodes `Null`
* `xyab cddd = 1111 0001` encodes a `Map`. It is followed by:
  * An unsigned integer length `n`
  * `n` times, in sorted order:
    * A FAB aligned value `key`
    * A state value `value`

Unsigned integers are represented as themselves if they are <128, otherwise
follow the following correspondence (as integers with flags in FAB, but without
the flags):

```
0aaa aaaa                     ~ [a]
1aaa aaaa 0bbb bbbb           ~ [a] + [b] << 7
1aaa aaaa 1bbb bbbb 0ccc cccc ~ [a] + [b] << 7 + [c] << 14
1--- ---- 1--- ---- 1--- ---- reserved
```

###### As field elements

The first field element `f` distinguishes the type of the state value, with the
remainder being specific on the type.

* `f = 0` encodes a `Null`, with no additional data.
* `f = 1` encodes a `Cell`, with the following field elements encoding a FAB
  `AlignedValue` stored within it (including the alignment encoding!).
* `f = 2 | (n << 4)`, for `n: u64` encodes a `Map` of length `n`. It is followed
  by, in stored order by encoded key-value pairs, consisting of FAB `AlignedValue` keys, and
  `StateValue` values.
* `f = 3 | (n << 4)`, for integers `n < 16` encodes a `Array(n)`. It is followed by `n` `StateValue` encodings.
* `f = 4 | (n-1 << 4) | (m << 8)`, for integers `0 < n <= 32` encodes a
  `BoundedMerkleTree(n)`. It is followed by `m` key-value pairs, with keys
  encoded directly as field elements, and values encoded as `bytes(32)`-aligned
  hashes.

##### Program representations

A program is encoded by encoding its sequence of instructions in order, with
each instruction starting with an opcode, optionally followed by some arguments
to this instruction.

To define program representations, we first define a common argument type:
`path(n)`, an array with `n` path entries, each being either a FAB `AlignedValue`, or
the symbol `stack`.

###### In Binary

An instruction is encoded by a single byte of its opcode, followed by encoding
its arguments (if any), followed by encoding its results (if any).

In the below, the following data may appear as arguments or results:
* `u8` (>0 or not)
* `u21`
* `Adt`

`u8` and `Adt` are encoded in the straightforward way, with `u21` being encoded
as unsigned integers above.

A `path(n)` is encoded by encoding each entry in turn. The symbol `stack` is
encoded as `0xff`, while FAB `AlignedValue`s are encoded directly.

###### As Field Elements

A program is encoded similarly to its binary form as fields. Opcodes are encoded
as a single field element, integers as single field elements, and `Adt`s as above.

An exception is `noop n`, which is encoded as `n` field elements.

A `path(n)` is as `-1` if it is a `stack` symbol, otherwise by encoding the `AlignedValue` directly.
Note that as an `AlignedValue` starts with its length, these are guaranteed not to collide.

### Programs

A `Program` is a sequence of `Op`s. Each `Op`
consists of an opcode, potentially followed by a number of arguments depending
on the specific opcode. For read operations, the operation may return a result
of some length. `Program`s can be run in two modes: evaluating and
verifying. In verifying mode, operation results are expected as arguments, and
are checked for correctness instead of being output.

`Programs` run on a stack machine with a stack of
`StateValue`s, guaranteed to have exactly one item on the stack to start. Each
`Op` has a fixed effect on the stack, which will be written as `-{a, b} +{c,
d}`: consuming items `a` and `b` being at the top of the stack (with `a` above
`b`), and replacing them with `c` and `d` (with `d` above `c`). The number of
values here is just an example. State values are _immutable_ from the perspective
of programs: A value on the stack cannot be changed, but it can be
replaced with a modified version of the same value. We write `[a]` to refer to
the FAB value stored in the `Cell` `a`. Due to the ubiquity of it, we write
"sets `[a] := ...`" for "create `a` as a new `Cell` containing `...`". We
prefix an output value with a `'` to indicate this is a *weak* value, kept
solely in-memory, and not written to disk, and an input value with `'` to
indicate it *may* be a weak value. We use `"` and `†` to indicate that an input
*may* be a weak value, and *iff* it is, the correspondingly marked output will
be a weak value.

Cells are not guaranteed to be fully loaded, if they exceed one database entry.
The first entry is always loaded, which contains the cell's length, and the
rest *can* only be necessary on a `popeq` or `concat` instruction, which
require specifying if the data is expected to reside in-cache or not.

| Name      | Opcode  | Stack                             | Arguments                       | Cost (unscaled) | Description |
| :---      | ------: | :-----                            | ------------------------------: | --------------: | ----------- |
| `noop`    |    `00` | `-{}               +{}`           |                        `n: u21` |             `n` | nothing |
| `lt`      |    `01` | `-{'a, 'b}         +{c}`          |                               - |             `1` | sets `[c] := [a] < [b]` |
| `eq`      |    `02` | `-{'a, 'b}         +{c}`          |                               - |             `1` | sets `[c] := [a] == [b]` |
| `type`    |    `03` | `-{'a}             +{b}`          |                               - |             `1` | sets `[b] := typeof(a)` |
| `size`    |    `04` | `-{'a}             +{b}`          |                               - |             `1` | sets `[b] := size(a)` |
| `new`     |    `05` | `-{'a}             +{b}`          |                               - |             `1` | sets `[b] := new [a]` |
| `and`     |    `06` | `-{'a, 'b}         +{c}`          |                               - |             `1` | sets `[c] := [a] & [b]` |
| `or`      |    `07` | `-{'a, 'b}         +{c}`          |                               - |             `1` | sets `[c] := [a] \| [b]` |
| `neg`     |    `08` | `-{'a}             +{b}`          |                               - |             `1` | sets `[b] := ![a]` |
| `log`     |    `09` | `-{'a}             +{}`           |                               - |             `1` | outputs `a` as an event |
| `root`    |    `0a` | `-{'a}             +{b}`          |                               - |             `1` | sets `[b] := root(a)` |
| `pop`     |    `0b` | `-{'a}             +{}`           |                               - |             `1` | removes `a` |
| `popeq`   |    `0c` | `-{'a}             +{}`           |   `a: Adt` only when validating |         `\|a\|` | returns `a` |
| `popeqc`  |    `0d` | `-{'a}             +{}`           |   `a: Adt` only when validating |         `\|a\|` | returns `a`, which must already be in memory |
| `addi`    |    `0e` | `-{'a}             +{b}`          |                        `c: Adt` |             `1` | sets `[b] := [a] + c`, where addition is defined below |
| `subi`    |    `0f` | `-{'a}             +{b}`          |                        `c: Adt` |             `1` | sets `[b] := [a] - c`, where subtraction is defined below |
| `push`    |    `10` | `-{}               +{'a}`         |                        `a: Adt` |         `\|a\|` | sets `a` |
| `pushs`   |    `11` | `-{}               +{a}`          |                        `a: Adt` |         `\|a\|` | sets `a` |
| `branch`  |    `12` | `-{'a}             +{}`           |                        `n: u21` |             `1` | if `a` is non-empty, skip `n` operations. |
| `jmp`     |    `13` | `-{}               +{}`           |                        `n: u21` |             `1` | skip `n` operations. |
| `add`     |    `14` | `-{'a, 'b}         +{c}`          |                               - |             `1` | sets `[c] := [a] + [b]` |
| `sub`     |    `15` | `-{'a, 'b}         +{c}`          |                               - |             `1` | sets `[c] := [b] - [a]` |
| `concat`  |    `16` | `-{'a, 'b}         +{c}`          |                        `n: u21` |             `1` | sets `[c] = [b] ++ [a]`, if `\|[a]\| + \|[b]\| <= n` |
| `concatc` |    `17` | `-{'a, 'b}         +{c}`          |                        `n: u21` |             `1` | as `concat`, but `a` and `b` must already be in-memory |
| `member`  |    `18` | `-{'a, 'b}         +{c}`          |                               - |       `size(b)` | sets `[c] := has_key(b, a)` |
| `rem`     |    `19` | `-{a, "b}          +{"c}`         |                               - |       `size(b)` | sets `c := rem(b, a, false)` |
| `remc`    |    `1a` | `-{a, "b}          +{"c}`         |                               - |       `size(b)` | sets `c := rem(b, a, true)` |
| `dup`     |    `3n` | `-{x*, "a}         +{"a, x*, "a}` |                               - |             `1` | duplicates `a`, where `x*` are `n` stack items |
| `swap`    |    `4n` | `-{"a, x*, †b}     +{†b, x*, "a}` |                               - |             `1` | swaps two stack items, with `n` items `x*` between them |
| `idx`     |    `5n` | `-{k*, "a}         +{"b}`         |                    `c: path(n)` | `\|c\| + sum size(x_i)` | where `k*` are `m` stack items, `k_1` - `k_{m+1}`, matching the `stack` symbols in `c`. Sets `"x_1 = "a`, `key_j = if c_j == 'stack' then k_{i++} else c_j`, `"x_{j+1} = "x_j.get(key_j, cached)`, `"b = "x_{n+2}`  for `i` initialized to 1, with `cached` set to `false` |
| `idxc`    |    `6n` | `-{k*, "a}         +{"b}`         |                    `c: path(n)` | `\|c\| + sum size(x_i)` | like `idx`, but with `cached` set to `true` |
| `idxp`    |    `7n` | `-{k*, "a}         +{"b, pth*}`   |                    `c: path(n)` | `\|c\| + sum size(x_i)` | as `idx`, with `pth*` set to `{key_{n+1}, "x_{n+1}, ..., key_1, "x_1}` |
| `idxpc`   |    `8n` | `-{k*, "a}         +{"b, pth*}`   |                    `c: path(n)` | `\|c\| + sum size(x_i)` | as `idxp`, but with `cached` set to `true` |
| `ins`     |    `9n` | `-{"a, pth*}       +{†b}`         |                               - | `sum size(x_i)` | where `pth*` is `{key_{n+1}, x_{n+1}, ..., key_1, x_1}` set `x'_{n+2} = a`, `x'_j = ins(x_j, key_j, cached, x'_{j+1})`, `b = x'_1`. `†` is the weakest modifier of `a` and `x_j`s, and `cached` set to `false` |
| `insc`    |    `an` | `-{"a, pth*}       +{†b}`         |                               - | `sum size(x_i)` | as `ins`, but with `cached` set to `true` |
| `ckpt`    |    `ff` | `-{}               +{}`           |                                 |             `1` | denotes boundary between internally atomic program segments. Should not be crossed by jumps. |

In the description above, the following short-hand notations were used. Where
not specified, result values are placed in a `Cell`, and encoded as FAB values.

* `a + b`, `a - b`, or `a < b` (collectively `a op b`), for applying `op` on
  the contents of `Cell`s `a` and `b`, interpreted as 64-bit unsigned integers,
  with alignment `b8`.
* `a ++ b` is the FAB `AlignedValue` of the concatenation of `a` and `b`.
* `a == b` for checking two `Cell`s for equality, at least one of which must
  contain at most 64 bytes of data (sum of all FAB atoms).
* `a & b`, `a | b`, `!a` are processed as boolean and, or, and not over the
  contents of `Cell`s `a` and maybe `b`. These must encode 1 or 0.
* `typeof(a)` returns a tag representing the type of a state value:
  * `Cell`: 0
  * `Null`: 1
  * `Map`: 2
  * `Array(n)`: 3 + n * 32
  * `BoundedMerkleTree(n)`: 4 + n * 32
* `size(a)` returns the number of non-null entries is a `Map`, `n` for
  an `Array(n)` or `BoundedMerkleTree(n)`.
* `has_key(a, b)` returns `true` if `b` is a key to a non-null value in the
  `Map` `a`.
* `new ty` creates a new instance of a state value according to the tag `ty` (as
  returned by `typeof`):
  * `Cell`: Containing the empty value.
  * `Null`: `null`
  * `Map`: The empty map
  * `Array(n)`: An array on `n` `Null`s
  * `BoundedMerkleTree(n)`: A blank Merkle tree
* `a.get(b, cached)` retrieves the sub-item indexed with `b`. If the
  sub-item is *not* loaded in memory, *and* `cached` is `true`, this command
  fails. For different `a`:
  * `a: Map`, the value stored at the key `b`
  * `a: Array(n)`, the value at the index `b` < n
* `rem(a, b, cached)` removes the sub-item indexed (as in `get`) with `b` from `a`. If the
  sub-item is *not* loaded in memory, *and* `cached` is `true`, this command
  fails.
* `ins(a, b, cached, c)` inserts `c` as a sub-item into `a` at index `c`. If
  the path for this index is *not* loaded in memory, *and* `cached` is `true`,
  this command fails.
* `root(a)` outputs the Merkle-tree root of the `BoundedMerkleTree(n)` or
  `SortedMerkleTree` `a`.

## Use in Midnight

### Mapping Existing Micro ADT Language

See the prior document: [Micro ADT language](../../proposals/0004-micro-adt-language.md)

The following programs correspond to each ADT operation.
Notationally, `idx* f` and `idxp* f` to index to a field, this is expected to
be `idx [i]` or `idxp [i]` on the first access to the `i+1`th field in a
`ledger` declaration on the first call, and `idxc [i]` or `idxpc [i]` on
subsequent calls. `(f + g)` should be read as list concatenation of `f` and
`g`. We will also use `push* (f)` to indicate pushing all keys in `f`, and
`|f|` in an `idx` / `idxc` instruction to indicate the length of `f`.
Finally, we write `f_head` and `f_tail` for all but the last, and the last
element of `f` respectively.

We assume a function `leaf_hash` that takes values to their Merkle tree hashes.

Each ADT will also provide initializers, which assume the existence of the field they are inserting into, but that this is set to `Null`.

#### `Counter` init at `f`

```
idxp* f_head
push (f_tail)
pushs (0u64)
insc |f|
```

#### `Counter.read(f)`

```
dup 0
idx* f
popeqc
```

#### `Counter.less_than(f, threshold)`

```
dup 0
idx* f
push (threshold)
lt
popeqc
```

#### `Counter.increment(f, amount)`

```
idxp* f
addi amount
insc |f|
```

#### `Counter.decrement(f, amount)`

```
idxp* f
subi amount
insc |f|
```

#### `Cell` init at `f` with value `v`

```
idxp* f_head
push (f_tail)
pushs (v)
insc |f|
```

#### `Cell.read(f)`

```
dup 0
idx* f
popeq
```

#### `Cell.write(f, v)`

```
idxp* f_head
push (f_tail)
pushs (v)
insc |f|
```

#### `Set` init at `f`

```
idxp* f_head
push (f_tail)
pushs {}
insc |f|
```

#### `Set.is_empty(f)`

```
dup 0
idx* f
size
push (0u64)
eq
popeqc
```

#### `Set.size(f)`

```
dup 0
idx* f
size
popeqc
```

#### `Set.member(f, elem)`

```
dup 0
idx* f
push (elem)
member
popeqc
```

#### `Set.insert(f, elem)`

```
idxp* f
push (elem)
pushs null
ins 1
insc |f|
```

#### `Set.remove(f, elem)`

```
idxp* f
push (elem)
rem
insc |f|
```

#### `Map` init at `f`

```
idxp* f_head
push (f_tail)
pushs {}
insc |f|
```

#### `Map.is_empty(f)`

```
dup 0
idx* f
size
push (0u64)
eq
popeqc
```

#### `Map.size(f)`

```
dup 0
idx* f
size
popeqc
```

#### `Map.member(f, key)`

```
dup 0
idx* f
push (key)
member
popeqc
```

#### `Map.lookup(f, key)`

```
dup 0
idx* (f + [key])
popeq
```

#### `Map.insert(f, key, value)`

```
idxp* f
push (key)
pushs (value)
ins 1
insc |f|
```

#### `Map.insert_default(f, key)` with default value `value`

As `Map.insert(f, key, value)`.

#### `Map.remove(f, key)`

```
idxp* f
push (key)
rem
insc |f|
```

#### `List` init at `f`

Representing as a singly-linked list, with the empty list being the triple
`[null, null, (0u64)]`, and a `cons(a, as)` being `[(a), as, (1 + len(as))]`.

```
inxp* f_head
push (f_tail)
pushs [null, null, (0u64)]
insc |f|
```

#### `List<T>.head(f)`

This assumes we know the maximum (binary) size `s` of `T`, and the default of
`Maybe[T]`, which we write as `none`.

```
dup 0
idx* (f + [0])
dup 0
type
push (1u8)
eq
branch 4
push (1u8)
swap 0
concat s
jmp 2
pop
push (none)
popeqc
```

#### `List.pop_front(f)`

```
idxp* f
idx [1u8]
insc |f|
```

#### `List.push_front(f, value)`

```
idxp* f
dup 0
idx [2u8]
addi 1
pushs [(value), null, null]
swap 0
push (2u8)
swap 0
insc 1
swap 0
push (1u8)
swap 0
insc (|f| + 1)
```

#### `List.length(f)`

```
dup 0
idx (f + [2u8])
popeqc
```

#### `MerkleTree<d>` init at `f`

Represented as a pair of the actual tree, and the `first_free` index counter.

```
idxp* f_head
push (f_tail)
pushs [MT(d) {}, (0u64)]
insc |f|
```

#### `MerkleTree<d>.check_root(f, rt)`

```
dup 0
idx (f + [0u8])
root
push (rt)
eq
popeqc
```

#### `MerkleTree<d>.is_full(f)`

```
dup 0
idx (f + [1u8])
push (1u64 << d)
lt
neg
popeqc
```

#### `MerkleTree<d>.insert(f, item)`

```
idxp* (f + [0u8])
dup 2
idx [1u8]
pushs (leaf_hash(item))
ins 1
insc 1
idxp [1u8]
addi 1
insc (|f| + 1)
```

#### `MerkleTree<d>.insert_index(f, item, index)`

```
idxp* (f + [0u8])
push (index)
pushs (leaf_hash(item))
ins 2
idxp [1u8]
push (index)
addi 1
dup 1
dup 1
lt
branch 2
pop
jmp 2
swap 0
pop
ins 1
insc |f|
```

#### `MerkleTree<d>.insert_index_default(f, index)` with default value `item`

As in `MerkleTree<d>.insert_index(f, item, index)`.

#### `HistoricMerkleTree<d>` init at `f`

Represented as `MerkleTree<d>`, with an additional field storing a set of
permissible roots.

```
idxp* f_head
push (f_tail)
pushs [MT(d) {}, (0u64), {}]
idxp [2u8]
dup 2
idx [0u8]
root
pushs null
insc (|f| + 2)
```

#### `HistoricMerkleTree<d>.size(f)` (for heuristic sizes only)

```
dup 0
idx (f + [2])
size
popeqc
```

#### `HistoricMerkleTree<d>.check_root(f, rt)`

```
dup 0
idx (f + [2])
push (rt)
member
popeqc
```

#### `HistoricMerkleTree<d>.is_full(f, rt)`

```
dup 0
idx (f + [1])
push (1u64 << d)
lt
neg
popeqc
```

#### `HistoricMerkleTree<d>.insert(f, item)`

```
idxp* (f + [0u8])
dup 2
idx [1u8]
pushs (leaf_hash(item))
ins 1
insc 1
idxp [1u8]
addi 1
insc 1
idxp [2u8]
dup 2
idx [0u8]
root
pushs null
ins 1
insc (|f| + 1)
```

#### `HistoricMerkleTree<d>.insert_index(f, item, index)`

```
idxp* (f + [0u8])
push (index)
pushs (leaf_hash(item))
ins 1
insc 1
idxp [1u8]
push (index)
addi 1
dup 1
dup 1
lt
branch 2
pop
jmp 2
swap 0
pop
insc 1
idxp [2u8]
dup 2
idx [0u8]
root
pushs null
ins 1
insc (|f| + 1)
```

#### `HistoricMerkleTree<d>.insert_index_default(f, index)` with default value `item`

As in `HistoricMerkleTree<d>.insert_index(f, item, index)`.

#### `HistoricMerkleTree<d>.reset_history(f)`

```
idxp* f
push (2u8)
pushs {}
dup 2
idx [0u8]
root
pushs null
insc (|f| + 2)
```

### Kernel Operation, Context and Effects

Kernel operations affect things, and retrieve knowledge from outside of the
contract's state. We model this by running a program not just on the
contract's current state, but on an initial stack of `{state, effects,
context}`. When the program finishes executing, it should leave a stack of
`{state', effects', _}`. `state'` is used to replace the contract's state, and
`effects'` must adhere to the structure given here, specifying the effects of
the operation.

The `context` is an `Array(_)`, with the following entries, in order:

1. A `Cell` containing the 32-byte aligned current contract's address.
2. A `Map` from `CoinCommitment` keys to 64-bit aligned Merkle tree indicies,
   for all newly allocated coins.
3. A `Cell` containing the block's 64-bit aligned seconds since the UNIX epoch
   approximation.
4. A `Cell` containing the block's 32-bit aligned seconds indicating the
   maximum amount that the former value may diverge.
5. A `Cell` containing the blocks's 32-bytes hash.

This list may be extended in the future in a minor version increment.

The `effects` is an `Array(_)`, with the following entries, in order:

1. A `Map` from `Nullifier`s to `Null`s, representing a set of claimed nullifiers.
2. A `Map` from `CoinCommitment`s to `Null`s, representing a set of received coins claimed.
3. A `Map` from `CoinCommitment`s to `Null`s, representing a set of spent coins claimed.
4. A `Map` from `(Address, Bytes(32), Field)` to `Null`, representing the contract calls claimed.
5. A `Map` from `Bytes(32)` to `Cell`s of `u64`, representing coins minted for any specialization hash.

This list may be extended in the future in a minor version increment.

`effects` is initialized to `[{}, {}, {}, {}, {}]`.

All of `context` and `effects` may be considered cached. To prevent cheaply
copying data into contract state with as little as two opcodes, both are
flagged as *tainted*, and any operations performed with them, that are not
size-bounded (such as `add`) will return a tainted value. If the final `state'`
is tainted, the transaction fails.

We will use a fixed bound of `d = 8` for all claims; note that these *are*
cheap due to being guaranteed in-cache.

#### Kernel `claim_zswap_nullifier(nul)`

```
swap 1
idxpc [0u8]
push (nul)
pushs null
insc 2
swap 1
```

#### Kernel `claim_zswap_coin_spend(note)`

```
swap 1
idxpc [2u8]
push (note)
pushs null
insc 2
swap 1
```

#### Kernel `claim_zswap_coin_receive(note)`

```
swap 1
idxpc [1u8]
push (note)
pushs null
insc 2
swap 1
```

#### Kernel `claim_contract_call(addr, entry_point, comm)`

```
swap 1
idxpc [3u8]
push ((addr, entry_point_hash(entry_point), comm))
pushs null
insc 2
swap 1
```

#### Kernel `mint(amount)` (changed to `mint(domain_sep, amount)`)

```
swap 1
idxpc [4u8]
push (domain_sep)
dup 1
dup 1
member
push (amount)
swap 0
neg
branch 4
dup 2
dup 2
idx [stack]
add
insc 2
swap 1
```

#### Kernel `self`

```
dup 2
idx [0u8]
popeqc
```

#### General `*_coin` flow

The `*_coin` variants are largely achieved by computing a coin's commitment,
looking it up in the context commitment map, and concatenating the resulting
index.

Since the commitment computation is done in-circuit, we assume that
`coin_com(coin)` exists as a function when describing this flow.

Then, the general flow to getting the qualified coin onto the stack is:

```
push (coin_com(coin))
dup 3
dup 1
idxc [1, stack]
concat 80
```

This is used in place of `pushs` in the relevant code snippets above.
