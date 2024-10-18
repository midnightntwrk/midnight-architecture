# Proposal 0016: Vector Slicing Syntax

## Problem Statement

[Proposal 0015](./0015-spread-syntax.md) introduces spread subexpressions in
Compact vector creation expressions.  This gives developers a more flexible way
to create vectors, such as concatenating a pair of vectors `v0` and `v1` via the
vector creation expression `[...v0, ...v1]`.

However, by itself, it does not give a convenient way for functional update of
vector elements.  If a developer wants to update element `m` in a vector of
length `n` (where `m` < `n`) there is no way to describe the vector up to but
not including `m`, and the vector from just after `m` to the end.

We introduce "vector slicing" expressions.  They look syntactically like
indexing a vector with a range of indexes, and they allow extracting a
(potentially) smaller vector from a vector.

## Proposed Changes

We will introduce syntax to Compact that allows slicing vectors.  This will look
like indexing a vector by a range of indexes.  The range syntax will be the same
one we use for ranged unsigned integer types: `m..n` where `m` and `n` are
natural number literals and `m` is required to be less than or equal to `n`.
`v[m..n]` is a vector consisting of all the elements of the vector `v` from
index `m` to index `n`, both inclusive.  Note that `v[i..i]` is a single element
vector consisting of the element `v[i]`.

A developer can use this, for instance, to get the first half of `v: Vector<8, T>`
by writing `v[0..3]` (truncating the vector) and the second half by writing
`v[4..7]`.  The same vector could be copied by writing `v[0..7]`.  (Note that
the vector can also be copied with `[...v]`, and that vectors are immutable.)

The problem described above, functional update of a vector element, can be
solved by slicing and spreading elements of the vector.  Specifically, for a
vector `v: Vector<n, T>`, we can get the effect of a functional update
`v[m] = e` by writing `[...v[0..i], e, ...v[j..k]]` where `i` is `m` - 1, `j` is
`m` + 1, and `k` is `n` - 1.

We chose the token `..` because it is used for ranges in ranged unsigned integer
types.  Another commonly used token for slicing is `:`, but that is already used
in Compact for type annotations and for `struct` fields in `struct` creation
expressions.

We chose to make the range inclusive on both ends, like ranges in ranged
unsigned integer types (we could have also maintained this consistency by
introducing a breaking change to unsigned integer types).  That way the indexes
used in slices will always be valid indexes into the vector.

Note that in many programming languages, including JavaScript with
`Array.prototype.slice`, slicing is inclusive on the left and exclusive on the
right.  This is convenient with zero-based indexing and where the length is
known to be `N` because you can write `0..N` instead of `0..N-1`.  However, in
this case, we felt that it was easier for programmers.  Suppose they have `v:
Vector<10, T>` and they want the effect of `v[5] = e`.  With our proposal they
can write:

```
[...v[0..4], e, ...v[6..9]]
```

compare to, with right exclusive slicing:

```
[...v[0..5], e, ...v[6..10]]
```

where it seems less obvious that it is `v[5]` that is being updated, and it
might look like an element is being inserted into the middle of the vector
instead.

## Syntax

We will modify *tail-expr4* in the grammar.  This is the production for vector
indexing.  It will now allow, in place of vector indexing, a range of indexes to
be used:

<table>
  <tr>
    <td><em>tail-expr<sub>4</sub></em></td>
    <td>&rarr;</td>
    <td><b><tt>[</tt></b> <em>vector-indexes</em> <b><tt>]</tt></b> <em>tail-expr<sub>4</sub></em></td>
  </tr>
  <tr>
    <td><em>vector-indexes</em></td>
    <td>&rarr;</td>
    <td><em>nat</em> <b><tt>..</tt></b> <em>nat</em></td>
  </tr>
  <tr>
    <td></td>
    <td>&rarr;</td>
    <td><em>nat</em></td>
  </tr>
</table>

## Static Checking

The static semantics of vector slicing is as follows.  In `v[m..n]`:

* The expression `v` must have a `Vector` type.  It is a static type error
  otherwise.
  
* The literal `m` must be less than or equal to the literal `n`, and they must
  both be (strictly) less than the vector `v`'s length.
  
* The type of the expression is a `Vector` type, with the same element type as
  `v` and whose length is 1 + `n` - `m`.

## Evaluation

In the vector slicing expression `v[m..n]`, the subexpressions `v`, `m`, and `n`
are evaluated from left to right (`m` and `n` are natural number literals and so
they have no side effects).

The result is a vector with length 1 + `n` - `m` with all the elements of the
original vector between `v[m]` and `v[n]` (both inclusive) in order.  (TODO: do
we need to specify copying the vector, like if they are mutable from
TypeScript/JavaScript?)

## Possible Further Changes

Working with vectors in generic circuits or modules (generic over the size of
the vector) will not generally be possible, because indexes are natural numbers
and because generic size parameters are not expressions that we can perform
arithmetic on.  We could consider an extension to allow generic indexes as
expressions and allow them to be used here.
