# Hoarfrost Data Storage

Hoarfrost is a scheme for persistently storing persistent data structures,
specifically Merkle-Patricia tries, in Midnight.

__Status__: Draft
__Version__: 1.0

## Assumptions

Hoarfrost assumes an efficient key-value database, and that data stored is
organized into deduplicated trees, or directed acyclic graphs. It assumes that
elements nodes in these trees have arbitrary data attached to them, and that
the format and correctness of this data is managed elsewhere.

## Data in Hoarfrost

Hoarfrost is conceptually a Merklised DAG, which doubles as a radix trie.

It consists of *vertices* labelled with arbitrary bytestrings `data`, and
directed *edges*, labelled with integers 0-15, typically written in hexadecimal
in this document. The graph must be acyclic, and no vertex may have two
outgoing edges with the same label, and two vertices with the same children and
label must be equal.

We will call a vertex a *leaf* if it has no outgoing edges. We will call a set
of vertices an *extension* if each vertex in it has exactly one outgoing edge,
the set is connected, and all vertex labels are the empty string. This
connection forms a total order over the extension, we call the sequence of
labels of the vertices used in this order the *extension label*. We will call
vertices that are not a leaf, and not part of an extension a *branch*.

We call the set of all vertices reachable from a vertex `v` the *closure* of
`v`.

### On-the-wire

The simplest encoding of Hoarfrost is the on-the-wire encoding. At its simplest,
it consists of a sequence of encoded vertices, each annotated with the outgoing
edges, and the index of the vertex at the other end.

We will first consider how to encode an individual vertex (which may end up
encoding some of its children), and then how to encode the full closure of a
vertex. Let us call the encoding of a vertex `v`: `E(v)`.

If `v` is part of an extension; that is, `v` has exactly one outgoing edge, we
first determine the largest extension starting at `v` that it is a part of,
`ext`, and the extension label `label`, and first reachable node after the
extension `u`. Then, we encode:
- A marker that this vertex is an extension
- The length of, and content of `label`
- The target `u` (see below)

If `v` is a leaf or a branch, we encode:
- A marker that this vertex is a branch
- The length of, and context of the vertex label `data`
- The label of largest outgoing edge, or `none`
- For each label up to and including that, the target vertex `u` for that label
  (see below)

Where we encode target vertices `u` above, these can be encoded in one of three
ways:
- Recursively as above, iff this is the only incoming edge to `u` in the
  closure being encoded.
- As non-existant/null, iff we're encoding a missing node in a branch
- As a reference to the top-level sequence of vertices, iff this node has
  multiple incoming edges

----

When encoding a closure of `v`, first the node `v` itself is encoded into an
array of encodings. This encoding may include references to further nodes,
which should be counting in order of appearance (left-to-right, in the
serialized data). If a node has already been encoded, or is queued to be
encoded, it's already given position is used instead. The encoding queue is then
processed in-order, encoded each into the array of encodings, and any further
nodes references are appended to the queue.

Finally, the array of encodings is itself serialized.


When decoding, to ensure that the encoding is canonical, a few extra checks are performed:
- That references are introduced in order: The first reference must be one, and
  any subsequent reference must be a prior reference, or 1 greater than the prior
  maximum reference.
- That no two top-level encoded vertices are equal.
- That all top-level encoded vertices are reachable from the first vertex.
- That no extension is encoded as a node, or encoded too short


{{TODO: Binary encoding format}}

### In-database

When stored on disk, in a key-value database, Hoarfrost is parameterised by a
*specific* hash function `H`. Each vertex `v` has a hash, denoted `H(v)`,
determined by:
- The label of `v`
- The ordered sequence of `(l, H(u))` pairs, for each outgoing edge to `u`,
  labelled `l`.

Vertices `v` are stored in a key-value database, with the key `H(v)`, and the
value consisting of a) a reference counter, and b) a similarly encoded value to
the on-the-wire encoding, but using hashes instead of indices in references.
Further, the conditions of when a vertex should be stored versus inlined are
changed to favor minimising look-ups over size.

Specifically, incoming edges are no longer used to determine inlining, and
instead *entries* are optimised to fit within a single disk read. That means
that a *target size* for an entry, `T` is fixed, and, after encoding a vertex,
if its entry is smaller than `T`, any children are expanded breadth-first until
the largest entry that is still smaller than `T` is arrived at. As references
are now 32 bytes, "small entries" are entries that are smaller than a reference
to them, and these are always inlined.

As `data` is unbounded, it may be *larger* than `T`. An entry larger than `T`
is split into consecutive entries, by incrementing `H(v)`. That is, the second
part of `v`'s entry may be found in `H(v) + 1` and so forth. The first part
must always contain the metadata, the length of the entry, and the children of
the entry.

{{TODO: Binary encoding format}}

### In-program

{{TODO: Rust usage, API suggestions}}

