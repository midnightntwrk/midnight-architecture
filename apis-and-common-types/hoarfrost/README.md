# Hoarfrost Data Storage

A forest of frozen trees.

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


A binary encoding is left for future specification -- the first revision of
this document is focused on high-level concepts.

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
are now 32 bytes (or whatever the hash size is), "small entries" are entries
that are smaller than a reference to them, and these are always inlined.

As `data` is unbounded, it may be *larger* than `T`. An entry larger than `T`
is split into consecutive entries, by incrementing `H(v)`. That is, the second
part of `v`'s entry may be found in `H(v) + 1` and so forth. The first part
must always contain the metadata, the length of the entry, and the children of
the entry. This splitting is to prevent $O(1)$ operations from being used to
require the database to load large sections of data into memory for low cost.

A binary encoding is left for future specification -- the first revision of
this document is focused on high-level concepts.

### In-program

In a program, Hoarfrost should be quasi-transparent, acting as a smart pointer
to data most of the time, equipped with an additional API to access underlying
storage an serialization formats. This document will focus on usage in rust,
although it does not preclude using Hoarfrost in other languages in the future.

```rust
type UntypedDeserializeFn<R, F> = dyn Fn(&Arena, &mut R, F) -> io::Result<Rc<dyn Storable>>;

pub trait Storable: Any {
    fn children<'a>(&'a self) -> [Option<Rc<dyn Storable>>; 16];
    fn data_size(&self) -> usize;
    fn write_data<W: Write>(&self, writer: &mut W) -> io::Result<()>;
    // Note that when implemented with children, an unsafe type cast is needed
    // to recover the `Rc<ChildType>` from the `Rc<dyn Storable>` type. This is due to the
    // limitations of rusts generics: Ideally `F` would of the following type:
    //   for<T: Storable> Fn(u8) -> io::Result<Rc<T>>
    // but Rust doesn't have forall types outside of lifetimes.
    fn deserialize<
      R: Read + 'static,
      F: Fn(u8, UntypedDeserializeFn<R, F>) -> io::Result<Rc<dyn Storable>> + 'static,
    >(arena: &Arena, reader: &mut R, children: F) -> io::Result<Rc<Self>>;
    fn deserialize_untyped<
      R: Read,
      F: Fn(u8, UntypedDeserializeFn<R, F>) -> io::Result<Rc<dyn Storable>> + 'static,
    >(arena: &Arena, reader: &mut R, children: F) -> io::Result<Rc<dyn Storable>> {
        Self::deserialize(arena, reader, children).map(Rc::upcast)
    }
}
```

Any type that wants to be stored in Hoarfrost should implement `Storable`.

`children` and `data_size` should be $O(1)$ cost, and `T::Child` should be a
smart pointer, or an enum of smart pointers to achieve this.

These can be used in a memory arena:

```rust
pub struct Arena { /* ... */ }

pub struct Rc<T: Storable> { /* ... */ }

impl Arena {
    // Creates a blank arena in memory
    pub fn new() -> Self;
    // Creates an arena from an existing database
    pub fn from_db(db: DB) -> Self;
    // Allocates a new storable within the arena
    pub fn alloc<T: Storable>(&self, value: T) -> Rc<T>;
    // Is the pointer contained within this particular arena?
    pub fn is_within<T: Storable>(&self, ptr: Rc<T>) -> bool;
    // Take a pointer from another arena, and ensure it is present in this one.
    pub fn copy_into_arena<T: Storable>(&self, ptr: Rc<T>) -> Rc<T>;
    // Tells a disk-backed arena to write a particular pointer, and its closure
    // to disk.
    pub fn add_disk_root<T: Storable>(&self, ptr: Rc<T>) -> io::Result<()>;
    // Tells a disk-backed arena to remove a particular pointer from the
    // storage roots.
    pub fn remove_disk_root<T: Storable>(&self, ptr: Rc<T>) -> io::Result<()>;
    // Imports a serialized form of a pointer's closure into this arena.
    pub fn import_from_serialized<T: Storable, R: Read + 'static>
        (&self, reader: &mut R) -> io::Result<Rc<T>>;
}

impl<T: Storable> Rc<T> {
    pub fn serialize_closure(&self, writer: &mut W) -> io::Result<()>;
    pub fn owner(&self) -> Arena;
    pub fn status(&self) -> RcStatus;
    pub fn upcast(self) -> Rc<dyn Storable>;
    pub async fn ensure_loaded();
}

impl Rc<dyn Storable> {
    pub fn downcast<T: Storable>(self) -> Result<Rc<T>, Rc<dyn Storable>>;
}

pub enum RcStatus {
    Unopened,
    DiskBacked,
    OnlyInMemory,
}

impl<T: Storable> Drop for Rc<T> {
    // ...
}

impl<T: Storable> Clone for Rc<T> {
    // ...
}

impl<T: Storable> Deref for Rc<T> {
    type Target = T;
    // ...
}

impl Eq for Arena {
    // ...
}
```

#### Tracking churn, insertions and deletions

The idea here is to measure these side-effectfully. At the start, before
measuring, create a new `Arena`, and copy the input `x` into it. This should be
almost a noop, referencing the original `Arena`, but keeping the smart pointer
as `RcStatus::Unopened`.

Then, perform the functional computation on `x`, resulting in `y`. With both
smart pointers in hand, step through the `Rc` tree manually to determine the
sets of *opened* vertices in both `x` and `y`, `O(x)` and `O(y)` respectively.
Insertions are the closure of `O(y) \ O(x)`, deletions `O(x) \ O(y)`, and churn
the union of both. Determining these closures *may* involve opening vertices in
`x` and `y` that we're previously opened, because it's possible to:
1. Remove a sub-tree without opening it
2. Insert a sub-tree by referencing to another `Arena` containing it

However, these operations are proportional to *at least* the churn cost, which
can pay for this book-keeping.

#### Implementation Concerns

Hoarfrost will naturally induce contention on a global resource: The database.
Care must be taken to limit this contention, both reducing time spent waiting
on disk, and time where spent on secondary resources which may induce
contention. In particular, the use of locks in inevitable in many places, but
should be reduced to a bare minimum.

When handling `Rc<T>` pointers, data should be accessed from the following, in
order of availability:

1. An internal shared pointer, for instance an `Arc<T>` (requiring no locks).
2. An in-memory cache of on-disk data base state, for instance internal data of
   an `Arena` (requiring a read lock).
3. The on-disk storage of the value (requiring a disk/db lock).

It appears reasonable to handle data requests in a separate thread, to allow DB
requests to be handled independently of standard program operation.

To enable parallel loading of data, batch loading should be possible. There are broadly three classes of loads:

1. Loading a (set of) hash(es) directly
2. Loading a (set of) known keys under a (set of) known hash(es)
3. Loading unknown keys under known hash(es)

Although in the worst case, 3. will require synchronous disk access, it can be
mitigated by loading relatively small vertices entirely. For this reason, a
disk-backed arena should expose endpoints to hint at loading a combination of
these:

```rust
impl Arena {
    /// Returns a promise that, once complete, all keys are guaranteed to be
    /// in-cache
    pub async fn preload_keys<T: AsRef<[u8]>>(&self, root: Hash, keys: &[T]) -> io::Result<()>;
    /// Returns a promise that, once complete, all keys are loaded (as far as
    /// possible) recursively into cache, up to `max_depth` depth depth, and a
    /// total size of `max_total_size`. /// Returns `true` if this is the
    /// entire closure, and `false` if the closure is limited due to resource
    /// bounds.
    pub async fn preload_dyn_keys<T: AsRef<[u8]>>(&self, root: Hash, keys: &[T], max_depth: u8, max_total_size: usize) -> io::Result<bool>;
    /// Marker that this is a good point to garbage collect the in-memory cache
    /// Behaviour is unspecified, but should release memory as possible if
    /// memory is running out
    pub async fn release_cache(&self);
    /// Forces a hard write to the DB of new additions.
    pub async fn sync(&self) -> io::Result<()>;
}
```
