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

A datum in Hoarfrost consists of:

- A bytestring `data` encoding the immediate data at the node.
- A sequence of child datums `children`
- Metadata attached to the datum
  - A reference count
  - Further in-memory only metadata, such as:
    - A non-persisted reference count
    - A cache status
    - Markers to track which parts of state were accessed

A datum has a hash `H(data, children)`, computed from `data`, and the hash of
the elements in `children`.

A datum `x`'s closure is smallest set `X` such that `x` is in `X`, and for each
`y` in `X`, and `z` in the `children` of `y`, `z` is in `X`.

### Data, concretely

A Hoarfrost datum is targeted for 4k random reads, and will assume that
references are 256-bit / 32 byte hashes.

We will assume an entry is targeted to be at most 4096 bytes long, potentially
consisting of both key and value, leaving 4064 bytes for content. Note that
longer entries are possible, as `data` is not restricted.

The first 11 bytes encode the shape of data included in this entry, as well as
it's (persisted) metadata, in Borsh encoding:

- A `u32` size of the `data` entry
- A `u8` length of `children`, which must be `<= 16`
- A `u16` bitmask encoding if `children` are a) references or b) inline
- A `u32` reference count

This is then followed by the `children` either a) encoded directly, or b)
encoded as content themselves, depending on the bitmask state, and finally
followed by the `data` entry. 

By default, `children` are stored by reference, taking up 32 bytes each, unless
there is room within the 4k read. If there is, children get expanded
breadth-first while there is still room, ensuring that the final entry contains
as many nodes as possible, without exceeding a 4k read.

Hoarfrost is parameterised by a 256-bit hash function, which is applied to the
following data, in Borsh encoding, to determine the key of a datum:

- The `u32` size of the `data` entry
- The content of the `data` entry
- The `u8` length of `children`
- The sequence of hashes of `children`

When a data entry is created, any children references are retrieved, and their
reference counts are increased by 1. When a data entry is deallocated, any
children references are retrieved, and their reference counts are decreased by 1.
Note that:

- We do not necessarily deallocate if a reference count is 0, although it is
  trivial to implement garbage collection upon this.
- As reference counts are limited to `u32`s, we consider the maximum `u32`
  value as "saturated": Anything that reaches a reference count this high will
  never have its reference count decreased, and will be permanently allocated.

## Smart pointers

{{TODO: Write on usage in rust, turning the database into smart pointers}}
{{TODO: Write on additional in-memory metadata, tracking usage and changes between two states}}
