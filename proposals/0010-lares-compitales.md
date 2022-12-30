# Proposal 0010: Lares Compitales

This proposal is to split out the ledger prototypes `adt` module into its
own repository, and increase the responsibilities of this to be:
1. A dependency of Abcird, to allow this to run without a ledger dependency.
2. The owner of what ledger ADTs Abcird supports, and how these function,
   without duplicate specifications in the Abcird repository.
3. Possible to factor out, to remove Midnight-specific ledger operations from
   Abcird and replace them with ones usable in other contexts.

# Problem Statement

Coupling between Abcird, the ledger, and the application backend is currently
too high. One of the reasons for this is that there is a large API surface for
making ADT queries on the ledger, for expressing these in Abcird, and these
need to be accurately threaded through the javascript execution context.

This makes changes to the ADT language difficult, especially large-scale ones
as the desired support for nesting in the medium-term future. We want an
architecture that allows minor changes to the ADT language to be performed
rapidly, and major changes to require minimal intervention on most
repositories.

# Proposed Changes

The proposed changes are a refactor of ADT-related code being moved from both
the Abcird repository and the ledger repository to a new, *Lares Compitales*
repository.

**This proposal is not complete, and needs feedback from Kent Dybvig on how
best to factor these out from Abcird.**

This repository will contain:

1. Definitions of the ADTs available, their operations, and the type signatures
   of these.
2. Rust implementations of the ADTs.
3. Definitions of (which?) nanopass languages and/or passes related to the
   ADTs
4. Definitions of the JS output, linking to... What? A new JS rust target?
   Compatibility?

# Desired Result

The primary goal is to be able to add a new ADT without touching any repository
but the new Lares Compitales one.
