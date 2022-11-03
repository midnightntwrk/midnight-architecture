# Proposal 0008: Signatures of Knowledge in Abcird

This is a proposal stating the intention that Abcird proofs should be Signatures
of Knowledge, rather than plain non-interactive zero-knowledge proofs, and how
this should be technically accomplished.

# Problem Statement
What prevents a malicious user from taking a proof from an honest transaction,
and using it in a different context? Clearly, this would not allow changing the
public transcript, but it would allow using different transcripts in sub-calls,
or even the same public transcript for a separate contract using the same
circuit.

In order to get the binding properties discussed in the [Transaction Structure
Proposal](./0005-transaction-structure-v1.md#binding-and-replays), we need the
ZK proofs to sign the contract address, entry point, and binding commitment of
the `CriticalSection`.

# Proposed Changes
The circuit output of Abcird (in the form of either ZKIR, or their underlying
Plonk implementation), should accept an additional public input `msg`. This
input should be a single field element, and should be used in a single, trivial
gate, to ensure that it is bound to. It should have no effect on the rest of the circuit.

Where explicitly mentioned, this input shall be treated as the first public
input, as seen in the [`ContractCall` public input
vector](./0005-transaction-structure-v1.md#contractcall). To sign over an
arbitrary value, the transient hash function (Poseidon) shall be used to
compress a canonical representation of this value as field elements to a single
field element.

# Desired Result
Proofs resulting from Abcird can be used as signatures of knowledge in larger systems.
