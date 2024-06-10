# Proposal 0014: Snark & other cryptographic upgrades

This proposal lays out how Midnight will survive various types of changes in
cryptographic primitives, specifically Snarks and elliptic curves used by
Snarks.

## Problem Statement
Any hard fork must, by necessity, provide a means to translate the ledger state
from prior to hard fork, to a valid and meaningful ledger state after the hard
fork. This is straightforward for *public, non-cryptographic* information, but
becomes an issue when the state itself encodes cryptographic objects, and the
intention of the hard fork is to *change this cryptography*. In particular, any
of the following being stored in the ledger state are affected:

1. Hashes
2. Commitments (homomorphic or otherwise)
3. Signatures
4. Zero-knowledge verifying keys (proving keys would also be, be cannot be practically stored)
5. Any custom cryptography making use of the Snark’s embedded elliptic curve
6. Any data dependent of the size of the Snark’s elliptic curve scalar field

In particular, the question is how these are processed if we modify built-in cryptography:

- Changing to a different Snark will invalidate 4.
- Changing our hash functions will invalidate 1. and in some cases 2.
- Changing our Snark’s elliptic curve will invalidate 3. and 5.
- Changing our Snark’s elliptic curve will *possibly* change the semantics of 6.

An important condition for any solution is *progress*: A contract should always
be able to resume operations, *if* it follows best practices. In particular, user
funds should not be lost or redistributed as a result of a cryptographic
upgrade.

A secondary, but important criteria is that we *do* wish to use Snark-friendly
cryptography, for hashes and commitments, which are significantly cheaper than
primitives which are independent of the Snark's scalar field.

## Proposed Changes

While these problems have the same root cause – data we cannot trivially
translate, they require different approaches to solve. The “solutions” here
will fall into 3 main categories:
1. Ensuring that we *can* translate data when needed.
2. Ensuring that a primitive change *will not* invalidate state
    1. By ensuring that the primitive *does not change*
    2. By *recommending* an alternative for use *in state*
3. Having a *fallback* that ensures the progress condition is satisfied.

This proposal consists of the following main parts:
- Ensuring that data stored in the ledger state is, almost-always, independent
  of the scalar field (addresses 6. along the lines of 1.)
- Separation of hash functions into `persistent_hash` and `transient_hash`
  (addresses 1. (and part of 2.) along the lines of 2.)
- Recommending use of hashes for authentication (addresses 3. along the lines
  of 2.b)
- Discouraging the use of custom, stateful cryptography, leaving 5.
  unaddressed, but warning of the dangers
- A “last resort” fallback for hashes and signatures 
- Providing two fallbacks for verifier keys (addressing 6. along the lines of
  3.):
    - For the short term: Contracts must nominate fallback keys, which are
      allowed to modify a contract’s verifier keys, as well as upgrade
      themselves.
    - For the long term: Contracts should upload an IR of their circuits, which
      can be used to emulate the circuit on a recursive VM, at increased prover
      cost.

### Representing State

While many parts of the ledger’s state must be encoded as field elements for
proof verification, we can use language design of Compact, and self-describing
encodings to keep data in a representation that is independent of the proving
system. Consider the difference between `ledger foo: Cell[Field]` and `ledger
foo: Cell[Unsigned Integer[64]]`, or, even more tellingly, `ledger foo:
Cell[Bytes[64]]`, and `ledger foo: Cell[Vector[2, Field]]` both of which have
the same representation as field elements, for scalar fields up to 256-bits,
but different representations for larger scalar fields.

To ensure we can tell which we want, we encode some level of type information
on-chain, using our [field-aligned binary
encoding](../apis-and-common-types/field-aligned-binary). In particular, the
latter is independent of the size of our prime field – even if this were to
drop below $2^64$, it would still be encodable (although our arithmetic
operations would need to be extended). The only case where data needs to be
translated is in the former, when items are directly stored as Field. This is
something we actively discourage in most cases, and heuristically will
translate by taking the stored values modulo the new field modulus in remaining
cases. This works fine for some instances, such as nonces, but not for stored
hashes (see section “Hash Functions”), and we will want to discourage or
prevent using field types directly in most instances.

This entry is phrased in present tense, as field-aligned binary is
being used at the time of writing this proposal.

### Hash Functions

Hash functions are pervasively used throughout Midnight, and are available for
use within Compact. There are a few possible uses of hash functions, with
increasing levels of complexity of switching them out:
1. Testing different parts of a transaction for integrity (such as the
   communications commitment used in inter-contract calls). This can be swapped
   out with low effort, so long as the parts using it for this integrity check
   are updated.
2. Merklising publicly known data. This can be swapped out with a relatively
   costly chain-wide recomputation step.
3. A hash function hiding (potentially as a commitment) a preimage in public
   data. This is difficult to swap out, but can be done using forced state
   translation (see below).
4. 3., paired with additional structure over this hash, for instance signatures
   of the hashes, or related layered cryptography. This can also be resolved
   using forced state translation in many cases, though some cases may not be
   easily possible.
5. A tree of hashes, whose preimages are all private, but held by different
   users. It is not clear that there is a way to translate this state to a new
   hash function.

Given the existence of 5., we want to avoid switching hash functions in most
cases. However, as we do want to be able to switch proof systems, this leaves
us with relatively costly options, such as SHA-256 and Blake2. As a compromise,
we are proposing to use two hash functions, one for cases such as 3, 4, and 5,
which we will refer to as `persistent_hash`, and one for cases such as 1, and 2,
which we will refer to as `transient_hash`. We will encourage the use of
`persistent_hash` in all cases where appropriate, and aim to not change this
function at all.

This may not be in our hands forever, which is where the “forced state
translation” approach serves as a last resort.

This proposal specifically suggests SHA-256 as `persistent_hash`, and a
suitable instance of Poseidon as `transient_hash`.

### Authentication and custom cryptography

We encourage using proofs of knowledge of hash preimages, together with
`persistent_hash` over using signatures for authentication. We discourage users
from implementing their own cryptography, and advise that if they do, they
should plan how to perform a forced state translation for this.

### Verifier keys and circuits

Verifier keys and circuits are in a unique position in Midnight, as they are
the *most foundational* part of the ledger semantics. A verifier key is a
compressed representation of a circuit, which is limited to being used with a
specific instance of a specific proof system. That means that any change to a
proof system *by necessity* changes all, marking all existing ones as invalid.
This is especially challenging, as a soundness error in the proof system may
require this form of update *without notice*.

Midnight has two types of circuits: Built-in, system level circuits, at the
moment specifically Zswap `spend` and `output` circuits (but this may be extended
in the future), and user-defined smart contract circuits. The latter pose the
primary challenge with replacing verifier keys, as we can simply define the
updated verifier keys for the former in a given hard fork.

Verifier keys are expensive to compute, and it is not tractable at this time to
prove that they were computed correctly. As a result, we need to rely on trust,
rather than cryptography, to ensure that new verifier keys will be available
and correct after an upgrade. We therefore propose that contracts have
*maintenance authorities*, which can, with some limits, modify the rules of
contracts by inserting new verifier keys. Further, as there is no guarantee
that such an authority will be responsive, we suggest using a *zero-knowledge
virtual machine* to allow an on-chain representation of the circuit to be
executed even in the absence of a corresponding verifier key, at significant
performance loss.

#### ZKVM and its relation to ZKIR

A ZKVM is a virtual machine that can execute a specific instruction set by
emulating the effect of each instruction in a zero-knowledge circuit.
Instructions are proved one-by-one, and zero-knowledge recursion of folding is
used to produce a single proof verifying the sequence of instructions executed.
When necessary, memory and programs are Merklized to prove only about the parts
of them which are updated.

As verifier keys will be invalidated on an update, and CMAs are not guaranteed
to be responsive, we suggest having a representation of the circuit for each
entry point stored on-chain, which can be run by a ZKVM when the proof system
is modified.

Crucially, this means that the *new* proof system must support recursion, and
implement the ZKVM chosen, ahead of an update.

It also means that the bytecode representation of the circuit is proof system
independent, which is especially a challenge if the field size changes. In
particular, a reasonable candidate for the bytecode would be the current ZKIR,
however this currently is field-size dependent.

We recommend a spike to modify ZKIR to be field-size independent, and to enable
storing binary circuit representations alongside verifier keys. Enabling
actually running a ZKVM is a longer-term story, however having appropriate data
available would be helpful when it is eventually needed.

This is *not* currently a target for main-net release.

#### Contract Maintenance Authorities

A *contract maintenance authority* (CMA) is a set of users that is permitted to
make arbitrary changes to the set of verifier keys. There are several options
how this may be structured:
- A simple public key signature (CMA being a public key)
- A multisignature (n/n threshold signature)
- A k/n threshold multisignature
- A stake-based threshold multisignature (allowing e.g. DAOs to be maintained
  by their participants)
The choice on which of these we will support will be based on technical
feasibility, with later options being preferable.

Initially, we will not be concerned with the privacy of CMAs, but we may add
this as a concern later.

Critical to the concept is that:

- CMA public keys are proof-system independent
- CMA signatures and signature verification may use the proof system, if
  treated as a built-in circuit

A contract’s CMA is established when the contract is uploaded, and must be set.
We need to provide programmatic tooling to set CMAs in Dapp code, and
documentation suggesting how CMAs can be reasonably selected.

CMAs can be restricted by limiting how quickly then can enact changes:

- A contract can have multiple CMAs, each with a update delay
- If a CMA with update delay $d$ makes a change, this change is pending for a
  time duration of $d$, before it is applied by the first subsequent
  interaction with this contract
- While an update is pending (and not due to be applied), any CMA can cancel it

This can be useful to enable users to detect malicious behavior, and withdraw
from a contract. We should recommend a meaningful CMA delay for this reason
(suggestion: 1 week). 0 delays may still be useful for patching
vulnerabilities, but should have a higher threshold of trust on them.

Once established, a CMA can perform the following actions:
- Remove a (set of) verifier key(s) from a contract
- Insert a (set of) verifier key(s) into a contract
- Nominate a new CMA set to replace the current one

Note that it is not intended for a CMA to directly replace a contract’s state,
although it can rewrite the rules of updating this state. This is to force CMAs
to articulate the rules governing a state change, and to prevent transactions
modifying the state during an update from being ignored.

### Transitionary forced state translation

A final fallback for many types of cryptographic updates is to require manual
intervention of end users. For instance, in translating hashes or signatures,
it is possible to allow a manual step that:

- Proves that, for $h \mapsto h’$, $\exists x . H_1(x) = h \land H_2(x) = h’$
- For a signature $\sigma$ valid for $pk_1$, produces $\sigma’ valid for
  $pk_2$, and signs $(\sigma, pk_1) \mapsto (\sigma’, pk_2)$ with $sk_1$.
- For a signature $\sigma$ valid for an unknown $pk$, provides $\sigma \mapsto
  \sigma’$, and proves that $\exists pk, pk’, \sigma_\delta . \mathsf{verify}((\sigma,
  pk, \sigma’, pk'), \sigma_\delta’, pk)$.

In short, it is possible to allow a transitionary period, where zero-knowledge
proofs are used to allow users to translate data for which they know the
preimage, and therefore data cannot be translated automatically.

This works better with shallow, relatively cheap primitives; the cost of
proving correct computation of a verifier key, for instance, is prohibitive,
which is why this is discussed separately. It also does not cope well with
shared data, as distrusting users may need to collaborate to reconstruct the
primages of, for instance, $H(x, y)$, if each only knows one of $x$, $y$. As a
result, there are some cases which cannot be easily translated, even in this
setting, although there are many which can be.

A key area where translation *is* possible is in the shielded UTXO set, which
has been done in practice by Zcash. The other question is how to apply this to
smart contracts, as one of the key requirements for forced state translation is
that old and new states can be maintained simultaneously, with a reasonable
translation between each other.

Consider a simple cases of translating a set of hashes; the following would be
a simple attempt to implement forced state translation:

- Keep the old set of hashes as part of the contract’s state, inaccessible to
  new calls
- Create a new set of hashes, taking the place of the old one, and accessible
  to new transactions
- Allow a transaction to remove a value from the old set, and insert it into
  the new set, if it proves knowledge of the same preimage for both.

This may appear fine on the surface, however it can violate key contract
invariants:

- A contract may reasonably assume that the set is monotonically increasing,
  but not seeing the old set violates this assumption.
- A contract may assume a linear correlation between the set and another
  variable, for instance a counter. This correlation can be violated both by
  the initial replacement with the (empty) new set, and by the translation
  operation subsequently.

In light of these difficulties, this proposal suggests that forced translation
is not enforced for contracts, but is rather presented as a tool to contract
authors, when and if it is necessary. Contract authors can set their own
invariants, and ensure they are sensibly preserved, and our handling of
verifier key updates already requires a fallback allowed to change the rules
and keys of a contract. Therefore, a forced translation can be implemented by
updating verifier keys to describe rules for permitted translation operations
inside of a contract, rather than globally for all of Midnight.
