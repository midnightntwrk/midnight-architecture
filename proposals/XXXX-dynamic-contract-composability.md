# Proposal XXXX: Dynamic Contract Composability

**Overview:** we have implemented a facility for contract composability.
The dependencies between contracts are *static* and *fixed* at deployment time.
This proposal describes a limited facility to allow dynamic contract dependencies that can arise after contract deployment.

## Context: Static Contract Composability

There were three proposals related to composable contracts:
[0009: Sealed Ledger State](0009-sealed-ledger-state.md),
[0010: Composable Contracts Syntax](0010-composable-contracts-syntax.md), and
[0011: Contract Interface Types](Proposal 0011: Contract Interface Types).
We sketch those proposals and then the actually implemented feature below.

### Sealed Ledger State

Ledger fields in a contract's public state can be declared `sealed`.
The compiler will only allow modification to sealed fields in a contract's constructor;
that is, before the contract is deployed.
Otherwise (after deployment), the compiler will not allow sealed fields to be modified.

This proposal is not directly about composable contracts.
It was used to enforce some restrictions on contract dependencies so that they were static and fixed at deployment time
(restrictions which we are proposing to lift here).

### Composable Contracts Syntax

This introduces syntax and (implicitly) a computation model for composable contracts.
Programs consist of a collection of contract declarations,
as well as non-contract utility declarations like types, modules, and pure circuits.
(Pure circuits are ones which can be called without a contract instance.)

A contract declaration introduces a named type (the contract name).
Values of contract types are represented as a reference to the contract (i.e., the contract address).
A value of a contract type can be used to invoke that contract's circuits.
You *cannot* pass contract-typed values to circuits nor return them to circuits.
You can pass them to witnesses (it's not clear what you can do with them in a witness),
but you *cannot* return them from witnesses.
You can store them into the public ledger.

This implies that the only way that a circuit can get a contract typed value to call is to read it from the public ledger.

You can pass contract typed values to the contract's constructor
which is invoked by JS code to establish the initial public ledger state before deploying the contract.

Presuming that these are represented in JS by an already-deployed contract's address, then
contract dependencies are static and fixed at deployment time.
There is no way to update a contract's public ledger state other than invoking the contract's own circuits,
and circuits do not have a way to obtain a statically unknown contract address that they were not
configure with at deployment time.

Similarly, there is no way to create a cyclic dependency between contracts.
A dependency is represented by a deployed contract address, it it must be fixed before deployment.
Therefore, contract dependencies form a DAG.

Note that this does not imply that the cross-contract call graph is fixed.
A contract could be deployed with multiple instances of the same dependent contract type.
It could then conditionally choose between which one of them to invoke.

There is no way in Compact to instantiate a contract.
Contracts are always instantiated and deployed via some extra-linguistic mechanism.

Consequently: there is a static fixed graph of contract dependencies
on preexisting contract deployments, which is established before a contract is deployed.

### Contract Interface Types

The final proposal is very simple.
It introduces contract interface types, with an implied (not explicit) subtyping rule
between contract interface types and between contract interface supertypes and contract type subtypes.

Contract dependencies are still static and fixed.
But in the scenario where code is conditionally choosing between multiple dependent contracts to invoke,
they no longer have to all be instances of the same contract type.

### What We Actually Implemented

This is basically what we've actually implemented.
The only exception is that we have not removed top-level impure circuits from programs.
The proposed model was that a program was a collection of named contracts.
The actual model is that a program has an implicit anonymous top-level contract,
with contracts nested inside it (is this nesting only one level deep?).

We did not introduce explicit contract interface types,
but we did introduce a subtyping relation on contract types which gives effectively the same
feature.

### The Implicit Computational Model

The proposal does not describe in specific terms what the semantics of this syntax is.
There is however, a somewhat obvious computational model that fits with the existing
single-contract coputational model.

Note that this is the downstream (from the compiler) implementation work that we are currently
implementing in the Compact.js and Midnight.js libraries.

A decentralized application (DApp) interacts with a contract.
DApps include applications with a user interface, like a web app or a mobile app.
They can also have only a command-line interface.
There can also be general "DApp-like" tools that can interact more generically with a contract.
And example of such a tool is the *Node Toolkit* that we've built,
which allows deploying contracts without writing any JS code
and making transactions without any extra JS code beyond providing implementations of any required
witnesses.

All of these are collectively called "DApps" below.

**A contract's constructor is invoked from JS code in a DApp.**
It can be passed an already deployed contract address and so the contract can be configured with
its contract dependencies before deployment.

**It's not specified how the JS constructor verifies the static type of the contract dependencies.**
A deployed contract address does not necessarily implement a subtype of the required contract type.
We could verify that it has all of (and perhaps more than) the expected exported circuits.
We could verify that the verifier keys (vks) are expected ones,
but this does not allow configuration with an arbitrary subtype of a contract type.
The code (verifier keys) for exported circuits must match exactly.

**When you interact with a deployed contract, you provide your own witnesses.**
The deployed contract can depend on witnesses, which are not deployed on chain with the contract.
Instead, your DApp can configure them with its own witness implementations.
This is not a (new) security hole, it's the Midnight computational model.
Witness return values will be verified to match the constraints expected by the contract.

**When a DApp makes a cross-contract call, it must have the JS implementation available.**
Contract dependencies are available as Compact source code, and compiled when the contract is compiled.
The DApp therefore has a JS implementation of the dependent contract available.

**The DApp must fetch a snapshot of the dependent contract state.**
A DApp executes a transaction off chain using a snapshot of the public state.
For dependent contract calls, the DApp must have fetched a snapshot of the dependent contract's state.
This is assumed to be fetched using the address of the called contract.

Given the contract state and the JS code, we can execute the cross-contract call in the DApp.

**When a cross-contract call is provem, the ZKIR code and prover key is available to the DApp.**
As part of constructing a transaction, the DApp uses the circuit's prover key and a representation
of the circuit in the form of a ZKIR circuit, to prove that the circuit was run with private witness values.
The ZKIR circuit and prover keys are produced by the Compact compiler, and they are available to a
DApp in the same way that the JS code is.

**Dependent proofs are constructed separately.**
Because the call graph is not fixed, we did not (cannot) inline the called circuit's ZKIR representation
into the calling circuit's ZKIR representation.
The system is designed to prove the dependent called computation separately,
and to use a dependent "communication commitment" to prove the calling computation.

**A transaction contains a sequence of transitively dependent proofs.**
Presumably these are verified separately on chain,
and the entire transaction atomically succeeds when all of the dependent ones do.

## Dynamic Cross-Contract Calls

### Syntax and Static Semantics

The changes to Compact are relaxations of the restrictions of the static cross-contract call feature.
A circuit is allowed to be passed a contract-typed value (i.e. a contract reference).
This allows invoking transactions that are passed contracts that were potentially unknown at deployment time.
Without loss of generality, we can allow witnesses to return contract values.
(Witnesses are essentially inputs whose production is interleaved with the circuit execution.)
We can also allow contract values to be returned from circuits.

This allows a circuit to make a call to a statically unknown contract,
either immediately or else by storing it in the public ledgers state to be called later.

### Computational Model (Runtime Semantics)

**The DApp provides its own witnesses.**
Contract types and interfaces don't contain witness signatures.
It's not clear how one would obtain the signatures and intended behavior of the required witnesses.
There is conceptually no (new) security issue, the platform assumes that the DApp provides witnesses.
However, to avoid the issues for now and because it's not necessary for, e.g., the decentralized exchange (DEX) use case,
**we propose that we do not allow dynamic cross-contract calls to circuits requiring witnesses**.

Because this is a restriction of the static cross-contract call case, the implementation effort is
expected to be to enforce the restriction (see below).

**The DApp gets the public state of the contract.**
A snapshot of the public state is obtained by the DApp exactly as in the static case.
The snapshot is obtained as before running a transaction offline, based on the contract's address.

**The DApp gets the implementation of the circuit.**
The normal computational model for Compact and for static cross-contract calls is that
the implementation is in the form of JS code.

For dynamic cross-contract calls **we propose that the implementation is in the form of ZKIR code**.
An important realization about ZKIR is that it has two different (related) interpretations.
There is a so-called "relational interpretation" which is defined by translation into the underlying
`midnight-circuits` backend cryptography library.
There is also a so-called "computational interpretation", an operational sematics which is (can be)
defined by a Rust (or other) implementation.

**Open Question: where does the DApp get the circuit's ZKIR code?**
A deployed contract in the ledger contains a map from circuit names to verifier keys (vk).
We need a way to also map a contract address and circuit name to the ZKIR code for the circuit.
We will potentially need to get the prover key (see below) as well.

One possibility is that we also store this in the ledger alongside the verifier key,
which will require ledger changes.
This implementation is less resilient to potential changes to the ZKIR format.
A second possibility is that we embed the ZKIR code as an immutable part of the contract's public state.
This can be in a part of the state that the Compact code does not have access to
(there is no reflective capability to read or manipulate your own ZKIR code).
This doesn't necessarily require ledger changes.
ZKIR has a binary represenation which can be used.
A third possibility is an off-chain mechanism, where we only have to associate a URL (for instance)
with the circuit name somehow.

**TODO: we need to come up with a proposal.**

**Static verification of ZKIR.**
We can verify that the obtained ZKIR circuit produces the same verifier key (vk) as the one
recorded in the contract.
If it does, and there is no mechanism to fetch the corresponding prover key (pk),
we can generate it from the ZKIR (is this sound and safe?).
ZKIR v2 does not have explicit input and output types.
It does have some partial type information but it's not known how well these are reflected in
the verifier key (it only takes instructions into account, essentially?
So it doesn't even reflect the number of inputs unless they all have constraints?).
ZKIR v3 is planned to have a static type system.
Using those static types for cross-contract calls is potentially a new requirement.

We can statically verify **absence of witnesses**.
Witnesses are represented in ZKIR by "private input" instructions and we can statically
verify that they do not occur in a circuit.
Alternately, the execution of ZKIR (below) can simply fail if it encounters such an instruction.

**Static checking of ZKIR is an open issue.**

**The ZKIR circuit is executed in a sandbox in the DApp.**
We can provide a Rust implementation of the operational semantics of ZKIR.
In fact, we already have nearly such an implementation though we haven't tested it in this scenario.
This is not expected to be difficult at all.

When executing ZKIR this way, we also need to execute Impact code for (off-chain) public state
reads and writes using the snapshot of the contract's public state.
Conveniently, ZKIR contains an embedded copy of the needed Impact code!
We previously thought that this was somewhat awkward, but here it turns out to be an advantage.

**Proving and transactions.**
When the DApp constructs proofs and makes transactions,
it does them in exactly the same way as in the static case, using the fetched ZKIR and fetched or computed
prover key.

This is not expected to impose any new implementation requirements.

## An Extended Example

TODO: fill in this section to explicitly describe how a DEX DApp would work.

* A token satisfies an expected interface
* A transaction on the DEX contract can register a new token type
* A DEX DApp can make calls to dynamically registered token circuits

Include a worked example of common DEX scenarios.
