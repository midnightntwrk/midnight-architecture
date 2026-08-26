# Proposal XXXX: Dynamic Contract Composability

**Overview:** we have implemented a facility for contract composability.
The dependencies between contracts are *static* and *fixed* at deployment time.
This proposal describes a limited facility to allow *dynamic* contract dependencies,
which are that can arise after contract deployment.

To motivate the feature we use the example of a decentralized exchange DEX.
The DEX contract exchanges tokens by interacting with token contracts.
New token contracts can be created all the time,
and so the DEX should be able to interact with contracts that it does not know about at (DEX) deployment time.

## 0. Motivating Example: a decentralized exchange (DEX)

We describe a simplified AMM (Automated Market Maker) style DEX.
There are other kinds of DEXs, and we believe the proposal here would also satisfy their requirements.

The components of the DEX consist of **the DEX contract** and the **DEX DApp**.
The DEX contract is deployed to the Midnight blockchain.
DEX Users will typically interact with the DEX contract using the DEX DApp.
In the Midnight network, there is nothing preventing a user from interacting directly with the DEX contract,
rather than using the DEX DApp.
Therefore, the DEX DApp can provide convenience to users, but is not an essential part of the DEX security story.
Note that this is not new for the DEX scenario, it is generally true of Midnight.

Tokens consist of a single component, a **token contract**.
Token contracts are implemented to follow a token standard so that the DEX can interact with them in a stylized way.
For the purpose of this example, we will use the Open Zeppelin `FungibleToken` specification
([documentation](https://docs.openzeppelin.com/contracts-compact/fungibleToken) |
 [source code](https://github.com/OpenZeppelin/compact-contracts/blob/main/contracts/src/token/FungibleToken.compact)).

### 0.1 Token Registration

Token developers can implement new tokens after the DEX is deployed.
They deploy their token contract to the Midnight blockchain, at which point the contract is assigned a contract address.
The DEX contract has a transaction that allows registration of a new token with the DEX.
At that point, the token becomes tradable on the DEX.
Note that it is not necessarily the token developer who registers the token with the DEX.

An AMM-style DEX maintains a **liquidity pool** of tradable tokens, which are owned by the DEX contract.
In order for a DEX users to trade and receive the newly registered token,
there must be some of those tokens available in the liquidity pool.

We could imagine various protocols to establish liquidity for the new token and we are not
specifically concerned with the details.
However, these protocols will possibly
**require the DEX contract to be able to call circuits on the newly-registered token contract**.
For the sake of the example, we consider a very simple protocol where the DEX calls the `transferFrom`
circuit on the newly-registered token to transfer from a specified address to the DEX contract address.

Users could register a new token through the DEX DApp, or by directly interacting with the DEX contract.

### 0.2 Token Trading

Traders can exchange tokens on the DEX.
An AMM-style DEX maintains sets the exchange rate for a token exchange based on the ratio of the tokens available in the liquidity pool.
A user would interact with the DEX through the DApp.
The DApp could tell them the current exchange rate,
and the user could request a trade within a range of exchange rates.
The DApp would fulfill the trade if the exchange rate falls within that range.

The actual exchange, by the DEX contract, requires it to invoke circuits on each of the exchanged tokens.
The specific details could vary.
For simplicity, we consider that the DEX simply calls the same `transferFrom` circuit metioned above.
To exchange a user's $FISK tokens for $HEST tokens (for example), the DEX will transfer $FISK from the user
to the DEX's liquidity pool (the DEX contract address), and transfer $HEST tokens from the DEX's liquidity
pool to the user.

## 1. Context: Static Contract Composability

There were three proposals related to composable contracts:
[0009: Sealed Ledger State](0009-sealed-ledger-state.md),
[0010: Composable Contracts Syntax](0010-composable-contracts-syntax.md), and
[0011: Contract Interface Types](0011-contract-interface-types.md).
As background we first sketch those proposals and the variation that has been implemented.

### 1.1. Sealed Ledger State

Ledger fields in a contract's public state can be declared `sealed`.
The compiler will only allow modification to sealed fields in a contract's constructor;
that is, before the contract is deployed.
Otherwise (after deployment), the compiler will not allow sealed fields to be modified.

This proposal is not directly about composable contracts.
It was used to enforce some restrictions on contract dependencies so that they were static and fixed at deployment time
(restrictions which we are proposing to lift here).

### 1.2. Composable Contracts Syntax

This introduces syntax and (implicitly) a computation model for composable contracts.
Programs consist of a collection of contract declarations,
as well as non-contract utility declarations like types, modules, and pure circuits.
(Pure circuits are ones which can be called without a contract instance.)

A contract declaration introduces a named type (the contract name).
Values of contract types are represented as a reference to the contract (i.e., the contract address).
A value of a contract type can be used to invoke that contract's circuits.
You *cannot* pass contract-typed values to circuits nor return them from circuits.
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
A dependency is represented by a deployed contract address, it must be fixed before deployment.
Therefore, contract dependencies form a DAG.

Note that this does not imply that the cross-contract call graph is fixed.
A contract could be deployed with multiple instances of the same dependent contract type.
It could then conditionally choose between which one of them to invoke.

There is no way in Compact to instantiate a contract.
Contracts are always instantiated and deployed via some extra-linguistic mechanism.

Consequently: there is a static fixed graph of contract dependencies
on preexisting contract deployments, which is established before a contract is deployed.

### 1.3. Contract Interface Types

The final proposal is very simple.
It introduces contract interface types, with an implied (not explicit) subtyping rule
between contract interface types and between contract interface supertypes and contract type subtypes.

Contract dependencies are still static and fixed.
But in the scenario where code is conditionally choosing between multiple dependent contracts to invoke,
they no longer have to all be instances of the same contract type.

### 1.4. What We Actually Implemented

This is basically what we've actually implemented, with some exceptions.

We have not removed top-level impure circuits from programs.
The proposed model was that a program was a collection of named contracts.
The actual model is that a program has an implicit anonymous top-level contract,
with contracts nested inside it (is this nesting only one level deep?).

We did not introduce explicit contract interface types,
but we did introduce a subtyping relation on contract types which gives effectively the same
feature.

## 2. The Implicit (Static) Computational Model

The proposal does not describe in specific terms what the semantics of this syntax is.
There is however, a somewhat obvious computational model that fits with the existing
single-contract coputational model.

Note that this is the downstream (from the compiler) implementation work that we are currently
implementing in the Compact.js and Midnight.js libraries.

A decentralized application (DApp) interacts with a contract.
DApps include applications with a user interface, like a web app or a mobile app.
They can also have only a command-line interface.
There can also be general "DApp-like" tools that can interact more generically with a contract.
An example of such a tool is the *Node Toolkit* that we've built,
which allows deploying contracts without writing any JS code
and making transactions without any extra JS code beyond providing implementations of any required
witnesses.

All of these are collectively called "DApps" below.

In this model, it is the DApp, **not the contract itself,**
that is responsible for making a cross-contract call.

**A. A contract's constructor is invoked from JS code in a DApp.**
This is the normal way that a contract's initial state is constructed.
To configure dependent contract addresses, the constructor is passed an already deployed contract address
and so the contract can be configured with its contract dependencies before deployment.

**B. It's not specified how the JS constructor verifies the static type of the contract dependencies.**
A deployed contract address does not necessarily implement a subtype of the required contract type.
We could verify that it has all of (and perhaps more than) the expected exported circuits.
We could verify that the verifier keys (vks) are expected ones,
but this does not allow configuration with an arbitrary subtype of a contract type.
The code (verifier keys) for exported circuits must match exactly.

**C. When you interact with a deployed contract, you provide your own witnesses.**
The deployed contract can depend on witnesses, which are not deployed on chain with the contract.
Instead, your DApp can configure them with its own witness implementations.
This is not a (new) security hole, it's the Midnight computational model.
Witness return values will be verified to match the constraints expected by the contract.

**D. When a DApp makes a cross-contract call, it must have the JS implementation available.**
Contract dependencies are available as Compact source code, and compiled when the contract is compiled.
The DApp therefore has a JS implementation of the dependent contract available.
Cross contract calls are represented in the JS implementation of a calling contract as calls to
corresponding functions in the JS implementation of the called contract.

**E. The DApp must fetch a snapshot of the dependent contract state.**
A DApp executes a transaction off chain using a snapshot of the public state.
For dependent contract calls, the DApp must have fetched a snapshot of the dependent contract's state.
This is assumed to be fetched using the address of the called contract.
When a transaction is made on the calling contract,
the DApp can already know the addresses of all the transitively dependent contracts.
It can use these addresses to fetch a snapshot of the dependent contract states from an indexer.

**Given the witnesses, JS code, and contract state, we can execute the cross-contract call in the DApp.**

**F. When a cross-contract call is proven, the ZKIR code and prover key is available to the DApp.**
As part of constructing a transaction, the DApp uses the circuit's prover key and a representation
of the circuit in the form of a ZKIR circuit, to prove that the circuit was run with private witness values.
The ZKIR circuit and prover keys are produced by the Compact compiler, and they are available to a
DApp in the same way that the JS code is.

**G. Dependent proofs are constructed separately.**
Because the call graph is not fixed, we did not (cannot) inline the called circuit's ZKIR representation
into the calling circuit's ZKIR representation.
The system is designed to prove the dependent called computation separately,
and to use a dependent "communication commitment" to prove the calling computation.

**H. A transaction contains a sequence of transitively dependent proofs.**
Presumably these are verified separately on chain,
and the entire transaction atomically succeeds or fails depending on the dependent transactions.

## 3. Dynamic Cross-Contract Calls

Like static ones, dynamic cross contract calls are executed by a DApp, not a contract.
The proposal is that we can support dynamic cross contract calls by using the ZKIR representation of a contract's circuits.
For a circuit call on a contract address, a DApp will first fetch a snapshot of the called contract's state from an indexer.
This should be fetched "just in time" before a cross contract call, not before the point that the called contract address is known and the call is inevitable.
The DApp will fetch the ZKIR representation of the called circuit for the called contract.
We discuss various ways to support this capability below.
The DApp can then verify the ZKIR code and generate the prover key for the circuit.
We do not (yet) propose to make witnesses (private state) available to a dynamic cross contract call,
so the DApp will verify the absence of witnesses in for the ZKIR representation or else fail the transaction
if they are used.
Finally, the ZKIR code for the contract is interpreted by Wasm code (compiled from Rust code in the ledger repository) in the on-chain runtime used by the DApp.

### 3.1. Syntax and Static Semantics

The changes to Compact are relaxations of the restrictions of the static cross-contract call feature.
The static feature disallows contract-typed values to appear as circuit parameters or return values,
or witness return values.
Therefore, the only way that a contract-typed value can get *into* a contract is to be passed to the contract's construtor,
or through some extra-linguistic mechanism.

For dynamic cross-contract calls we remove all these restrictions:

* Circuits can have contract-typed parameters.
  This allows transactions to be passed contract addresses, which can have cross-contract calls invoked on them immediately
  or later (by storing the contract address in the public state).
* Witnesses can return contract-typed values.
  Witness return values are conceptually similar to circuit parameters, and there is therefore no real reason to
  restrict contract-typed values from appearing there.
  This allows contract-typed values to also be retrieved from the private state.
* Circuits can return contract-typed values.

### 3.2. Computational Model

**A. The DApp gets the public state of the contract.**
A snapshot of the public state is obtained by the DApp from an indexer.
Unlike the static case, we can not fetch the public state before we know the contract address for a call.
And we should not fetch it before the call is inevitable, so that the DApp does experience a delay for calls that it does not make.

To avoid repeatedly fetching snapshots of the same contract's state, the DApp can cache contract states keyed by the address during transaction construction.

**B. Witnesses are disallowed.**
The normal computational model is that a DApp provides its own witnesses.
In the static composition case, this is a fixed set of witness signatures that a DApp has to provide.
In the dynamic case, it is an open set, depending on the interfaces of the contracts that might be called.
In fact, contract interfaces do not even (yet) contain witness signatures.

Therefore, we disallow dynamic calls to circuits that need witnesses.

*Question: How do we distinguish static and dynamic contract calls.?*
One possible way to distinguish them is that a dynamic contract call is to a contract with an *interface type*.
This requires support for contract interfaces in the language and compiler.

*Question: How do we detect that a circuit call needs witnesses.?*
We can verify that it does not directly use witnesses statically, because we can check whether the ZKIR representation (see below) uses witnesses.
However, we cannot verify that it does not indirectly use witnesses (e.g., via a static cross-contract call).

**C. The DApp gets the implementation of the circuit.**
The normal computational model for Compact and for static cross-contract calls is that
the implementation is in the form of JS code.

For dynamic cross-contract calls **we propose that the implementation is in the form of ZKIR code**.
An important realization about ZKIR is that it has two different (related) interpretations.
There is a so-called "relational interpretation" which is defined by translation into the underlying
`midnight-circuits` backend cryptography library.
There is also a so-called "computational interpretation", an operational sematics which is (can be)
defined by a Rust (or other) implementation.

ZKIR has a binary representation that we can use.
This representation is relatively compact (expected to be smaller than verifier keys in most cases),
and it has not yet been explicitly optimized for size.

**D. Major Open Question: where does the DApp get the circuit's ZKIR code?**
A deployed contract in the ledger contains a map from circuit names to verifier keys (vk).
We need a way to also map a contract address and circuit name to the ZKIR code for the circuit.
There are several ways that we can achieve this.

1. The ledger maintains it as part of the contract reperesentation.
   In addition to mapping a circuit name to a verifier key,
   it also maps the name to the binary ZKIR representation.
   The DApp can then extract this from the called contract.
   This might be ultimately useful for other purposes, and is in some ways the ideal way to do it.
   However, we won't make this change before mainnet so we need to find an alternative way to do it.

2. The calling contract keeps the ZKIR representation for called contracts in its public state,
   associated with the called contract address.
   The DApp has access to a snapshot of the calling contract's public state,
   from which it can fetch the ZKIR representation for an address.

3. The called contract keeps its own ZKIR representation in its public state.
   This does not have to be part of the public state that is accessible to Compact,
   we could design a way for the token contract deployment to manage appending or prepending the binary
   ZKIR encoding of its token circuits.
   This solution has the advantage of being more like (1) above which we might eventually implement.

4. There is an off chain mechanism.
   This would be possible as well, but we don't pursue it below.

Neither solution 2 nor solution 3 require any special compiler support.

In solution 2 for instance,
the transaction that registers a token with the DEX will include the necessary binary ZKIR
representations of the token circuits as an input to the transaction.
This would be encoded as an opaque blob to the contract.
The DEX contract can manage storing this in its public state as a normal contract operation,
and the DEX DApp can find it in the DEX's public state.

In solution 3,
the token needs to be deployed in a special way to ensure that the binary ZKIR representations
are included in a way that should be defined by a token standard,
e.g., an accepted Midnight Improvement Process (MIP) proposal.
If the token is not deployed properly, DApps will not have access to cross-contract calls to its circuits.

**E. Static verification of ZKIR.**
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

**F. The ZKIR circuit is executed in a sandbox in the DApp.**
We can provide a Rust implementation of the operational semantics of ZKIR.
In fact, we already have nearly such an implementation though we haven't tested it in this scenario.
This is not expected to be difficult at all.

When executing ZKIR this way, we also need to execute Impact code for (off-chain) public state
reads and writes using the snapshot of the contract's public state.
Conveniently, ZKIR contains an embedded copy of the needed Impact code!
We previously thought that this was somewhat awkward, but here it turns out to be an advantage.

**Note:** there is nothing proposed that prohibits a dynamic cross contract called circuit from
making dynamic cross contract calls in turn.  This implies that such calls need to evident in the
ZKIR representation, and that the ZKIR interpreter needs to have a way to "call back" to the DApp
to perform a cross-contract call.

**G. Proving and transactions.**
When the DApp constructs proofs and makes transactions,
it does them in exactly the same way as in the static case, using the fetched ZKIR and fetched or computed
prover key.

This is not expected to impose any new implementation requirements.

## An Extended Example

We turn back to the example of an AMM-style DEX, with dynamically registered tokens.
For the sake of discussion, we assume that the DEX contract will maintain a map from token contract addresses
to the binary ZKIR representation of the token.

**A. Writing, compiling, and deploying a token contract.**
This is done as normal.  The contract implements the Open Zeppelin fungible token specification.
It is compiled and deployed as normal, at which time it has a contract address and users can interact with it.

**B. Registering a token using the DEX DApp.**
The token is registered with the DEX.
In the normal case, this would be done by interacting with the DEX DApp.
The registration transaction will include the binary ZKIR representation of the token's circuits required
by the DEX (which could be a subset or even a superset of the OZ fungible token specification).
The transaction will also include a representation of how to deposit initial liquidity for the token,
such as an address and amount.

The DEX registration circuit will, before completing registration, make a cross-contract call
to the token contract to withdraw the initial liquidity.

At the point of the call in the DEX DApp's JS implementation,
the calling code will (a) lookup the token's ZKIR code for the transfer operation from the DEX's public state
and (b) fetch a snapshot of the token's public state from an indexer.
The calling code can be written to verify that the verifier key of the called contract agrees with
the one produced by compiling the binary ZKIR representation.
The call to the token transfer circuit is made from the DEX DApp,
and then the DEX's registration circuit is resumed.
The token transfer therefore occurs synchronously with respect to the calling circuit.

The DApp will produce two proofs as part of the registration transaction,
(1) a proof of the token transfer and (2) a proof of the DEX registration.
Both proofs will be verified on-chain before allowing the transaction.

*Question:* the public state updates for the DEX and token contract are interleaved.
Will this occur properly on-chain?

**C. Registering a token directly with the DEX contract.**
There is no guarantee that users will interact with the DEX contract via the "offical" DEX Dapp,
and the Midnight Network does not rely on this happening.
In reality, a user can construct a DEX registration transaction through any mechanism that works.

To convince the blockchain to accept such a transaction, two proofs must be submitted:
(1) the proof of a token transfer, and (2) a proof of the DEX registration.

*Question:* is there any way to connect the token transfer proof to the registered token,
or is it just generically a proof of some transfer?  What is actually required of this
dependent proof?

**D. Trading tokens using the DEX DApp.**
