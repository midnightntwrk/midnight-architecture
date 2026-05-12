# Proposal 0022: Cross-contract Calls

_[KSM: we need to generate ZKIR for all exported circuits, no only the ones that need a proof.  Mention this.]_

## Abstract

This CoIP proposes to add *cross-contract calls*,
a feature that allows a Compact circuit to directly call exported circuits from other deployed Compact contracts.
With this feature, deployed contracts become first-class Compact values that can be passed as arguments, returned,
written into the public ledger state, and stored in data structures such as `struct` values and tuple values.
Given such a contract value, a Compact circuit is able to call that contract's exported circuits.

## Motivation

Compact contracts do not currently have a way to interact directly with each other.
This rules out numerous useful ways that contracts can interact.
An unsatisfactory workaround is that a DApp can coordinate interactions between contracts.
However, such interactions do not happen on the blockchain and there is no way to ensure that their interaction is correct.

As a motivating example, we consider a simple Uniswap-style decentralized exchange (DEX) using *liquidity pools*.
The DEX allows users to make exchanges between pairs of tokens.
For each pair of tokens that can be exchanged, the DEX maintains a separate liquidity pool containing a reserve amount of both of the tokens in the pair.
Users exchange tokens by interacting with a *router* contract.

The router contract will have an exported circuit similar to this:

```compact
// Exchange `n` of token `a` for token `b`, return the amount of `b` that was received by `key`.
export circuit exchange(key: ZswapPublicKey,
                        a: TokenName,
                        n: Uint<128>,
                        b: TokenName): Uint<128> {
  // <<Exchange `n` `a` for some `b`>>
}
```

Then a user with key `key` can make a transaction like `exchange(key, $FOO, 1, $BAR)` to trade one `$FOO` for some `$BAR` if the transaction succeeds.
We ignore details like how token names are represented, because they are not important to how cross-contract calls work.

The router contract's `exchange` circuit finds the appropriate liquidity pool for a pair of tokens and determines an exchange rate based on the ratio of tokens in the pool.
It then transfers `n` of token `a` for an amount of token `b`.
We are not particulary concerned with the specific implementation of the router.
For simplicity, we imagine that it has a circuit `getPool` that can return a liquidity pool for a pair of tokens:

```
// <<Exchange `n` `a` for some `b`>>
  const lp: LiquidityPool = getPool(a, b);
  // <<Compute `m` = quantity of `b` to receive>>
  // <<Exchange `n` `a` for `m` `b`>>
  return m;
```

The AMM protocol maintains a constant product of the quantity of tokens of both types in the pool.
That computation might look something like this (ignoring any fees taken by the pool, and ignoring issues like rounding and type casting):

```
// <<Compute `m` = quantity of `b` to receive>>
  const [aBefore, bBefore] = // <<Quantity of `a` and `b` in the pool before the exchange>>
  const m = bBefore - (aBefore * bBefore) / (aBefore + n);
```

Crucial to this DEX design is that **the liquidity pools themselves are implemented as contracts**.
Moreover, there is no fixed set of token pairs that the DEX can exchange.
Liquidity pools can be created and registered with the router after the router contract is deployed.
In fact, new tokens can be created after the router contract is deployed.
The question of how liquidity pools get created and registered with the router is an important one,
bit it's outside the scope of this CoIP.

This CoIP proposes to add *cross-contract calls* to Compact.
Cross-contract calls gives a contract, like the router contract, to the ability issue transactions on another contract, like the liquidity pool contract.
For example, in order to compute the quantities of the tokens in the pool, we imagine that there is a circuit in the liquidity pool contract that we can call like this:

```
// <<Quantity of `a` and `b` in the pool before the exchange>>
  lp.quantities(a);
```

If we tell `quantities` which token we want first, it can return a tuple of the quantities of tokens held by the pool.
Likewise, we imagine that there is a circuit that can tell the liquidity pool to exhange quantities of tokens.

```
// <<Exchange `n` `a` for `m` `b`>>
  lp.exchange(key, a, n, m);
```

The liquidity pool needs to know the key of the user and which token is being sold, in addition to the quantities.

Compact is a strongly-typed language.
In order to type check calls such as `lp.quantities(a)` and `lp.exchange(key, a, n, m)` we need to know the signatures of those circuits.

This CoIP proposes to add *contract interface declarations*.
For example:

```
interface LiquidityPool {
  circuit quantities(a: TokenName): [Uint<128>, Uint<128>];
  circuit exchange(key: ZswapPublicKey, a: TokenName, n: Uint<128>, m: Uint<128>): [];
}
```

A contract interface declaration introduces a named *interface type*, which is a new kind of program-defined Compact type.
Values of interface type represent deployed contracts.
They are first-class values: they can be passed to circuits and witnesses, returned, written into a contract's public ledger state, and stored in Compact data structures like `struct` values, tuples, vectors.

## Specification

### Overview of the Proposal

In the current Compact system, a Compact circuit such as the DEX router's `exchange` circuit in the example is executed off-chain as JavaScript (JS) code generated by the Compact compiler.
As a side effect of this execution, the Compact runtime JS package builds so-called *partial proof data*.
The partial proof data records the return values of witness calls, the Impact VM code that was executed (off-chain) to perform public state updates, and the results of ledger operations.
The partial proof data is encoded using *field aligned binary* (FAB).
FAB is the Midnight ledger's data format, which is a binary encoding as blobs of bytes, along with *alignment tags* that tell how to decode the bytes as sequences of field values in the underlying cryptographic field.
The partial proof data is "partial" because not all control-flow paths through the circuit were taken during execution.

After executing the circuit, a ZK proof is constructed, proving that the public and private inputs in the partial proof data are correctly related according to the circuit's implementation.
Proof construction uses a representation of the circuit as ZKIR (the **Z**ero **K**nowledge **I**ntermediate **R**epresentation).
ZKIR is low-level binary encoding of the circuit, which is generated by the Compact compiler in addition to the JS implementation of the circuit.
The FAB-encoded partial proof data collected during off-chain execution is converted into ZKIR-typed values and used as an input to the proof construction, along with the ZKIR representation and a Compact-compiler-generated prover key.
The ZKIR-typed representation of the partial proof data is the so-called *proof preimage*.

In order to perform a off-chain execution of a cross-contract call, we must first obtain the code for the called circuit.
There is currently no trusted way to obtain the Compact code for the circuit.
Nor is there any trusted way to obtain the JS implementation.
However, the binary ZKIR representation of exported circuits is going to be stored on-chain in the Midnight blockchain.
This is a feature that will come in a future version of the Midnight ledger (likely version 9).
We propose to execute cross-contract calls off-chain by **interpreting the ZKIR representation of the called circuit**.
Interpreting ZKIR will directly construct a proof preimage (rather than the FAB-encoded partial proof data).

As a simplification, we could also modify the JS partial proof data to be a ZKIR-typed proof preimage, but this implementation work is not necessary at this time.

Proof construction also requires the circuit's prover key.
This can be constructed from the ZKIR representation, though the time taken to construct the prover key might be prohibitive.
The size of prover keys might make it infeasible to store them on-chain.
We can investigate ways to cache prover keys off-chain.

The Compact compiler-generated JS code does not itself construct transactions or make proofs, this is performed by an outer layer of the system we will call "Midnight.js".
This component is also responsible for fetching a copy of a contract's public state to pass to the JS circuit implementation.
We propose that **this layer is also responsible for performing cross-contract calls**.
The JS-generated contract code will perform a callback to Midnight.js (possibly through the so-called *circuit context* passed to the JS code).
The callback is given the called contract's address, the circuit name, and the arguments.
It returns the return value of the cross-contract call, and collects the proof preimage that it needs to make the ZK proof.

### Contract Interfaces

#### Interface Declarations

An interface declaration introduces a named *interface type*.
This is a new kind of Compact type describing the exported circuits of a deployed contract.

In the Compact grammar, the `contract-declaration` program element is replaced with `interface-declaration`.
The key syntactic differences are:

- The interface declaration uses the `interface` keyword instead of `contract`.
- Interface declarations can be generic.
- Circuit declarations cannot contain the `pure` modifier.

```
interface-declaration → exportᵒᵖᵗ interface contract-name gparamsᵒᵖᵗ { circuit-declaration ; ⋯ ; circuit-declaration ;ᵒᵖᵗ } ;ᵒᵖᵗ
                      | exportᵒᵖᵗ interface contract-name gparamsᵒᵖᵗ { circuit-declaration , ⋯ , circuit-declaration ,ᵒᵖᵗ } ;ᵒᵖᵗ

circuit-declaration   → circuit id simple-parameter-list : type
```

An interface declaration contains one or more circuit declarations describing exported circuits of a deployed contract.
Circuit declarations define a circuit's signature, but not an implementation.
Therefore, they do not have a body.
Because exported circuits cannot be generic, neither can circuit declarations.
The parameters of circuit declarations are named, but the names are merely cosmetic.
They can be useful to indicate intent and the names can be used in documentation to refer to specific parameters.

_[KSM: We could allow zero or more (rather than one or more) circuit declarations.
This would allow an interface that was the supertype of all interface types.
I'm not sure how that would be useful, though.]_

An interface exported from a module can be imported into a contract or another module.
_[KSM: What does it mean to export an interface from the top-level of a contract?]_

The scope of the generic parameters of an interface declaration are visible in the body of the declaration.

In this proposal, interface declarations do not contain other kinds of declarations such as modules, `struct` or `enum` types, type aliases, `ledger` declarations, witnesses, or constructors.

##### Examples

_[KSM: We could use the signatures of some of the the OZ fungible token circuits to make this more realistic.]_
A simple contract interface describing a fungible token:

```compact
contract interface FungibleToken {
    circuit transfer(from: Bytes<32>, to: Bytes<32>, amount: Field): Field;
    circuit balance(owner: Bytes<32>): Field;
}
```

A contract interface may be exported from a module so that it can be imported by other programs:

```compact
module TokenStandard {
    export contract interface FungibleToken {
        circuit transfer(from: Bytes<32>, to: Bytes<32>, amount: Field): Field;
        circuit balance(owner: Bytes<32>): Field;
    }
}
```

#### Interface Types

An interface declaration defines an interface type, a new kind of program-defined type.
An interface type represents an unordered collection of named circuit *signatures*.
Circuit signatures have an ordered sequence of zero or more Compact types that are the *parameter types*, and a Compact type which is the *return type*.
Note that the parameters in circuit signatures are ordered but they are unnamed.

A Compact value of an interface type represents a deployed contract.
Values of interface types are first-class values: they can be passed to circuits and witnesses, returned, and stored in structures like `struct` values, tuples, or vectors.
They also support the operation of calling one of the named circuits, by passing the required number of parameters of the required types.
The type of such a cross-contract call is the circuit signature's return type.
The value of such an cross-contract call is a Compact value of that return type.

A non-generic interface declaration introduces a named interface type, where the names of the circuits are the names from the circuit declarations, and the signatures have the parameter types in the same order as the corresponding circuit declaration, with the return type specified by that circuit declaration.

A generic interface type declaration does not itself introduce an interface type.
An attempt to use it (without specialization) is a static error.
When specialized, such a declaration introduces 


needs to be specialized 

#### Subtyping

There is a subtyping relation on interface types.
A Compact value of interface type can be used wherever a value of a supertype is expected.
A supertype has a subset of the subtype's named circuits, where each circuit has a compatible signature.
Interface subtyping is structural: the subtyping relation is not declared explicitly in the program, but instead it holds whenever the types are in the relation defined below.

To define interface subtyping, we first define *signature subtyping*.  A signature `(T0, ..., Tm) -> T` is a signature subtype of a signature `(S0, ..., Sn) -> S` iff:

- `m` = `n`,
- for each `i` in 0..`m`, `Si` is a subtype of `Ti`, and
- `T` is a subtype of `S`.

Then we define that an interface type `I` is a subtype of an interface type `J` iff, for each named signature in `J`:

- there is a signature with the same name in `I`, and
- that signature in `I` is a signature subtype of the signature in `J`.

#### 1.2 Structural Conformance

_[KSM: I think this is describing a runtime check, but by placing it here it reads like it's describing a static check.  We should move it later in the proposal.]_

When a caller declares that it expects a contract of type `T`, and a concrete callee address arrives at runtime, the system must determine whether the callee conforms to `T`.
There are two classical approaches to this question: nominal conformance (the callee explicitly declares that it implements `T`) and structural conformance (the callee's circuit signatures match those required by `T`).
We consider both, and argue that structural conformance is the right foundation for Compact.

##### The case for nominal conformance

Nominal conformance requires explicit intent.
A contract would declare something like `implements FungibleToken`, and only contracts bearing that declaration would be accepted where a `FungibleToken` is expected.
This prevents accidental conformance — the classic example being two interfaces with identical signatures but different meanings:

```compact
contract interface Killable {
    circuit kill(): [];    // destroy the contract
}

contract interface GameCharacter {
    circuit kill(): [];    // remove a life in a game
}
```

Under structural conformance, a `GameCharacter` would accidentally satisfy `Killable`.
Nominal conformance prevents this by requiring the programmer to state which interfaces a contract intends to implement.

##### Why nominal conformance is insufficient for Compact

Compact contracts are compiled and deployed independently.
There is no global namespace for contract type names across independent compilation units.
When Alice deploys a DEX with a `contract interface FungibleToken { ... }` declaration, and Bob separately deploys a token contract with his own `contract interface FungibleToken { ... }` declaration, the name `FungibleToken` is not shared between them — it exists independently in each compilation unit.
For nominal conformance to work, there would need to be some shared notion of identity that both Alice and Bob agree on.
This would require either a global interface registry or an interface description language distributed out of band.

More fundamentally, nominal conformance does not prevent the attack it appears to prevent.
A malicious contract can declare `implements FungibleToken` and then implement a `transfer` circuit that does something entirely different from what the caller expects.
The `implements` declaration is a claim of intent, not a proof of behavior.

##### Why structural conformance is the right foundation

A sound type system should only promise what can actually be verified at runtime.
At runtime, the system can inspect the callee's circuit signatures — their names, parameter types, and return types — and check whether they match the caller's expectations.
It cannot inspect whether the callee "intended" to implement a particular interface, because intent is not an observable property of deployed code.

Structural conformance aligns the compile-time guarantee with the runtime guarantee: the compiler checks that the caller only uses circuits declared in the expected interface, and the runtime checks that the callee actually has those circuits with compatible signatures.
There is no gap between what the type system claims and what the runtime enforces.

##### Nominal conformance as an ecosystem convention

Rather than being enforced by the core type system, nominal conformance is relocated to ecosystem conventions - interface standards can be established, e.g., via Midnight Improvement Proposals (MIPs).
A MIP can define a canonical `FungibleToken` interface with specific circuit signatures, and tooling, auditors, and marketplaces can verify that a contract conforms to the standard.

### Cross-Contract Calls

The Compact syntax `expr . id ( expr0 , ⋯ , exprn ,opt )` where `expr` has an interface type is a *cross-contract call*.

All of the following are static errors:

- there is no signature `(T0, ..., Tm) -> T` with name `id` in the interface type,
- `m` does not equal `n`,
- for all `i` in 0..`m`, the static type of `expri` is not a subtype of `Ti`.

The type of a cross-contract call is the return type `T` from the corresponding signature.

#### 2.1 Calling Circuits on Contract References

The `e.c(args)` syntax for invoking a circuit on a contract-typed expression.

### 3\. Static Semantics (Kevin)

#### 3.1 Typing Environments

The environments needed for type checking:

- Variable environment (Γ)  
- Contract signature environment (Δ)  
- Interface signature environment (Σ)

#### 3.2 Typing Rules

Rules for type-checking circuit calls, including:

- Looking up circuit signatures  
- Verifying argument types  
- Subsumption

### 4\. Execution and Communication Model (Joe - Done)

Sections 1 through 3 describe contract interfaces and cross-contract calls as language-level concepts, independent of any particular blockchain.
This section turns to the concrete realization on Midnight: how the ZKIR interpreter executes cross-contract calls, how communication commitments bind caller and callee proofs together, and how the resulting transcripts compose into a single transaction.

#### 4.1 Architectural Change: ZKIR as the Execution Engine

Today, the Compact compiler produces two artifacts per contract.
A JavaScript file serves as the execution engine during rehearsal — it runs the circuit logic, calls witnesses, reads and writes ledger state through Impact VM, and builds the public and private transcripts.
A separate ZKIR file compiles into a zero-knowledge circuit whose sole purpose is proving that the transcripts were produced honestly.
The JS executes; the ZKIR verifies.

This proposal collapses the two artifacts into one.
The Compact compiler will emit ZKIR as the sole computational artifact, and a new `execute` method on `IrSource` — distinct from the existing `preprocess` method, which validates proof preimages — will serve as the execution engine.
The only JavaScript that survives is a thin binding layer in `zkir-v3-wasm` for converting TypeScript values to and from ZKIR field-element representations.
Witness callbacks are not supported for any contract under this proposal (see §4.6).

Replacing the JS executable means the ZKIR interpreter must also take over ledger operations.
Today, the JS executable calls into the `onchain-runtime` WASM API to execute Impact VM bytecode — the stack-based instruction set that reads, writes, and mutates contract state.
ZKIR already has an `impact` instruction, but it currently serves only the proving circuit: it declares conditional public inputs and validates that previously-computed values match what was committed to.
It does not execute the ledger operations itself.
The `execute` method must evaluate Impact VM bytecode against the contract's ledger state, building the public transcript as it goes.

This architectural change also requires a change to what the ledger stores at deployment time.
Today, the on-chain `ContractState` stores a verifier key per entry point (via `ContractOperation`), but not the ZKIR itself — the ZKIR lives only on the deployer's device, used locally for proving.
This is sufficient when every user who calls a contract already possesses its ZKIR (bundled with the DApp).
It is not sufficient for dynamic cross-contract calls, where contract A calls contract B without A's developer ever having seen B's code.
This proposal requires that the deployer's ZKIR be stored on-chain as part of the contract's state, alongside the existing verifier keys.
When contract A dynamically calls contract B, the interpreter fetches B's ZKIR from the ledger and executes it directly — no out-of-band artifact retrieval, no second compilation step.

#### 4.2 The `contract_call` Instruction

This proposal introduces a new instruction to ZKIR v3: `contract_call`.
When the Compact compiler encounters a cross-contract call expression `e.c(args)`, it emits a `contract_call` with four groups of operands: the contract-reference value (the result of evaluating `e`, which resolves to a contract address at runtime), the circuit name `c` (identifying the callee's entry point), the argument values to pass as inputs, and the output identifiers that will receive the callee's return values.
`contract_call` is the sole mechanism by which one contract's ZKIR can invoke another's.

#### 4.3 Circuit Call Evaluation

When the interpreter encounters a `contract_call` during rehearsal, evaluation proceeds as follows.

First, the interpreter resolves the contract reference operand to a concrete address and fetches the callee's ZKIR from the blockchain.
If the address does not correspond to a deployed contract, execution fails immediately.

Next, the interpreter performs the structural conformance check described in §5.5: it extracts the callee's circuit signatures from the fetched ZKIR and verifies that the callee is a structural subtype of the caller's expected contract type.
A failed check aborts the execution.

With conformance established, the interpreter gathers the caller's argument values and passes them as the callee's input vector.
No encoding conversion occurs at this point: the Compact compiler has already flattened all structured types to field elements at compile time, and the conformance check has verified that both sides agree on the layout.

The interpreter then fetches a snapshot of the callee's ledger state (the callee's circuits may read or write their own ledger) and recursively executes the callee's ZKIR in an isolated context: its own ledger snapshot, its own transcript, and no witness callbacks.
If any circuit encounters a `private_input` instruction — that is, if the circuit's implementation requires witness data — execution fails immediately.
This restriction confines cross-contract calls to circuits that operate only on ledger state and caller-provided inputs (see §4.6).
The callee may itself encounter `contract_call` instructions, leading to further recursion under the same constraint.

When the callee finishes, the interpreter collects its output values (those designated by `output` instructions in the callee's ZKIR) and writes them into the caller's output identifiers.
It then computes a communication commitment that cryptographically binds the call's inputs and outputs:

```
comm_comm = transient_commit(concat(input, output), rand)
```

where `input` and `output` are the field-element sequences representing the argument and return values and `rand` is fresh randomness.
Finally, the interpreter records a contract-call claim in the caller's public transcript — an Impact VM operation containing the callee's address, the entry-point hash, and the commitment value.
The node will match this claim against the callee's proof during verification.

#### 4.4 Communication Commitments

Each contract in a cross-contract call produces its own zero-knowledge proof independently.
The communication commitment is what ties these proofs together: it is a Poseidon hash over the input and output values that crossed the call boundary, and it must appear — identically — in both the caller's and the callee's proofs.

On the callee's side, the ZKIR circuit (with `do_communications_commitment` enabled) constrains that `public_input[1] == poseidon(binding_input, inputs..., outputs...)`.
The callee's proof therefore attests: "given these inputs, I produced these outputs, and here is a commitment to that fact." On the caller's side, the public transcript contains a claim: "I called contract A at entry point E with communication commitment C." The node verifies that every such claim has a matching callee proof whose commitment is identical.

The commitment binds field-element values, not Compact-level types.
Each contract's ZKIR determines how it interprets those field elements.
This is why the structural conformance check (§5.5) must run before the call: it ensures both sides agree on the type layout so that the field elements flowing through the commitment are interpreted consistently.
The commitment does not bind behavior — a `transfer` circuit that passes the conformance check could still send tokens to the wrong address.
No type system prevents behavioral incorrectness; the commitment guarantees only input-output consistency.

#### 4.5 Transcript and Proof Composition

A transaction involving cross-contract calls produces one transcript per contract execution.
These transcripts are proven independently and assembled into a single transaction.

During rehearsal, the interpreter begins with the top-level circuit.
Each `contract_call` triggers recursive execution of the callee, and each execution accumulates its own public transcript (ledger operations, contract-call claims) along with the communication commitment for each call.
No contract produces a private transcript, since witness callbacks are not available under this proposal (see §4.6).

After rehearsal completes, the flat list of executions is organized into a call forest by `partition_transcripts`, which matches each caller's contract-call claims to the corresponding callee executions using their commitment values.
The output is a tree of `ContractCallPrototype` objects — one per execution — each carrying the contract address, entry point, partitioned transcript segments, input/output values, and commitment randomness.

Each prototype is proven independently.
The callee's proof constrains the communication commitment; the caller's proof includes the commitment as a public input via the claim in its transcript.
The node verifies every proof, then checks that every claim is matched by a callee whose commitment is identical.
An unmatched claim causes the transaction to be rejected - in the current codebase, this is the `RealCallsSubsetCheckFailure` error path.

Finally, assuming all proofs verify and all claims match, the node replays the public transcripts against its current ledger state.
Each contract's state mutations are applied in call-tree order.
If the replay produces the same intermediate results as the rehearsal the transaction is accepted and the block is extended.

#### 4.6 Witness Limitation

Under this proposal, witness callbacks are not available for any contract involved in a cross-contract call — including the top-level caller.
If any circuit in the call tree encounters a `private_input` instruction during execution, the transaction fails immediately.
All contracts are restricted to operating on ledger state and caller-provided inputs.

This is a deliberate simplification.
Provisioning witnesses requires the DApp to anticipate and supply callbacks for every contract in the call tree, including contracts that may not be known at DApp build time.
Solving this problem is deferred to a subsequent CoIP.
The restriction applies uniformly rather than only to callees in order to keep the execution model consistent: every contract in the call tree operates under the same constraints, and no contract produces a private transcript.

### 5\. Runtime Interface Verification (Joe - Done)

The structural conformance rules defined in §1.2–1.3 are enforced at compile time when the callee is statically known.
For dynamic cross-contract calls, the callee is not known until rehearsal time, and the compiler has never seen it.
Soundness of the type system therefore requires a runtime conformance check: when a contract address arrives as a circuit argument, the runtime must verify that the contract at that address is a structural subtype of the caller’s expected contract type before allowing any calls to proceed.

This section considers how to represent the type information needed for that check, examines the design space, and identifies a security constraint that narrows the viable options.

#### 5.1 The Problem of Type Representation

The conformance check requires two pieces of information:

1. The **caller’s expected type**: the contract type `T` that the caller declared in its source code.
   The caller’s compiled artifact must carry this information so the runtime knows what to check against.
2. The **callee’s actual type**: the circuit signatures that the deployed callee contract actually exposes.
   This information must be available on-chain, since the callee was compiled and deployed independently.

The challenge is that Compact’s type system, ZKIR’s type system, and the on-chain representation operate at different levels of abstraction, and type information is lost as it moves down the stack:

- **Compact** has a rich type system: `Field`, `Uint<N>`, `Bytes<N>`, `Boolean`, structs, enums, tuples, vectors, contract types, generic type parameters, type aliases, and `new` types.
  These are the types that appear in circuit signatures and that the subtyping rules of §1.3 operate on.
- **ZKIR v3** currently has a minimal type system: `Native` (a BLS12-381 scalar field element) and `JubjubPoint`.
  When the Compact compiler emits ZKIR, structured types are flattened into sequences of field elements.
  For example, given struct `struct A { u: Field }`, the structs `struct C { w: Field, x: A }` and a `struct D { y: A, z: Field }` compile to the same ZKIR representation (a sequence of `Field` values), even though they are distinct Compact types with different subtyping relationships.
- **The Field Aligned Binary (FAB) format** describes the physical layout of values as sequences of field elements and byte strings.
  FAB alignment descriptors distinguish between `Field`, `Bytes { length }`, and `Compress` atoms, but they do not preserve semantic type distinctions.
  A struct and a tuple with the same field types have the same FAB alignment.

The runtime conformance check requires type information that is richer than what ZKIR or FAB currently provide, but it does not need the full expressiveness of Compact’s type system.
It needs the *resolved, monomorphized types at circuit boundaries* — the concrete types of circuit parameters and return values after all generic instantiation, alias resolution, and module expansion has been performed.

#### 5.2 Approaches Considered

We considered three approaches to bridging this gap between Compact’s type system and the on-chain representation.
Each has different trade-offs in terms of architectural cleanliness, security, and implementation effort.

##### Approach A: Separate on-chain type descriptor

Each deployed contract stores a type descriptor — a serialized representation of its circuit signatures using Compact-level types — as metadata alongside its on-chain state.
The caller’s ZKIR (or accompanying metadata) contains the expected contract type.
The runtime conformance check compares the callee’s stored descriptor against the caller’s expected type using Compact’s subtyping rules.

This approach provides the most precise conformance checking, since it operates directly on Compact-level types.
However, it means the on-chain representation carries Compact-specific type information, which couples the ledger layer to a specific source language.
This is architecturally undesirable because its a dependency inversion: the ledger should be agnostic to the source language that produced the contracts it stores.

The descriptor could be stored as an opaque blob that only Compact tooling interprets, which avoids the ledger itself parsing Compact types.
But the coupling remains — the blob’s format is defined by and for the Compact compiler, and any future language targeting ZKIR would need to produce compatible descriptors or introduce its own.

##### Approach B: Enrich ZKIR’s type system

Rather than storing a separate descriptor, ZKIR’s type system could be extended with richer types — bounded unsigned integers, fixed-length byte strings, structs, enums, and so on — similar to how LLVM IR supports `i32`, arrays, and structs even though the underlying hardware operates on bits.
The Compact compiler would compile Compact types to ZKIR types with less loss, and the ZKIR stored on-chain would carry enough type information for the conformance check.

This approach is architecturally cleaner.
ZKIR is already the language-independent intermediate representation; enriching its types maintains the layering between source language and execution format.
It follows the precedent set by the JVM (whose bytecode carries class and method signatures for the bytecode verifier, even though the CPU doesn’t use them), the .NET CLR (whose Common Type System provides a shared type vocabulary across source languages), and WebAssembly’s Component Model (whose WIT interface types are richer than core Wasm types but simpler than any source language’s type system).

The trade-off is that ZKIR’s types serve double duty: they describe circuit structure for the proving system (where everything reduces to field elements) and circuit interfaces for the conformance checker (where type distinctions matter).
The types would exist for the interpreter and conformance checker but would be erased during proving.
This split — types for verification, not for execution — is standard in intermediate representations and is not an architectural smell.

The key design question is the vocabulary of ZKIR types.
It must be expressive enough to capture the Compact types that appear at circuit boundaries (the "surface area" of a contract’s interface), but it does not need to represent every type that can exist inside a circuit body.
This vocabulary is naturally bounded: any type that can appear as a circuit parameter must be serializable into the public transcript, which constrains it to a finite set of type constructors.

##### Approach C: A language-independent interface description format

A dedicated interface description language — analogous to WebAssembly’s WIT, Android’s AIDL, or COM’s IDL — could be defined at the Midnight platform level.
This format would describe circuit signatures using types that are richer than ZKIR’s current types but independent of any source language.
Compact would compile contract interface declarations down to this format; hypothetical future languages targeting Midnight would do the same.

This approach provides the cleanest separation of concerns, but it introduces a new artifact format that must be designed, versioned, and maintained.
Given that Midnight currently has one source language, a full IDL may be premature.
If a second language emerges, the IDL could be extracted from ZKIR’s type system at that point.

#### 5.3 Security Constraint: Binding Types to Code

Any approach that stores type information separately from the executable ZKIR introduces a security vulnerability.
If the type descriptor (or enriched type annotations) and the executable ZKIR are independent artifacts, an attacker can deploy a contract where the type information claims one interface while the ZKIR implements a different one.

Consider this attack in the DEX scenario:

1. An attacker deploys a contract whose type descriptor claims: `circuit transfer(from: Bytes<32>, to: Bytes<32>, amount: Uint<64>): Field`.
2. The DEX checks the descriptor, sees it conforms to `FungibleToken`, and allows the token to be registered.
3. The actual ZKIR stored on-chain interprets the input field elements differently — perhaps the "amount" parameter is treated as a destination address, or the circuit unconditionally transfers tokens to the attacker rather than to the specified recipient.
4. The communication commitment binds the caller and callee to the same *field element values* for inputs and outputs, but the *interpretation* of those field elements is determined by the callee’s ZKIR, not by the type descriptor.
   The commitment ensures that specific values went in and specific values came out; it does not ensure that the callee treated those values as the types the descriptor claims.

This attack is distinct from ordinary behavioral incorrectness.
Even with a perfectly honest type descriptor, a `transfer` circuit could transfer tokens to the wrong address — no type system prevents that.
But without type binding, the attacker can deceive the caller about the structural interface itself: the caller believes it is passing a `Uint<64>` amount parameter, but the callee interprets those same field elements as something entirely different.

To prevent this attack, the type information must be **derived from or cryptographically bound to the executable ZKIR**.
The viable options are:

1. **Types are embedded in the ZKIR itself** (Approach B).
   The ZKIR is both the executable and the type descriptor.
   The node can type-check the ZKIR at deployment time to verify internal consistency.
   There is no separate artifact to forge.

2. **Types are derived from the ZKIR by the node at deployment time.** The node parses the ZKIR, extracts circuit signatures with their types, and stores the derived descriptor on-chain.
   The descriptor is a deterministic function of the ZKIR, so an attacker cannot forge it without also changing the ZKIR (which would change the verifier key and invalidate existing proofs).

3. **Types are cryptographically committed alongside the ZKIR.** The verifier key is computed over both the ZKIR and the type descriptor, so changing either one without the other invalidates the key.
   This allows a separate descriptor but binds it to the code.

All three options converge on the same requirement: **the ZKIR must carry enough type information to either serve as the descriptor directly or to allow one to be derived from it.** A user-supplied descriptor that is not bound to the ZKIR is not trustworthy.

This security constraint is a strong argument for Approach B.
If ZKIR must carry rich types anyway — either as first-class types in its type system or as metadata annotations that the node extracts at deploy time — then the type descriptor is not really a separate artifact.
It is an intrinsic property of the ZKIR, and the simplest representation is to make it part of ZKIR’s type system directly.

#### 5.4 Recommendation

This proposal recommends Approach B: enriching ZKIR’s type system to carry the type information needed for runtime conformance checking.

The security analysis in §5.3 narrows the design space considerably.
Approach A (a separate on-chain descriptor) is viable only if the descriptor is cryptographically bound to the ZKIR, but at that point the descriptor is no longer independent — it is derived from the ZKIR.
Approach C (a standalone IDL) introduces the same binding problem plus the overhead of a new artifact format for an ecosystem that currently has one source language.
Approach B avoids these problems by making the ZKIR the single source of truth for both execution and type information.
The types are embedded in the artifact that the node stores, validates, and executes (per the on-chain ZKIR storage requirement introduced in §4.1), so there is no separate artifact to forge and no additional binding mechanism to design.

ZKIR v3’s type system must be extended from its current two types (`Native` and `JubjubPoint`) to a vocabulary rich enough to distinguish the Compact types that appear at circuit boundaries — at minimum: unsigned integers, fields, byte strings, booleans, structs, enums, vectors, and contract references.
The proving system does not need these types (it operates on field elements), so they exist solely for the interpreter and conformance checker.
This is the same split that, e.g., JVM makes: types for verification, erased during execution.

The detailed design of the enriched ZKIR type vocabulary is outside the scope of this proposal and will be addressed in a companion ZKIR specification.
This proposal assumes only that ZKIR will carry sufficient type information to perform the conformance check described in §5.5.

#### 5.5 Runtime Conformance Check

Given the above, the runtime conformance check proceeds as follows.

At deployment time, the node validates that the contract’s ZKIR is well-typed according to ZKIR’s enriched type system.
This includes verifying that the types of circuit inputs and outputs are internally consistent and that no type annotations have been tampered with.
If the ZKIR fails type-checking, deployment is rejected.

At rehearsal time, when a contract address enters the caller’s execution as a circuit argument, the ZKIR interpreter performs the structural conformance check:

1. The caller’s ZKIR contains the expected contract type `T` — a set of circuit signatures with their parameter and return types, as compiled from the Compact source.
2. The interpreter fetches the callee’s ZKIR from the ledger (stored on-chain at deployment time per §4.1).
3. The interpreter extracts the callee’s actual circuit signatures from the callee’s ZKIR.
4. The interpreter checks that the callee’s circuit signatures form a structural subtype of `T`, applying the subtyping rules of §1.3.
5. If the check fails, the transaction construction fails and no proof is produced.

There are two scenarios in which the conformance check is performed:

1. When a contract is passed as an argument to an exported circuit (including the constructor).
2. When a `contract_call` instruction is processed (defensively, since all contract values in ledger state ultimately originate from circuit arguments that have already been checked).

### Acceptance Criteria

### Implementation Plan

## Backwards Compatibility Assessment

- Andy’s question \- what kind of versioning system for ZKIR are we assuming here? What if callee and caller ZKIR versions differ?

## Security Considerations

- Type safety  
- Interface verification  
- Behavioral safety (interfaces don't guarantee correct behavior)  
- Reentrancy  
- Witness limitation and its implications  

## Testing

## References

## Acknowledgements

## Copyright Waiver

---

Need to figure out sections where Kevin’s questions from the original draft “[dynamic-contract-composability.md](http://dynamic-contract-composability.md)” document are answered.

* What distinguishes dynamic calls from static calls?  
* Where does the DApp get the circuit's executable representation?  
* Static verification of executable representation  
* Public state updates interleaving  
* Connecting proofs to specific contracts  
* Witnesses disallowed for dynamic calls — how enforced? — **Answered**: Runtime enforcement by the ZKIR interpreter.
* Contract interfaces don't contain witness signatures — **Answered**: See §1.1 "What a contract interface declaration does not contain."
* Dynamic calls making dynamic calls (recursion) — **Answered**: See §4.3 — recursive `contract_call` is supported under the no-witness constraint.
* Can contract types appear in circuit params/returns/witness returns? — **Answered**: See §1.1 "Restrictions on contract-typed values" table.

Joe’s open questions:

* **Q**: ZKIR v3 will have typed values.
  But, value types are *not* actual inputs to the proof, meaning they’re not reflected in the prover / verifier keys for the ZKIR.
  Then, how can the argument types declared in the ZKIR be trusted? Is there an attack vector in which callee “checks” the parameter types for interface conformance but callee has somehow used adversarial parameter types?  
**A**: We can type check ZKIR and refuse to execute if it’s not well typed.
  When does type-checking occur? On the node at deployment or by the user on invocation? If the former, then we have to think about DDOS protection.
  Type checking has to be efficient / costed.

* **Q**: When and how do we efficiently check that the retrieved ZKIR and verifier key match?
