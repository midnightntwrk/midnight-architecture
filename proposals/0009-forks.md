# Proposal 00009: Upgrades with forks

## Problem Statement
Midnight's design and capabilities, similarly to other chains, are not set in 
stone. There are many known and unknown protocol changes in the future, which will require a clear protocol, mechanism and policy for upgrades, so that they can be delivered to Midnight users without: 
- putting Midnight network to stop
- causing operational inconveniences to people running Midnight nodes 
- Midnight value at risk
- users data at risk
- users funds at risk

In particular, with following good practices which enable engineering teams to progress, certain properties of the solution should be kept:
- separation of ledger and consensus
- ledger transaction validation a pure function
- ledger state evolution a pure function
- different ledger versions oblivious of each other
- separation of ledger and Substrate APIs

It is recognized, that there are aspects of the problem, which are not necessarily considered primary concerns, but should be taken into consideration, when evaluation different options:
  - centralization, in various forms: code, implementation, governance
  - overall flexibility
  - block validation time
  - historic block validation throughput 

Focus for this proposal is on changes requiring hard-forks (see [Glossary](../product/Glossary.md)) because of their inherently trickier nature. It is very likely though, that the same protocol, mechanism and policy would apply to changes requiring soft-forks for consistency.

## Prior art

### Bitcoin

Bitcoin seems to have a strong policy against hard-forks, which directly led to inception of Bitcoin Cash.

So far only 2 hard forks occurred on Bitcoin, and both were incidental:
  - one from 2018: https://bitcoincore.org/en/2018/09/20/notice/
  - one from 2013: https://github.com/bitcoin/bips/blob/master/bip-0050.mediawiki

All the other updates are implemented through soft-forks.

The policy and protocol are explained in a series of BIPs:
  - [BIP-34](https://github.com/bitcoin/bips/blob/master/bip-0034.mediawiki) for the basic policy
  - [BIP-8](https://github.com/bitcoin/bips/blob/master/bip-0008.mediawiki) and [BIP-9](https://github.com/bitcoin/bips/blob/master/bip-0009.mediawiki) for scheduling multiple deployments concurrently, with possibility to time out ones not getting enough support

An example of a change implemented following that: https://github.com/bitcoin/bips/blob/master/bip-0066.mediawiki

In short, Bitcoin's approach is as follows:
  - take advantage of the fact, that block version number has more bits available, than reasonably needed to encode a single version number, to encode next version number too
  - enable new rules when 750 block out of last 1000 has encoded related next version
  - don't accept blocks with older versions when 950 out of last 1000 blocks has encoded related next version

In other words, if current version of block is `1`, and new rules are related to block version `2`:
  - old client software would be able to produce blocks `1` and would encode next version as `1` too (if at all)
  - new client software would be able to produce blocks `1` and `2`, and would encode next version as `2`
  - miners encode next version accordingly to capabilities of their software
  - once 750 out of 1000 blocks have encoded next version 2 - new rules are enabled for all blocks
  - once 950 out of 1000 blocks have encoded next version 2 or greater - blocks of version 1 are not valid anymore

### Ethereum

Ethereum approach is slightly different one - whenever a fork-requiring change is planned, it is specified with activation block height on networks maintained at the moment of planning.

Then, clients simply check for a block height to determine rules to use, which requires clients to maintain consistent configuration in order to participate in the network. It seems that mechanics used to choose set of rules to validate blocks really differ depending on a client. Ranging from simple `if`s spread over codebase, towards more structured approach.

An important note is that Ethereum in its Proof-of-Work days was equipped in a mechanism called difficulty bomb to force miners to deploy hard-forks.

Additionally, forks have unique hashes based on genesis, history of previous forks and block activation height to help with quick identification if client is connected to another node of the same network, as specified here: https://eips.ethereum.org/EIPS/eip-2124

Examples of hard-forks deployed to Ethereum:
  - https://eips.ethereum.org/EIPS/eip-606
  - https://eips.ethereum.org/EIPS/eip-1013
  - https://eips.ethereum.org/EIPS/eip-609
  - https://eips.ethereum.org/EIPS/eip-608
  - https://eips.ethereum.org/EIPS/eip-607
  - https://eips.ethereum.org/EIPS/eip-1716
  - https://eips.ethereum.org/EIPS/eip-7568
  - https://eips.ethereum.org/EIPS/eip-7569
  - https://github.com/ethereum/execution-specs/blob/8dbde99b132ff8d8fcc9cfb015a9947ccc8b12d6/network-upgrades/mainnet-upgrades/paris.md
  - https://github.com/ethereum/consensus-specs/blob/f8ae982c2fc7dbb03a3c95a638da4486310e09e9/README.md#stable-specifications

### Solana

In Solana, upgrades are scheduled on a per–feature basis. For a feature a dedicated key is being generated, then dedicated voting tokens are being minted and transferred to validators based on their stake. Finally, if voting result is in favor of a feature - it gets enabled in next epoch.

Sources:
  - https://spl.solana.com/feature-proposal
  - https://docs.rs/solana-program/latest/solana_program/feature/index.html
  - https://docs.rs/solana-sdk/latest/solana_sdk/feature_set/index.html

### Cardano

In Cardano, Shelley upgrade equipped the code and the protocol in capabilities for scheduling upgrades (among a couple of other governance actions).

In its initial form, the protocol is to issue a transaction signed by 5 out of 7 governing keys as defined in genesis, early enough in epoch to be stabilized on total of at least `4k` blocks before next epoch starts. With CIP-1694 the protocol changes to allow other forms of voting and proposing hard-fork activation.

Technically - it as all managed by a type-driven facade called _Hard-fork combinator_, which is ensuring state is properly adjusted to the active rules and that rules are activated properly.

Sources:
  - https://ouroboros-consensus.cardano.intersectmbo.org/docs/for-developers/AddingAnEra
  - https://github.com/IntersectMBO/ouroboros-consensus/blob/8bd8a920607bc256fb001f95621c48469adaf765/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator.hs#L4
  - https://docs.cardano.org/learn/about-hard-forks/

### Substrate/Polkadot

Substrate allows to perform upgrades to be recorded on-chain as a WASM code. This allows for having upgrades of the most functionality without need to update clients — and thus — forking.

Additionally, Substrate offers possibility to define traits implemented with native code, which are versioned, see runtime interface https://docs.rs/sp-runtime-interface/latest/sp_runtime_interface/. This macro builds a WASM-compiled facade to native code. There is also hooks interface, which allows to schedule specific action when runtime version changes. This hooks interface is quite generic, but is allowed to be used together with [Versioned Migration API](https://paritytech.github.io/polkadot-sdk/master/frame_support/migrations/struct.VersionedMigration.html) to ensure what and if it needs to be run based on version change.

Updates to runtime can be done either with sudo module or through governance - what is needed is an origin, which maps to `Root` one: 
  - https://docs.substrate.io/build/origins/
  - https://wiki.polkadot.network/docs/learn-runtime-upgrades
  - https://wiki.polkadot.network/docs/learn-governance#enactment
  - https://docs.substrate.io/maintain/runtime-upgrades/
  - https://paritytech.github.io/polkadot-sdk/master/frame_support/traits/trait.Hooks.html#method.on_runtime_upgrade
  - https://marketplace.substrate.io/pallets/pallet-collective/

## Current state

Many data structures are already versioned with `MAJOR.MINOR` numbers and serialization verifies version compatibility following semantic versioning guidelines.

Also - Node implementation has a well-defined entrypoints for interaction with ledger for transaction validation and execution.

FRAME also requires runtime to be versioned for validation purposes. But it seems that making use of any versioning, require to use runtime upgrades for the changes to take effect with the alternative being replacing code in-place.

Currently - the runtime (consensus + midnight-specific APIs) is already being built with WASM, but ledger is hidden behind the runtime interface API. Whole runtime WASM file at this moment takes around 1MB - 2MB depending on amount of optimizations enabled. 

We know, that ZK operations are taking a lot of time in WASM environment and that it is a largely unknown engineering effort to make ledger code compile with WASM to even benchmark the difference.  

## Proposed Changes

### Option A

This is an option, which assumes no use of runtime upgrades feature. This means, that the versioning framework of Substrate cannot be used and from Substrate's perspective all updates are performed in-place. This implies, that reliance on Substrate's hook APIs is also limited.

#### Protocol

At this moment there is no detailed protocol. Partially - because a big part of protocol definition falls under governance and incentives. 

Nonetheless, there is a set of identified desired properties, which seem to indicate the direction:
- no federation or single party holding governance keys - this removes issues and risks related to selecting the parties, as well as managing very sensitive key material. It also seems to reduce legal risks for potential parties involved 
- protocol updates follow semantic versioning - to clearly indicate compatibility; including support for pre-releases, to allow testing changes e2e _before_ they are released and assigned version number. Following semantic versioning also allows to schedule multiple upgrades in parallel, with clear semantics of compatibility and exact set of rules to obey
- current protocol version is encoded in block and is the same as block version - block is a datatype, which is shared by both consensus and ledger and need to convey data for both, this makes it a perfect target to encode the protocol version
- initial protocol version (the one network starts with) is encoded in the genesis block - so specific-purpose networks can be spun up using desired set of rules
- blocks have encoded latest version supported by its producer to allow at any time verify software upgrades adoption
- initiation of the upgrade is recorded on-chain and need to include 2 pieces of information: policy to be used to determine activation and next version to be activated; the policy may vary - it might follow statistical approach as in Bitcoin, it might be as well a specific transaction, or subject of a voting mechanism; Encoding both data will reduce number of assumptions that need to be made on consensus in order to determine set of rules to apply, as well as should simplify chain selection at the time of a fork
- in order to let clients efficiently choose version of rules to comply, PubSub needs to provide an API to query the current protocol version

##### Compatibility chart

Semantics of compatibility between data and code may be unclear in certain cases, table below may be used as a reference

Legend:
  - ✅ - yes
  - ❌ - no
  - ☑️ - should

| Data (block) version | Protocol (code) version | Can (compatible) data be produced by the code | Can data be consumed by the code |
|----------------------|-------------------------|-----------------------------------------------|----------------------------------|
| `X.Y.Z`              | `X.Y.Z`                 | ✅                                             | ✅                                |
| `(X+n).Y.Z`          | `X.Y.Z`                 | ❌                                             | ❌                                |
| `X.Y.Z`              | `(X+n).Y.Z`             | ❌                                             | ❌                                |
| `X.(Y+n).Z`          | `X.Y.Z`                 | ❌                                             | ☑️(not necessarily fully)        |
| `X.Y.Z`              | `X.(Y+n).Z`             | ✅                                             | ✅                                |
| `X.Y.(Z+n)`          | `X.Y.Z`                 | ✅                                             | ✅                                |
| `X.Y.Z`              | `X.Y.(Z+n)`             | ✅                                             | ✅                                |
| `X.Y.Z-pre.A`        | `X.Y.Z-pre.A`           | ✅                                             | ✅                                |
| `X.Y.Z-pre.A`        | `X.Y.Z-pre.B`           | ❌                                             | ❌                                |
| `X.Y.Z`              | `X.Y.Z-pre.A`           | ☑️                                            | ☑️                               |
| `X.Y.Z-pre.A`        | `X.Y.Z`                 | ☑️                                            | ☑️                               |

In other words:
  - major version change involve complete lack of compatibility and requires a hard-fork to do the update 
  - minor version change maintains backward compatibility, but older code might not be able to fully inspect the data, thus a soft-fork is required to do the update
  - patch version change maintains backward and forward compatibility, so the update can be performed in-place at will
  - pre-releases in principle are treated as major versions, but preferably maintain compatibility with minor version - usually the point of a pre-release is exactly to verify integration and compatibility 

#### Mechanism

A Rust framework following design principles of Cardano's hard-fork combinator for both server- and client-side. In particular, the framework is meant to act as a facade to a ledger functionality in those components, where based on blockchain state it is identified, what set of rules to choose. 

The framework is not a prerequisite, so it can be built organically, but in such case a special care should be put to coupling, to be able to extract the framework from the place it was developed.

The design would follow following mechanic:
  - there exists a (heterogeneous) list of protocol implementations annotated with their versions
  - there exist a set of combinators to offer following capabilities:
    - sort/ensure it is sorted by versions
    - find a version given block/transaction is supposed to follow 
    - find a protocol for a specific version
    - given a version, find set of next supported versions - major, minor, patch and prerelease
    - fold left or right the list
    - find first, last, or all protocols matching a predicate
    - iterate over the list
  - each component can hava facade implemented, which holds the list, and delegate operation using mentioned combinators, specifically
    - ledger:
      - validating a transaction
        - get current protocol version
        - find ledger implementation for that version 
        - delegate validation
      - applying a transaction/block:
        - get current protocol version
        - ensure ledger state is initialized accordingly
        - find ledger implementation for current version
        - delegate application
    - wallet:
      - applying a transaction/update (includes indexing wallet)
        - get current protocol version
        - ensure wallet state is initialized accordingly
        - find implementation for current version
        - delegate application
      - calculating balances
        - get current protocol version
        - find implementation for current version
        - delegate calculation
      - preparing transaction
        - get current protocol version
        - find implementation for current version
        - delegate calculation
    - pubsub indexer:
      - indexing a block/transaction
        - get current protocol version
        - find implementation for current version
        - delegate calculation
      - calculating auxiliary data like zswap chain state:
        - get current protocol version
        - ensure wallet state is initialized accordingly
        - find implementation for current version
        - delegate calculation
  - it is expected, that the facades will need to support sum of all operations from a range of versions, like ledger queries, wallet state queries, etc.; In such cases API should communicate it clearly, that there is a possibility of lack of support for an operation on current version of a component

#### Policy

For initial phases of Midnight, a policy where upgrade is activated automatically whenever there is adoption across majority of block producers, seems to be a good default. 

For emergencies requiring immediate action and preventing use of the previous policy, a dedicated, immediate one might be provided - so that the version upgrade happens immediately at the block it is proposed to. Nodes with incompatible implementation would reject such blocks, but as soon as the majority of block producers/nodes upgrade, whole network would eventually pick up the version with a fix. At the time of network functioning properly - this policy could not be used without a majority of block producers enforcing it.  

Eventually, updates should be managed by a governance mechanism.

#### Pros

1. Independence from Substrate (including testing)
2. Usage of proven, reliable and type-safe pattern
3. No expected performance impact compared with current state
4. Possibility to share the framework with clients of nodes - like wallets and pubsub 
5. Avoidance of storing large amount of code on-chain
6. No need to compile ledger to WASM
7. No code centralization

#### Cons

1. Need to implement version management
2. Ignore Substrate's capabilities
3. Nodes need a restart to update

### Option B

This is a hybrid option, where runtime upgrades are used together with mechanics of Option A. This involves full use of Substrate versioning framework, usage of Substrate hook APIs, but keeping ledger compiled only to native code, with managing ledger and its state updates with the approach similar to hard-fork combinator.

#### Protocol

Protocol is based on runtime upgrades feature of Substrate. That is - upgrades are performed by using dedicated `system.set_code` call from an elevated origin. That means, that changes are registered on-chain quite literally as WASM code. There can, but not have to be, other data present in blocks, to enable other policies - like the one with confirmed code updates.

#### Mechanism

It's two-fold:
  - runtime
  - runtime interface (where ledger is executed)

Runtime is being picked by comparing the version registered on-chain and local, native one. If there is a full match - native code is used. Otherwise, the WASM code registered on-chain is used.

Runtime interface functions are picked depending on what version of runtime is used. So while all functions used by runtimes registered on chain need to be accessible, only subset of them is active depending on runtime version used. So, each ledger version may receive its own well-typed facade, which further is hidden behind the framework mentioned in Option A.

#### Policy

A wide range of policies is available out of the box, as well as implementing new ones should be rather straightforward.
In particular - existing pallets like sudo (which should be avoided), collective or democracy can be used, it would also be possible to implement a policy, which is based on number of nodes that are updated to relevant version.

Because of the separation of ledger from the rest of the runtime, it is even possible to trigger hard forks independently from runtime upgrades, and it is just a matter of policy.

#### Pros

1. Ledger independence from Substrate (including testing)
2. Usage of proven, reliable and type-safe pattern
3. Framework can be used for node clients like pubsub or wallets
4. Leverage relevant Substrate APIs
5. No expected performance impact
6. No ledger code centralization
7. No need to compile ledger to WASM

#### Cons

1. There is WASM code shared on chain, but in fairly limited amounts (1MB—5MB is the expected range)
2. There is a certain code centralization - the runtime, though it involves consensus code
3. Nodes need a restart to update

### Option C

Leverage runtime upgrades fully, including ledger code.

#### Protocol

Similarly to Option B - the protocol is based on `system.set_code` call, WASM code present on-chain, with possible additions if needed for specific policies.

#### Mechanism

With ledger code compiled to WASM as part of the runtime, at the moment runtime is upgraded, ledger is too and Substrate's hooks need to be leveraged fully to e.g. migrate state.

#### Policy

Similarly to Option B - wide range of policies is available out of the box and implementing new ones should be rather straightforward. The major difference is that there is no separation between runtime and ledger from chain perspective.

#### Pros

1. Ledger code still does not depend on substrate
2. Computationally expensive operations and IO can be moved to the edges of ledger code to leverage native runtime interfaces
3. Leverage relevant Substrate APIs

#### Cons

1. Code centralization - the on-chain WASM code is the one, that dictates the rules
2. Substrate-specific tooling needed to test upgrades
3. Node clients like pubsub or wallets still need a solution to react to updates
4. Ledger code needs to be refactored and adjusted to compile with WASM
5. Depending on specific implementation/linking - a performance impact is expected for nodes not running recent versions as well as for validating historical blocks
6. Node updates, and thus - hard forks, are still needed, just maybe a bit less frequently

## Desired Result

As per related PRD, the desired result is as follows:
- Provide a mechanism to execute snark upgrades.
- Provide a framework for managing rules changes both server-side (node, pubsub) as well as client-side (dapps, wallets)
- It is possible to execute protocol backward-incompatible changes, without affecting past block validity.
- Various kinds of forecasted upgrades can be deployed with a confidence and network stability:
  - Transaction format upgrade - Introduce a capability that affects transaction format without affecting previous transactions. Showcase example: adding a signature.
  - Runtime upgrade -upgrade/change the way contracts are executed or validated on-chain(very likely to affect off-chain components as well). Example: providing new on-chain vm operations, introduction of first-class ledger ADTs.
  - Zswap upgrade - upgrade/change coin management and validation in the protocol, which might affect wallet implementation and auxiliary components of the wallet. Example: adding encrypted memos
  - Zswap upgrade- Alter/upgrade  the cryptography that is used for coin management . example: by affecting key derivation, introducing viewing keys or diversified addresses
  - Backward incompatible Changes: Provide a way to validate historical transactions in case of an Upgrade/Change the are backward incompatible.  Example: removing some capability or data - deprecating one way of executing contracts.
  - Ledger emergency Upgrade: Provide a way to persist ledger state in case of a hard fork due to an emergency bugfix affecting ledger execution or state, like usage of persistent storage or serialization/deserialization code.
  - Consensus Upgrade??
- API Updates guidelines - various kinds of upgrades to the ledger code requiring hard-fork are very likely to affect APIs of all Midnight components. It is important to have at least guidelines to evolve the APIs in responses to hard forks

## Open questions/uncertainties

### How should ledger state be initialized on startup?

Blockchain data should allow to determine ledger implementation to be used as a starting one

### How and when perform ledger state upgrade?

It seems excessive and slow to perform state readiness check on each block/transaction application. Though it might be a good starting point for a low cost (overhead of an enum similar to Option for making it explicit whether a state was initialized or not)

Eventually it seems to be a preferred approach to equip the facades with capability of checking whether there might be a fork executed soon, and in such case - perform necessary checks only when expected.

### Is the immediate policy really needed? Can't it be used to take ownership of network at the moment of emergency?

TBD

### The mechanics are very likely to require separate packages for major versions/eras of underlying components

There are ecosystems, where such approach is common, as it allows for gradual upgrades between, otherwise completely incompatible, versions.

### How does SCALE and Borsh handle serialization of data structure extended with an additional field?

TBD

### Why not forkless runtime upgrades Substrate offers? 

They are not completely ruled out. In fact - this mechanic still may be used in the future. 
Substrate offers _Runtime Interface_ feature to link native code to WASM one, so that computationally expensive operations or IO can be performed natively (see https://docs.rs/sp-runtime-interface/latest/sp_runtime_interface/ and https://docs.rs/sp-runtime-interface/latest/sp_runtime_interface/attr.runtime_interface.html).

There are some observations though, which make it hard to select _today_:
- ledger as a whole does not compile to WASM today and size of the effort to compile it to WASM is unknown - this also prevents performing benchmarks and profiling to assess performance impact
- refactoring of ledger code would be needed to be able to factor out operations like IO or ZK; Effort needed for this kind of refactoring would be significant
- certain forms of upgrades still need a form of hard-fork, because of the need to adjust runtime interfaces
- without defined governance the `sudo` pallet would be needed, which in turn would require master keys to the network
