# Component Name

[Wallet Core](https://github.com/input-output-hk/midnight-wallet)
[Wallet Browser Extension UI](https://github.com/input-output-hk/midnight-wallet-extension)

Wallet is a component run by the end user. Its core purpose is to:
  - protect the private key(s)
  - allow making transactions authenticated using the key

Everything else is more of a convenience functionality to bring solid user experience than something wallet has to do. Most notably, very common functionalities, that is hard to imagine a modern wallet without, are:
  - an API allowing websites to initiate a transaction and query for some data
  - track tokens owned by user: native and defined through smart contracts
  - keep track of additional data allowing to generate witnesses necessary to construct a correct transaction (like Merkle trees, ZK-proofs, temporary keys)

There are also important non-functional considerations:
  - intuitiveness
  - ease of use
  - performance
  - need for the interface to guide the user and prevent from performing actions that may end up in an irrecoverable state
Which, together, may be put under umbrella of User/Developer Experience. They apply equally to all different flavors of wallets, only way of interaction changes (RPC, CLI, TUI, GUI). 

Unless stated differently, this document focuses on a flavor of Midnight Wallet that:
  - runs as a browser extension
  - does not require user to run its Midnight Node instance

## Special Needs

Because of how web extensions work - dApp connector API needs to be carefully designed wrt privacy and security. The 
biggest risks seem to arise from 2 directions: 
  - possibility of eavesdropping communication between dApp and the Wallet by a malicious extension
  - possibility of eavesdropping communication between dApp and the Wallet by a malicious code being part of dApp 
    code (e.g. due to a supply-chain attack)

## Neighbors & API Dependencies

Wallet has 2 neighbors: [Wallet Backend](../WalletBackend) and dApp(Client SDK effectively)

### Service - dApp connector _(just a WIP name)_

This is an API that allows a dApp ([see Glossary](../../product/Glossary.md)) to initiate a transaction and query 
wallet data.

### Client - Wallet Backend sync API

It allows the Wallet to learn about blocks that are relevant to it. And thus, with additional processing - exact 
transactions, their confirmations, finality and metadata for constructing future transactions 
([see Wallet Backend](../WalletBackend))

### Client - transaction submission API

It allows Wallet to submit transactions, so eventually they can be included in blockchain. The neighbor component 
implementing this API is [Wallet Backend](../WalletBackend), though a similar (if not identical) one is needed 
between Wallet Backend and Node.

### Client/service - Lace (the Light Wallet project) integration APIs

They allow to embed Wallet within the Lace product, that is:
  - show Midnight-unique UI
  - integrate with other projects within Lace like core wallet functionality (that owns the keys) or, for example, 
    address book
  - deploy Midnight Wallet's dApp connector implementation

### Client - proving system

It allows Wallet to generate ZK proofs necessary to construct transactions

## Operating Environment

Wallet is run in a desktop browser, potentially any that support WebExtensions API. Specifically, the ones that are 
most 
likely to be used are:
  - Google Chrome
  - Mozilla Firefox
  - Apple Safari
  - other Chromium-based browsers like Microsoft Edge, Brave, Opera, Vivaldi, etc.

Possibly any desktop operating system that allows running some browser listed above may be used, the most popular 
ones are:
  - Microsoft Windows
  - Linux distributions
  - macOS
  - BSD flavors

## Key Library Dependencies

React.js - for rendering UI
Kernel (internal) - for processing&creating transactions

## Logical Data Model

Include an [ER diagram](https://plantuml.com/ie-diagram).

### Entities

Document the entities.

#### Entity 1

#### Entity 2

### Invariants

This MUST include state invariants expressed in terms of the ER model that describe the valid states of the system.

## Responsibilities

### Interface Data Types

What kinds of data are used in the API's, either as inputs or outputs?  Are they versioned?  Does the component have to support multiple versions at once?

### API's
What API's does the component support?  It's not necessary to include the actual code.  Rather, document the nature of the responsibility and any special constraints.

#### API 1

##### Event 1

- Name, input args, return type, kinds of failures
- Computational complexity
- Net effect on memory size or disk usage
- What ER-model structures are used to handle the event?

##### Event 2



## Non-Functional Requirements

### Scalability

- What is the expected complexity bound of each API function?
- For each API function, what is its net effect on memory growth and what mechanisms are included to prevent memory leaks?

### Availability

Is it ok for the component to "just let it fail" when things go wrong, or must this component fight to survive all errors?

### Security

How are the API's protected against unauthorized use?  What is the DDoS defense, for example?  Are there operations that require specific authorization using signatures or authenticated identities?

### Debugability, Serviceability

- What logging levels are supported and can they be dynamically configured?
- How does the component provide debug context on a crash?


## Life Cycle (State Machine)

The component MUST declare whether it has a lifecycle that can be described as a state machine.  This should include any state changes that affect things like the availability of the component or its resources.  A component that performs periodic expensive memory-refactoring, for example, should document this period of unavailability and high resource usage as a distinct state. 

How will the component handle unavailability of required services, both at launch and in steady state?
