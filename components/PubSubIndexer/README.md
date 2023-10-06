# PubSub-Indexer

https://github.com/input-output-hk/midnight-pubsub-indexer

The PubSub-Indexer is a component meant to optimize the flow of data from the node to the end users'
applications. Because nodes aren't designed to support such clients, they only store the raw blocks
of transactions and the most updated ledger state, so user applications would have to retrieve the
whole history of blocks just to find the ones that are of interest.
To solve this mismatch, PubSub-Indexer retrieves the history of blocks, processes them, and stores
data with a structure that is optimized (i.e. _indexed_) for the end users' applications. It also
offers a mechanism so that applications can subscribe to be notified whenever some data of their
interest changes, avoiding the necessity to constantly poll to see if there is something new that
they should be aware of.

## Special Needs

## Neighbors & API Dependencies

There are at least, but not limited to, 3 types of clients of the PubSub-Indexer:

1. Wallets
2. dApps
3. Block explorers

And there is one source from where the PubSub-Indexer pulls the blocks, which is at least
one [node](missing_documentation).

![](./components.svg)

**Events Source:** This component is responsible for subscribing to and requesting data from a node.

**Indexer:** The indexer receives events from the events source, processes them, and stores them in the index. It also takes care of notifying the pubsub mechanism about these events.

**Pubsub Mechanism:** This component allows various parts of the system to publish and subscribe to specific topics, facilitating real-time data updates.

**Subscription API:** The subscription API provides WebSocket-based subscriptions. Clients can use it to receive real-time updates and notifications about events and data changes.

**Query API:** This component offers an HTTP API that allows clients to query and retrieve data from the index, providing a more structured and user-friendly way to access information through a GraphQL interface.

### Wallets

Wallets allow users to build transactions that transfer tokens and/or call or deploy contracts. All transactions will spend some of the user's coins, so wallets need to know the transactions that send coins to the user's addresses, and they also need to know when a transaction they submitted was confirmed, in order to mark the input coins as spent and remove them from their available coins.

### dApps

dApps are all about contracts, and so they need to know when a contract's state was updated. This means knowing when and how a contract was called, in order to update the state.

### Block explorers

A block explorer will typically allow users to find blocks by their hash or height, find transactions by hash, or get a contract state by address. PubSub-Indexer allows for simply doing these kind of queries and getting an immediate response.

## Operating Environment

Possibly any _desktop_ operating system may be used, the most popular ones are:
- Microsoft Windows
- Linux distributions
- macOS
- BSD flavors

## Key Library Dependencies

- Scala standard library
- Typelevel stack
  - cats-core
  - cats-effect
  - doobie
  - fs2
- Caliban
- Sttp
- Circe

## Logical Data Model

![](./datamodel.svg)

### Entities

#### Block

#### Transaction

#### Contract Call

#### Contract Deploy

#### WalletAppliedTransaction

### Invariants

1. Once data is persisted, it should remain available and consistent over time. 
2. Any data retrieval or query operation for information from the genesis block or any subsequent block should consistently return the same results as initially.
3. For each block, every transaction associated must be indexed.
4. For each indexed transaction, its associated block must include it in its list of transactions.
5. For each block, its parent field should refer to a valid parent block.
6. A parent block should have a height that is one less than the height of the following block.
7. The hash of the parent block should match the parent field in the following block.
8. If a transaction is listed in the transactions of a block, then the block field of said transaction should refer to that block.
9. For each contract call or deploy listed in a transaction's contractCalls, the transaction field of the contract call or deploy should refer to the same transaction that contains it in its contractCalls list.
10. For each contract call there must be a single corresponding contract deploy with the same address.
11. Each wallet session is uniquely identified by a session ID, which is randomly generated and associated to a viewing key.
12. If a session ID is removed, a new session ID will be generated for the same viewing key when requested.
13. Each transaction has an associated wallet local state that can be generated if there is a session with the viewing key that owns the transaction.
14. The wallet local state associated with a particular transaction remains consistent for every wallet session.


## Responsibilities

### Interface Data Types

These are the data types used in the previous interfaces. The ones defined as just `scalar` are yet
to be defined in more detail.

```graphql

union WalletSyncEvent = ProgressUpdate | TransactionAdded

input BlockOffsetInput {
  hash: BlockHash
  height: BlockHeight
}

input TransactionOffsetInput {
  hash: String
  identifier: String
}

type Block {
  parent: Block!
  hash: BlockHash!
  height: BlockHeight!
  timestamp: DateTime!
  transactions: [Transaction!]!
}

type Transaction {
  block: Block!
  hash: TransactionHash!
  identifiers: [TransactionIdentifier!]!
  contractCalls: [ContractCallOrDeploy!]!
  raw: RawTransaction!
  fallible: Boolean!
}

type TransactionAdded {
  transaction: Transaction!
  state: WalletLocalState
}

type ProgressUpdate {
  synced: BlockHeight
  total: BlockHeight
}

interface ContractCallOrDeploy {
  state: ContractState!
  transaction: Transaction!
  address: ContractAddress!
  zswapChainState: ZswapChainState!
}

type ContractCall implements ContractCallOrDeploy {
  transaction: Transaction!
  deploy: ContractDeploy!
  address: ContractAddress!
  state: ContractState! # New state after this contract call
  zswapChainState: ZswapChainState!
  operation: ContractOperation!
}

type ContractDeploy implements ContractCallOrDeploy {
  transaction: Transaction!
  address: ContractAddress!
  state: ContractState! # Initial contract state
  definition: ContractDefinition!
  zswapChainState: ZswapChainState!
}

scalar BlockHash

scalar BlockHeight

scalar TransactionHash

scalar TransactionIdentifier

scalar ContractAddress

scalar ContractState

scalar ContractDefinition

scalar ContractOperation

scalar ViewingKey

scalar SessionId

scalar DateTime

scalar Void

scalar RawTransaction

scalar ZswapChainState

scalar WalletLocalState
```

### API's

#### Blockchain queries

This is a set of stateless request-response APIs that can be exposed on top of HTTP.
It is implicitly meant to be used by a public blockchain explorer.

```graphql
# No block offset argument means that client wants to get the latest
type Query {
    block(offset: BlockOffsetInput): Block
    transaction(offset: TransactionOffsetInput): Transaction
    contract(address: String!, offset: BlockOffsetInput): ContractCallOrDeploy
}
```

#### Contract state subscriber

This is a subscription API, where the client sends a request first, and from that moment the server
starts pushing an indefinite number of responses back to the client.

The most prominent use case for this API are dApps, which need to be constantly updated whenever
there is an event that affects the contract state.

```graphql
type Subscription {
    contract(address: ContractAddress!, offset: BlockOffset): ContractCallOrDeploy
}
```

#### Blocks Subscriber 

This subscription API provides clients with all the blocks

```graphql
type Subscription {
    blocks(offset: BlockOffsetInput): Block
}
```

#### Transactions subscriber

This subscription API provides clients with all the transactions. If `sessionId` is provided either by argument or in the header of the request, only transaction associated to that ID will be returned with associated `WalletLocalState`.

```graphql
type Subscription {
    transactions(offset: TransactionOffsetInput, sessionId: SessionId): WalletSyncEvent
}
```

To obtain the ID, the clients must first connect with a viewing key to get the session identifier and then use the identifier to subscribe
and start receiving all the relevant transactions.

This API design is meant for wallets. Only wallets should have access to user's keys and with the inputs and outputs information can build a view of the available coins.

```graphql
type Mutation {
    connect(key: ViewingKey): SessionId!
    disconnect(sessionId: SessionId!): Void!
}
```
Disconnect mutation will permanently remove the session associated to the viewing key. To subscribe again to a wallet's transactions, a new session must be created.


## Architecture Characteristics

_NOTE:  There is also a
quick [reference list of architecture characteristics](../definitions.md#architecture-characteristics)
available._

_NOTE:  Choose wisely, the more architecture characteristics are identified for a component, the more
complicated it will be. Also, bear in mind that some architecture characteristics can be delegated
to software design or UX._

_Here is a list of sample architecture characteristics, please remember to update them to match the
needs of the particular component._

### Configurability

The component accepts the following configurations
- Storage:
  - `driver-name`
  - `jdbc-url`
  - `user`
  - `pass`
  - `thread-pool-size`
- Transaction Steam
  - `progress-update-delay`
- Server
  - `host`
  - `port`
- Events-source
  - `node-host`
- API
  - `max-cost`
  - `max-depth`
  - `max-fields`
  - `timeout`

### Performance

- _What is the expected complexity bound of each API function?_
- _For each API function, what is its net effect on memory growth and what mechanisms are included to
  prevent memory leaks?_

### Availability

_Is it ok for the component to "just let it fail" when things go wrong, or must this component fight
to survive all errors?_

### Security, Authentication, Authorization

_How are the API's protected against unauthorized use? What is the DDoS defense, for example? Are
there operations that require specific authorization using signatures or authenticated identities?_

### Debugability, Serviceability

- _What logging levels are supported and can they be dynamically configured?_
- _How does the component provide debug context on a crash?_

## Life Cycle (State Machine)

_The component MUST declare whether it has a lifecycle that can be described as a state machine. This
should include any state changes that affect things like the availability of the component or its
resources. A component that performs periodic expensive memory-refactoring, for example, should
document this period of unavailability and high resource usage as a distinct state._

_How will the component handle unavailability of required services, both at launch and in steady
state?_
