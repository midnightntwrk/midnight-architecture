# PubSub-Indexer APIs

## Blockchain queries

This is a set of stateless request-response APIs that can be exposed on top of HTTP.
It is implicitly meant to be used by a public blockchain explorer.

```graphql
type Query {
    block(offset: BlockOffset!): Block
    transaction(hash: TransactionHash!): Transaction
    contractState(address: ContractAddress!, offset: BlockOffset): ContractState
}
```

## Contract state subscriber

This is a subscription API, where the client sends a request first, and from that moment the server 
starts pushing an indefinite number of responses back to the client.

The most prominent use case for this API are dApps, which need to be constantly updated whenever 
there is an event that affects the contract state.

```graphql
type Subscription {
    contractState(address: ContractAddress!, offset: BlockOffset!): ContractCalled
}
```

## Viewing key subscriber

Also a subscription API, it provides clients with all the events (i.e. transactions) 
related to a particular viewing key if one is passed, all transactions are streamed if no viewing
key is given.

The clients must first connect to get a session identifier and then use the identifier to subscribe 
and start receiving all the relevant transactions.

This API design is meant for wallets. Only wallets should have access to user's keys and with the 
inputs and outputs information can build a view of the available coins.

```graphql
type Query {
    connect(key: ViewingKey): SessionId
}
type Subscription {
    transactions(id: SessionId!, offset: BlockOffset!): Transaction
}
```

## Data types

These are the data types used in the previous interfaces. The ones defined as just `scalar` are yet 
to be defined in more detail.

```graphql

# It's not possible to use a union as input type, so using 2 optional fields
input BlockOffset {
    hash: BlockHash
    height: BlockHeight
}

type Block {
    hash: BlockHash!
    parentHash: BlockHash!
    height: BlockHeight!
    timestamp: DateTime!
    transactions: [Transaction!]!
}

type Transaction {
    hash: TransactionHash!
    blockHash: BlockHash!
    inputs: [TransactionInput!]!
    outputs: [TransactionOutput!]!
}

type TransactionInput {
    nullifier: Nullifier!
    valueCommitment: ValueCommitment!
    merkleTreeRoot: MerkleTreeHash!
}

type TransactionOutput {
    coinCommitment: CoinCommitment!
    valueCommitment: ValueCommitment!
}

type ContractCalled {
    address: ContractAddress!
    transaction: Transaction!
    newState: ContractState!
}

scalar BlockHash

scalar BlockHeight

scalar TransactionHash

scalar Nullifier

scalar CoinCommitment

scalar ValueCommitment

scalar ContractAddress

scalar ContractState

scalar ViewingKey

scalar SessionId

scalar DateTime
```
