# Event log

An API, which is exposed by a node, to allow processing chain and transaction-related 
data.

__Status__: Draft

## Use cases and data needs

Major use-cases this API has to enable are:
  - Implementing a block explorer
  - Implementing a (light)wallet backend
  - Implementing DApp ledger state sync
  - Debugging transaction failures, especially ones preventing tx from being added to 
    a block
  - Calculating statistical data of transactions and blocks 

These are the major pieces of data, that PubSub Indexer needs to obtain (either receive directly or receive metadata allowing to calculate these) from connected node(s), in order to fulfill use-cases above:
  - raw blocks and transactions, mostly for block explorer, but also, as a useful data for post-processing or to anchor integrity checks into
  - contract state updates on a per-transaction basis - for allowing quick sync of contracts public state
  - contract events on a per-transaction basis - for a clear source of data for evolving contracts private state (to be discussed as of now, there's no concept of contract events to get this and DApps are better relying on watching how state changes)
  - coin commitment merkle tree - for wallets, and as one of ways of checking data integrity if part of block header, probably important for dapps too (handling coins)
  - nullifier set - for wallets and dapps, to help maintain consistent view on spent coins
  - ephemeral events related to mempool (tx added to mempool, tx removed because of TTL and block inclusion errors, etc., tx removed because of being successfuly added to a block) - debugging, block explorer, calculating statistics



## Interface

Tentative specification of interface (TS syntax). Datatypes like 
`Block`, `Transaction`, etc. are left undefined here on purpose because of many 
changes expected to be made soon. As of time of writing, the most recent definitions 
of shape of those can be found at [Ledger Repository](https://github.com/input-output-hk/midnight-ledger-prototype)

Most of these events are sourced from ledger and mempool/consensus, rising a requirement
for the component APIs to report these. It is not required from node code to know exact 
contents of the events or how to parse them.

```TS
interface EventsSync {
  startSync(knownPoints: Array[BlockchainPoint]): Observable<BlockAdded|NewPendingTx|PendingTxDropped>
}

interface BlokchainPoint {
  hash: BlockHash
  height: BlockHeight
}

// New transaction received to mempool
interface NewPendingTx {
  tx: Transaction
  timestamp: DateTime
}

// Transaction removed from mempool due to an error condition (e.g. TTL expired)
interface PendingTxDropped {
  tx: Transaction
  timestamp: DateTime
  reason: string //TODO: a more detailed error type is a better option here
}

// New block added to chain
interface BlockAdded {
  hash: BlockHash
  height: BlockHeight
  timestamp: DateTime //feasible/reasonable/required?
  header: BlockHeader //expecting to contain integrity check data for nullifier set and commitment tree
  transactions: Array<TransactionAdded>
  raw: bytes 
}

interface TransactionAdded {
  hash: TransactionHash //is this a reasonable to expect?
  identifiers: Array[TransactionIdentifier]
  parts: Array[TransactionPart]
  raw: bytes
}

type TransactionPart = 
  | {type: "input", nullifier: Nullifier}
  | {type: "output", commitment: Commitment, raw: bytes}
  | {type: "call", address: ContractAddress, operation: Operation, newState: ADT}
  | {type: "deploy", address: ContractAddress, definition: ContractDefinition, state: ADT}
```

## Transport API

Undefined. Most probably a streaming-oriented, widely implemented protocol like 
Web-Sockets.

## Replaying events from node

Most of these events can be recreated by applying blocks in ledger. It requires ledger 
to be able to rewind to arbitrary state or to quickly replay arbitrary chain of blocks 
from scratch.

This observation leads to 3 connected decisions that will need to be made:
  - do mempool/consensus-related events need persistence?
  - does ledger allow to replay blockchain-related events?
  - is dedicated _event store_ needed?

## Replaying events from indexer 

It is expected from indexer to be always able to replay these events so that various 
clients can lose their local data and still get to the same view.  