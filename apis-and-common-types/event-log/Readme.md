# Event log

An API, which is exposed by a node, to allow processing chain and transaction-related 
data.

__Status__: Draft

## Use cases

Major use-cases this API has to enable are:
  - Implementing a PubSub Indexer
  - Implementing a block explorer
  - Implementing a (light)wallet backend
  - Implementing DApp ledger state sync
  - Debugging transaction failures, especially ones preventing tx from being added to 
    a block
  - Calculating statistical data of transactions and blocks 

## Events

Tentative specification of events to be published is as below (TS syntax). Datatypes like 
`Block`, `Transaction`, etc. are left undefined here on purpose because of many 
changes expected to be made soon. As of time of writing, the most recent definitions 
of shape of those can be found at [Ledger Repository](https://github.com/input-output-hk/midnight-ledger-prototype)

Most of these events are sourced from ledger and mempool/consensus, rising a requirement
for the component APIs to report these. It is not required from node code to know exact 
contents of the events or how to parse them as long as a canonical serialization is defined for ledger-owned datatypes

```TS
// New block added to chain
interface NewBlock {
  block: Block
}

// New transaction received to mempool
interface NewPendingTx {
  tx: Transaction
}

// Transaction got included in block
interface TxIncluded {
  tx: Transaction
  block: Block
}

// Nullifier set was updated
interface NewNullifiers {
  tx: Transaction
  nullifiers: Nullifier[]
}

// Commitment Tree was updated
interface NewCommitments {
  tx: Transaction
  commitments: Commitment[]
  rootHash: Hash
}

// Attempt to prepare a block with given transaction failed
interface TxInclusionFailed {
  tx: Transaction
  reason: string //TODO: a more detailed error type is a better option here
}

// Transaction removed from mempool due to an error condition (e.g. TTL expired)
interface PendingTxDropped {
  tx: Transaction
  reason: string //TODO: a more detailed error type is a better option here
}

// New contract got deployed
interface NewContract {
  tx: Transaction
  address: ContractAddress
  state: ContractState
}

// Contract was called
interface ContractCalled {
  tx: Transaction
  address: ContractAddress
  newState: ContractState
}

// State changed
interface LedgerStateChanged {
  address: ContractAddress
  newState: ADT
}
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

## Use-cases implementation

### Block explorer

Just listening to `NewBlock` events should be enough to implement a simple block 
explorer. Other events allow to expand on functionality (looking at contract states, 
seeing pending transactions, etc.)

### (Light)wallet backend

Wallet requires 3 pieces of chain data to be able to create a valid transfer transaction:
  - subset of nullifier set - to prevent double spends
  - commitment tree - to be able to commit coins spending
  - own coins - to know balance and be able to spend them

Stream of `TxIncluded`, `NewNullifiers` (optional) and `NewCommitments` events covers 
these. It is easy to imagine a more fine-grained events, where transaction inputs 
and outputs are accessible by separate events, and thus - reducing amount of data 
transmitted and processed by wallet

### Implementing DApp ledger state sync

Events `NewContract`, `ContractCalled` and `LedgerStateChanged` cover this.

### Debugging transaction failures

Listening to events `TxInclusionFailed` and `PendingTxDropped` should provide enough 
information to know why transaction was not added to a block. This mechanism is 
supplementary to error reporting in [Transaction Submission API](../transaction-submission)

### Calculating statistical data of transactions and blocks

It depends heavily on metrics to implement. 
Events `NewBlock`, `NewNullifiers`, `NewCommitments`, `ContractCalled` and 
`NewContract` seem to cover many cases related to blockchain data itself.
If events `NewBlock` and `NewPendingTx` have timestamps, it becomes feasible to 
calculate time-bound metrics related to e.g. network congestion

## Current state

Node uses substrate integration points to expose necessary APIs as a mix of RPC 
methods and Substrate events in the Midnight pallet definition: https://github.com/input-output-hk/midnight-substrate-prototype/blob/main/pallets/midnight
