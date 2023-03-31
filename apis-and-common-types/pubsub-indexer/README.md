# PubSub-Indexer APIs

Interfaces are written in Typescript for brevity first and a draft in Smithy is provided in 
[src/smithy](src/smithy) directory.

## Blockchain queries

This is a set of stateless request-response APIs that can be exposed on top of HTTP, possibly in a 
REST or Json-RPC style.

It is implicitly meant to be used by a public blockchain explorer.

```typescript
interface BlockchainQuerier {
  
  getBlockByHash(hash: BlockHash): Option<Block>;
  
  getBlockByHeight(height: BlockHeight): Option<Block>;
  
  getTransactionByHash(hash: TransactionHash): Option<Transaction>;

}
```

## Contract state subscriber

This is a subscription API, where the client sends a request first, a subscription state is 
saved on the server, and from that moment the server starts pushing an indefinite number of 
responses back to the client.
The `Observable` type is used on purpose to resemble `rxjs` semantics in Javascript.

The most prominent use case for this API are dApps, which need to be constantly updated whenever 
there is an event that affects the contract state.

```typescript
interface ContractStateSubscriber {
  
  subscribeToContractState(
      contractAddress: ContractAddress,
      offset: BlockHash | BlockHeight,
  ): Observable<ContractCalled>;

}
```

## Viewing key subscriber

Also a subscription API, it provides clients with all the events (i.e. nullifiers or commitments) 
related to a particular viewing key.

This API design is meant for wallets. Only wallets should have access to user's keys and with the 
nullifiers and commitments information can build a view of the current balance and available coins.

```typescript
interface ViewingKeySubscriber {
  
  subscribeToViewingKey(
      viewingKey: ViewingKey,
      offset: BlockHash | BlockHeight,
  ): Observable<NewNullifiers | NewCommitments>;
  
}
```

## Data types

These are the data types used in the previous interfaces. The ones defined as `unknown` are yet to 
be defined.

```typescript
type MerkleTreeHash = string;

type BlockHash = string;

type BlockHeight = bigint;

type TransactionHash = string;

type Nullifier = unknown;

type Commitment = unknown;

type Block = {
  hash: BlockHash;
  parentHash: BlockHash;
  height: BlockHeight;
  timestamp: Date;
  transactions: Transaction[];
};

type Transaction = {
  hash: TransactionHash;
  blockHash: BlockHash;
  nullifiers: Nullifier[];
  commitments: Commitment[];
};

type ContractAddress = string;

type ContractState = unknown;

type ContractCalled = {
  address: ContractAddress;
  transaction: Transaction;
  newState: ContractState;
};

type NewNullifiers = {
  transaction: TransactionHash;
  nullifiers: Nullifier[];
};

type NewCommitments = {
  transaction: TransactionHash;
  commitments: Commitment[];
  rootHash: MerkleTreeHash;
};
```
