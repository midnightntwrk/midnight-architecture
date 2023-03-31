$version: "2"

namespace io.iohk.midnight.pubsub_indexer.data_types

@pattern("^[a-f0-9]{64}$")
string MerkleTreeHash

@input
@pattern("^[a-f0-9]{64}$")
string BlockHash

@input
@range(min: 0)
bigInteger BlockHeight

@input
@pattern("^[a-f0-9]{64}$")
string TransactionHash

@pattern("^[a-f0-9]{64}$")
string ContractAddress

@output
structure Block {
    @required
    hash: BlockHash

    parentHash: BlockHash

    @required
    height: BlockHeight

    @required
    timestamp: timestamp

    @required
    transactions: TransactionList
}

list TransactionList {
    member: Transaction
}

@output
structure Transaction {
    @required
    hash: TransactionHash

    @required
    nullifiers: Nullifiers

    @required
    commitments: Commitments
}

union BlockchainOffset {
    blockHash: BlockHash
    blockHeight: BlockHeight
}

structure ContractCalled {
    address: ContractAddress
    transaction: Transaction
    newState: ContractState
}

structure NewNullifiers {
    transaction: TransactionHash
    nullifiers: Nullifiers
}

structure NewCommitments {
    transaction: TransactionHash
    commitments: Commitments
    rootHash: MerkleTreeHash
}

list Nullifiers {
    member: Nullifier
}

list Commitments {
    member: Commitment
}
