$version: "2"
namespace io.iohk.midnight.pubsub_indexer.blockchain_querier

service BlockchainQuerier {
    operations: [
        GetBlockByHash,
        GetBlockByHeight,
        GetTransactionByHash
    ]
}

@readonly
operation GetBlockByHash {
    input: BlockHash
    output: Block
    errors: [BlockHashNotFound]
}

@readonly
operation GetBlockByHeight {
    input: BlockHeight
    output: Block
    errors: [BlockHeightNotFound]
}

@readonly
operation GetTransactionByHash {
    input: TransactionHash
    output: Transaction
    errors: [TransactionHashNotFound]
}
