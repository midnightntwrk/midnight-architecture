$version: "2"

namespace io.iohk.midnight.pubsub_indexer.contract_state_subscriber

use io.iohk.midnight.pubsub_indexer.data_types#ContractAddress

service ContractStateSubscriber {
    operations: [SubscribeToContractState]
}

@readonly
operation SubscribeToContractState {
    input: SubscribeToContractStateInput
    output: SubscribeToContractStateOutput
}

@input
structure SubscribeToContractStateInput {
    @required
    contractAddress: ContractAddress
    @required
    offset: BlockchainOffset
}

@output
@streaming
union SubscribeToContractStateOutput {
    contractCalled: ContractCalled
}
