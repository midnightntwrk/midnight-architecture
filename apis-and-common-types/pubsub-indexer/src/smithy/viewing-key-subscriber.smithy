$version: "2"

namespace io.iohk.midnight.pubsub_indexer.viewing_key_subscriber

use io.iohk.midnight.pubsub_indexer.data_types#BlockchainOffset

service ViewingKeySubscriber {
    operations: [SubscribeToViewingKey]
}

operation SubscribeToViewingKey {
    input: SubscribeToViewingKeyInput
    output: SubscribeToViewingKeyOutput
}

@input
structure SubscribeToViewingKeyInput {
    viewingKey: ViewingKey
    offset: BlockchainOffset
}

@output
structure SubscribeToViewingKeyOutput {
    viewingKeyEvent: ViewingKeyEvent
}

@streaming
union ViewingKeyEvent {
    newNullifiers: NewNullifiers
    newCommitments: NewCommitments
}
