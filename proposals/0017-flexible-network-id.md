# Proposal 0017: Flexible network identifier

## Problem Statement

Network identifier, as defined at the moment of writing is just a Rust enum defined in ledger:
```rust
pub enum NetworkId {
    Undeployed = 0,
    DevNet = 1,
    TestNet = 2,
    MainNet = 3,
}
```

While it is simple approach, with easy to predict values and serialization, it lacks certain flexibility and precision when setting up multiple networks:
- it is not obvious, how to apply different variants of `NetworkId` to different networks
- multiple testing networks receive the same network id
- expected multiple testnets would end up using the same network id
- expected multiple mainnets would end up using the same network id
- due to above - there is no way to visually discriminate addresses, if they belong to one network or another
- due to above - a transaction built against one testnet would be accepted for submission in another testnet and likely fail for random and unknown reason  

## Proposed Changes

The proposal is to:
- change network id to be an arbitrary string of alphanumeric characters: small and big letters, numbers, and a hyphen 
- remove network id from ledger serialization format entirely (alternatively keep it optional to use only with specific datatypes, like contract state serialization)
- make network id part of ledger state and genesis block data
- make network id part of transactions or intents, so that they need to match ledger's one as well as each other upon merging
- extend APIs of node, indexer and wallet, so that they advertise network id they are configured with, and can learn it, and validate data received against provided network id

Since there are existing networks, which are expected to be long-running, maintaining compatibility is a concern here. There are two possible approaches to introduce these changes. Both cases assume introducing them in hard-forks. In such a hard-fork ledger would need to have its state converted, to introduce new data (network id). Network id is already part of node storage, so performing a ledger state migration is entirely possible, with a mapping of NetworkId enum into a string.

One approach to introduce those changes would be to perform a hard-fork, requiring new rules to be obeyed, at a cost of all clients needing to upgrade too. In such case it would be good to bundle it with different, more important changes to transaction format.

The other approach would make it possible to gradually introduce changes - first introduce network id as an optional data in a transaction. At this stage transaction processing code (both in ledger and outside it) would need to accept existing transactions as well as ones with network id present. In the latter case - presence of network id enables its validation. At a next (optional) stage, transactions without network id present would be rejected. This approach has the advantage of providing client applications a window, where they can update their code in place.

## Desired Result

- addresses can clearly indicate what specific network they are created for
- mixing data from different networks is prevented
- less configuration needed - indexer can learn network id from node, proof server does not need the configuration setting at all
