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
- make network id part of transactions or intents, so that they need to match ledger's one as well as each other upon merging
- extend APIs of node, indexer and wallet, so that they advertise network id they are configured with, and can learn it, and validate data received against provided network id

## Desired Result

- addresses can clearly indicate what specific network they are created for
- mixing data from different networks is prevented
- less configuration needed - indexer can learn network id from node, proof server does not need the configuration setting at all
