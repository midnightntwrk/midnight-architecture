# 15. Off-chain (token) metadata

## Status

Proposed

Supersedes [12. Manual token names](./0012-manual-token-names.md)

---
| -               | -                                                                               |
|-----------------|---------------------------------------------------------------------------------|
| date            | March 2024                                                                      |
| deciders        | Andrzej Kopeć, Thomas Kerber                                                    |
| consulted       | Jonathan Sobel, Jon Rossie                                                      |
| informed        | Mike Lin                                                                        |
| PRD             | https://docs.google.com/document/d/1uhVGU7iV9OHMdo_HrMYVFAO-gvlnHkdHrkUvm0-hP3c |
| Jira initiative | [PM-8517](https://input-output.atlassian.net/browse/PM-8517)                    |
---

## Context and Problem Statement

Midnight needs a dedicated space to attach token metadata to. As the name says - they are metadata - that is ledger code does not make any use of this information to validate transactions. But ledger operates in a big part on opaque hashes of values, which are very difficult to work with for humans. 

Another issue with metadata is that it is particularly difficult to prove correctness of it. For example - USDC is a widely present stablecoin, which can be brought to chains using different mechanisms - e.g. natively, or through various bridges. How to encode that only token of type "abc" is USDC, while "def" is a completely unrelated token, which just chose USDC name (unaware of name clash or with malicious intents)?

Across the industry, there are multiple approaches to this problem. Ranging from storing the metadata on-chain, as part of the originating contract, to independent off-chain services. Importantly, while the context is token metadata, this ADR makes a decision over direction for all kinds of metadata in Midnight, which forces to think on how to make token metadata datatypes and ways of work flexible enough to accommodate for e.g. DApps or stake pools.

## Decision Drivers

* Fit into existing architecture
* Security/trust assumptions always needed
* Security/trust assumptions flexibility

## Considered Options

* Store metadata on-chain, defined by contracts or through dedicated transaction extension
* Store metadata off-chain, similarly to [CIP-26](https://cips.cardano.org/cip/CIP-0026) design

## Decision Outcome

Chosen option: "Store metadata off-chain, similarly to CIP-26", because
it allows to implement many different security models and start small with the implementation - a simple HTTP server serving data from a predefined, community-maintained repository. Serving token metadata is a good case for PubSub Indexer within existing architecture.

## Validation

Review shows that initial implementation of the initiative does not store token metadata on chain and is served from PubSub Indexer.

## Pros and Cons of the Options

### On-chain metadata

* Good, because all data are on-chain and can be easily indexed and served to users
* Good, because of convenience of defining new tokens
* Bad, because security/trust model becomes very rigid and inherently tied to contract authorship
* Bad, because storing data on-chain is expensive
* Bad, because metadata could not be verified by ledger in any meaningful way and yet are stored with other data ledger cares about

### Off-chain metadata

* Good, because storage independent of chain is relatively cheap, and still, if someone wants to build a metadata server on top of a contract - it remains an option
* Good, because provides flexibility regarding trust and security model
* Good, because first iteration can be implemented relatively quickly
* Neutral, because  PubSub Indexer is a natural hosting service for the metadata
* Bad, because metadata is stored independently of the data it describes, which adds additional source of data to manage


## More Information

It is a clear trend in Cardano ecosystem to move towards off-chain metadata. The initial transaction metadata, which is defined to describe tokens too, is stored on-chain, but then, there is a series of CIPs and metadata designs, which move the metadata off-chain: 
  - [SMASH](https://github.com/IntersectMBO/cardano-db-sync/blob/master/doc/smash.md)
  - [CIP-26](https://cips.cardano.org/cip/CIP-0026)
  - [CIP-72](https://cips.cardano.org/cip/CIP-0072)


