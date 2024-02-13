# Proposal 00009: Upgrades with forks

## Problem Statement
Midnight's design and capabilities, similarly to other chains, are not set in 
stone. There are many known and unknown protocol changes in the future, which will require a clear protocol, mechanism and policy for upgrades, so that they can be delivered to Midnight users without: 
- putting Midnight network to stop
- Midnight value at risk
- users data at risk
- users funds at risk

Focus for this proposal is on changes requiring hard-forks (see [Glossary](../product/Glossary.md)) because of their inherently trickier nature. It is very likely though, that the same protocol, mechanism and policy would apply to changes requiring soft-forks for consistency.

## Prior art

### Bitcoin

Bitcoin seems to have a strong policy against hard-forks, which directly led to inception of Bitcoin Cash.

So far only 2 hard forks occurred on Bitcoin, and both were incidental:
  - one from 2018: https://bitcoincore.org/en/2018/09/20/notice/
  - one from 2013: https://github.com/bitcoin/bips/blob/master/bip-0050.mediawiki

All the other updates are implemented through soft-forks.

The policy and protocol are explained in a series of BIPs:
  - [BIP-34](https://github.com/bitcoin/bips/blob/master/bip-0034.mediawiki) for the basic policy
  - [BIP-8](https://github.com/bitcoin/bips/blob/master/bip-0008.mediawiki) and [BIP-9](https://github.com/bitcoin/bips/blob/master/bip-0009.mediawiki) for scheduling multiple deployments concurrently, with possibility to time out ones not getting enough support

An example of a change implemented following that: https://github.com/bitcoin/bips/blob/master/bip-0066.mediawiki

In short, Bitcoin's approach is as follows:
  - take advantage of the fact, that block version number has more bits available, than reasonably needed to encode a single version number, to encode next version number too
  - enable new rules when 750 block out of last 1000 has encoded related next version
  - don't accept blocks with older versions when 950 out of last 1000 blocks has encoded related next version

In other words, if current version of block is `1`, and new rules are related to block version `2`:
  - old client software would be able to produce blocks `1` and would encode next version as `1` too (if at all)
  - new client software would be able to produce blocks `1` and `2`, and would encode next version as `2`
  - miners encode next version accordingly to capabilities of their software
  - once 750 out of 1000 blocks have encoded next version 2 - new rules are enabled for all blocks
  - once 950 out of 1000 blocks have encoded next version 2 or greater - blocks of version 1 are not valid anymore

### Ethereum

Ethereum approach is slightly different one - whenever a fork-requiring change is planned, it is specified with activation block height on networks maintained at the moment of planning.

Then, clients simply check for a block height to determine rules to use, which requires clients to maintain consistent configuration in order to participate in the network. It seems that mechanics used to choose set of rules to validate blocks really differ depending on a client. Ranging from simple `if`s spread over codebase, towards more structured approach.

An important note is that Ethereum in its Proof-of-Work days was equipped in a mechanism called difficulty bomb to force miners to deploy hard-forks.

Additionally, forks have unique hashes based on genesis, history of previous forks and block activation height to help with quick identification if client is connected to another node of the same network, as specified here: https://eips.ethereum.org/EIPS/eip-2124

Examples of hard-forks deployed to Ethereum:
  - https://eips.ethereum.org/EIPS/eip-606
  - https://eips.ethereum.org/EIPS/eip-1013
  - https://eips.ethereum.org/EIPS/eip-609
  - https://eips.ethereum.org/EIPS/eip-608
  - https://eips.ethereum.org/EIPS/eip-607
  - https://eips.ethereum.org/EIPS/eip-1716
  - https://eips.ethereum.org/EIPS/eip-7568
  - https://eips.ethereum.org/EIPS/eip-7569
  - https://github.com/ethereum/execution-specs/blob/8dbde99b132ff8d8fcc9cfb015a9947ccc8b12d6/network-upgrades/mainnet-upgrades/paris.md
  - https://github.com/ethereum/consensus-specs/blob/f8ae982c2fc7dbb03a3c95a638da4486310e09e9/README.md#stable-specifications

### Solana

In Solana, upgrades are scheduled on a per–feature basis. For a feature a dedicated key is being generated, then dedicated voting tokens are being minted and transferred to validators based on their stake. Finally, if voting result is in favor of a feature - it gets enabled in next epoch.

Sources:
  - https://spl.solana.com/feature-proposal
  - https://docs.rs/solana-program/latest/solana_program/feature/index.html
  - https://docs.rs/solana-sdk/latest/solana_sdk/feature_set/index.html

### Cardano

In Cardano, Shelley upgrade equipped the code and the protocol in capabilities for scheduling upgrades (among a couple of other governance actions).

In its initial form, the protocol is to issue a transaction signed by 5 out of 7 governing keys as defined in genesis, early enough in epoch to be stabilized on total of at least `4k` blocks before next epoch starts. With CIP-1694 the protocol changes to allow other forms of voting and proposing hard-fork activation.

Technically - it as all managed by a type-driven facade called _Hard-fork combinator_, which is ensuring state is properly adjusted to the active rules and that rules are activated properly.

Sources:
  - https://ouroboros-consensus.cardano.intersectmbo.org/docs/for-developers/AddingAnEra
  - https://github.com/IntersectMBO/ouroboros-consensus/blob/8bd8a920607bc256fb001f95621c48469adaf765/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator.hs#L4
  - https://docs.cardano.org/learn/about-hard-forks/

### Substrate/Polkadot

Substrate allows to perform upgrades to be recorded on-chain as a WASM code. This allows for having upgrades of the most functionality without need to update clients — and thus — forking.

This can be done either with sudo module or through governance:
  - https://wiki.polkadot.network/docs/learn-runtime-upgrades
  - https://wiki.polkadot.network/docs/learn-governance#enactment
  - https://docs.substrate.io/maintain/runtime-upgrades/

## Current state

Many data structures are already versioned with `MAJOR.MINOR` numbers and serialization verifies version compatibility following semantic versioning guidelines.

Also - Node implementation has a well-defined entrypoints for interaction with ledger for transaction validation and execution.

FRAME also requires runtime to be versioned for validation purposes.

We know, that ZK operations are taking a lot of time in WASM environment. 

## Proposed Changes
Describe your proposal in detail.

## Desired Result
Finally, describe what you hope to achieve and how you can evaluate that you
have achieved it.
