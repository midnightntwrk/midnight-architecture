# Midnight Wallet Specification

This document is meant to be a reference for wallet implementors: explaining the differences between other well-known blockchain protocols, providing details on data needed to successfully create and submit transactions, as well as provide practical insights. There are some aspects of cryptography and algorithms used, which are unique to wallet, and thus - are explained in more detail, while others, more ubiquitous across the stack - are meant to be a target of separate documents.  

Midnight features a unique set of features, which influence the way wallet software can operate significantly. In particular, in comparison to many other blockchain protocols:
- transactions are not sealed with signatures
- usage of zero-knowledge technology requires users to generate proofs, which takes relatively a lot of resources: time, CPU and memory
- knowing wallet balance requires iterating over every single transaction present

This document comprises a couple of sections:
1. *[Introduction](#introduction)* - which explains, how addressing goals stated for the protocol leads to differences mentioned above
2. *Key management* - where the details of key structure, address format and relationship with existing standards are provided
3. *Transaction structure* - which explains, what data are present in transactions
4. *State management* - where state needed to build transactions is defined, together with operations necessary to manipulate it
5. *Transaction building* - on the details and steps to be performed to build transaction

<!-- TOC -->
* [Midnight Wallet Specification](#midnight-wallet-specification)
  * [Introduction](#introduction)
    * [Non-interactive zero knowledge proofs of knowledge (NIZK)](#non-interactive-zero-knowledge-proofs-of-knowledge-nizk)
    * [Coin nullifiers and commitments](#coin-nullifiers-and-commitments)
    * [Binding randomness](#binding-randomness)
    * [Output encryption and blockchain scanning](#output-encryption-and-blockchain-scanning)
    * [Summary](#summary)
<!-- TOC -->

## Introduction

Wallet is an important component in a whole network - it stores and protects user's secret keys and allows to use them in order to create or confirm transactions.

It is often the case, that for user's convenience, wallets also collect all the data necessary for issuing simple operations on tokens. Midnight Wallet is no exception in this regard, one could even say, that in case of Midnight, that data management is a particularly important task because the data needed to create transaction is not only sensitive, but also computationally expensive to obtain. This is a common property to many, if not all implementations of protocols based on [Zerocash](http://zerocash-project.org/media/pdf/zerocash-extended-20140518.pdf) and [CryptoNote](https://bytecoin.org/old/whitepaper.pdf) protocols of privacy-preserving tokens, and Midnight shielded tokens protocol belongs to this family, as it is based on [Zswap](https://iohk.io/en/research/library/papers/zswap-zk-snark-based-non-interactive-multi-asset-swaps/), which is related to an evolution of Zerocash protocol.

Zswap, as a protocol for privacy-preserving tokens, has 3 major goals:
1. Maintain privacy of transfers, so that it is impossible to tell:
   - who the input provider (sender) is, unless one is the provider themself
   - who the output recipient is, unless one created that output or is the recipient
   - what amounts were moved, unless one is sender or receiver of particular output
   - what kinds of tokens were moved, unless one is sender or receiver of the token
2. Allow to maintain privacy, while using a non-interactive protocol. That is - to not need interact with the network or other parties after transaction was submitted.
3. Allow to make swap transactions

It appears, these 3 goals combined, motivate usage of specific tools and data structures, that have significant impact on the wallet. Let's see what they are, and how they are used thorough the lifecycle of a coin.

### Non-interactive zero knowledge proofs of knowledge (NIZK)

They provide one, but crucial capability - prove certain computation was performed according to predefined rules, without revealing private data inputs. This means that eventually transaction can contain only the zero-knowledge proof about all the data (including private one) used to build the transaction and some additional data, which has to be public in order to properly evolve the ledger state and allow it to verify future transactions. And that after transaction is submitted - there is no need for additional interaction in order to verify transaction validity.

The predefined rules encoded in the proofs are:
- sender has the right to spend coins provided as inputs
- the transaction contains only specific inputs and outputs
- auxiliary data for preventing unbalanced spends (see [Coin nullifiers and commitments](#coin-nullifiers-and-commitments))

### Coin nullifiers and commitments

Inputs and outputs of a transaction can be thought as exchanging banknotes - each has its (secret) serial number (nonce), currency (type) and value. But the goal is to exchange them while maintaining privacy, so nonce, type, and value should not be publicly available, and at the same time - ledger needs to be assured no tokens are created out of thin air. 

The zero-knowledge proof can assure ledger that no new tokens are created in a transaction - that for each token type the value in inputs covers the value in outputs up to a certain, publicly known imbalance, which is the difference between value from outputs and value from inputs. Having this assertion in place, what is left, is to ensure that:
- no coin is ever used twice (double spend)
- coin was indeed created in an earlier transaction

Preventing double spends is achieved using _nullifiers_ - these are hashes, which take as input: coin (value, type and nonce) and sender secret key. Involvement of sender secret key allows only sender to calculate nullifier that will match the one encoded in a proof, while the whole coin makes each nullifier unique for that coin. Ledger keeps track of nullifiers in a set data structure, so that whenever an input provides a nullifier, which already is known to ledger - it means the transaction should be rejected, because a double spend attempt is taking place.

Ensuring that coin was earlier created as an output is slightly more involved. Firstly, it requires a function to calculate value called coin commitment. This function takes coin as an input, together with receiver address. This allows both sender and receiver to calculate the same value, but no one else (because coin nonce is secret). Each output to the transaction has the commitment publicly readable, and ledger tracks them in a data structure called Merkle tree, which allows to generate a succinct proof that a value is stored in the tree. Such proof needs to be provided when spending a coin. If the proof leads to a tree root, which ledger did not register - it means the coin being spent was not created in a transaction known to the ledger.

### Binding randomness

Many other protocols make use of signature schemes to prevent transaction malleability and prove credentials to issue transaction. To enable atomic swaps, ultimately needed are (at least) 2 parties, which create matching offers, which eventually are combined into a single transaction or executed within a single transaction. The approach Zswap is taking to enable atomic swaps is by allowing controlled malleability - namely merging transactions. But this means known signature schemes can not be used as they prevent malleability completely. It is already not needed to prove credentials to issue transaction - each input and output has relevant zero-knowledge proof attached. 

It is enabled by a construction called _sparse homomorphic commitment_, which is built from 3 functions:
1. for calculating a value commitment for a set consisting of pairs of coin type and value, and additional random element called randomness
2. for combining the value commitments
3. for combining the randomnesses

These functions are carefully selected so that together they provide a really nice properties:
- combining commitments is equal to calculating a commitment for a set being a sum of sets provided to combined commitments and randomnesses combined too
- commitment for a coin when value is equal 0 is equal to a commitment of an empty set

With such scheme in place one can do the following: 
- attach the commitment to each input and output as well as calculate it in its proof (so that proof binds the input or output it is attached to)
- combine randomnesses of all inputs and outputs and attach it to the transaction
- attach to transaction imbalances of each token type

This allows to ensure that transaction was not tampered with, because resulting combination of commitments of all inputs, outputs and imbalances needs to be equal to commitment of an empty set with transaction randomness, if they differ - it means transaction was tampered with. And, because it is known how to combine both commitments and randomnesses, it is possible to merge two transactions into one and still make this check pass. 

### Output encryption and blockchain scanning

With just zero-knowledge proof no additional interaction is needed to verify transaction, but there is no way for the receiver to know, that there exists a transaction, which contains a coin meant for them. Attaching any identifier would end up with not meeting privacy goal, for that reason outputs can have attached coin details, encrypted with receiver's public key. So that in a pursuit in lack of interaction, one can scan a blockchain transaction outputs for ones that decrypt successfully with own private key.

### Summary

Zswap reaches its goals of maintaining privacy using a non-interactive protocol and allowing swaps through a combination of zero-knowledge technology, coin nullifiers and Merkle tree of coin commitments tracked by ledger, sparse homomorphic commitments and output encryption. This indicates high level goals of wallet software for Midnight, which need to be met in order to be able to create a transaction, that will be accepted by Midnight's ledger:
- generate proper zero-knowledge proofs
- track coin lifecycle to prevent double spends
- keep access to an up-to-date view on the Merkle tree of coin commitments, which allows to generate inclusion proofs for coins owned by particular wallet instance
- derive relevant keys
- calculate nullifiers, coin commitments, value commitments as well as combine them accordingly
- encrypt and decrypt outputs
- scan blockchain transactions for own outputs

