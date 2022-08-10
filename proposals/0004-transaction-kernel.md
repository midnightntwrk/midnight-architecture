# Proposal 0004: Transaction Format and Smart Contract Kernel

This proposal describes Midnight's high-level transaction structure, transaction
creation and validation, and how contracts can interact with other parts of a
transactions.

# Problem Statement

Kachina defines contracts as independant state machines. We want a level of
interdependance that needs extra though: Contracts should be able to hold
currency, and should be able to interact with other contracts.

# Proposed Changes

## Transaction Format

[transaction consists of Zswap, inputs, outputs, transitory value commitments, contract interactions, binding signature, links between them]

### Transaction Merging

[notes on it]

## Funds Held by Users vs Contracts

[Zswap inputs/outputs distinguishing, needing proof of authorization for the latter]

## Contracts and the Kernel

[priviledged circuits that can make priviledged queries. These access broader state: Transaction state, other contracts]

### Permissions

[why we need them, why they aren't fleshed out]

## Transaction Creation

[Start at a contract, slowly populate during a linear pass. Special care for input/output creations, bindings, and contract calls]

## Transaction Validation

[proofs, links, execution, etc.]

## Exposing Contract Interaction

[abcird passes to allow syntactic sugar over call]

# Desired Result
This proposal should enable mocking of the Zswap and smart contract kernel
components until their cryptography has been implemented. It should provide a
non-final API that is sufficiently close to our final API to provide a
meaningful stand-in for its developer experience.
