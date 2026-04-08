# Proposals for Midnight Architecture
Here is a list of proposed changes captured in proposal documents.  We
deliberately keep the proposal format lightweight as any changes will eventually
be captured as ADRs.

## Naming and Numbering Scheme
The proposals should follow sequential numbering scheme, starting from `0001`.
File names should use `kebab-case` without any non-ASCII characters.

## List of Proposals

- [0001: Template for Midnight Architecture Proposals](./0001-template.md) for writing new proposals
- [0002: Error Handling in TypeScript](./0002-error-handling-in-TS.md) for TypeScript error handling
- [0003: A Language for Public Oracles](./0003-public-oracle-language.md) for the high-level options for public oracles
- [0004: Micro ADT Language](./0004-micro-adt-language.md) for the details of our initial public oracle language
- [0005: Transaction Structure (Version 1)](./0005-transaction-structure-v1.md) for the initial specification of Midnight's transaction structure
- [0006: Coins in Abcird](./0006-abcird-coins.md) for specifying how coins should be used in Abcird
- [0007: Contract Interfaces in Abcird](./0007-abcird-contract-interfaces.md) for handling private oracle calls and calls to other contracts in Abcird
- [0008: Signatures of Knowledge in Abcird](./0008-abcird-sok.md) for noting that we want to target SoKs
- [0009: Sealed Ledger State](./0009-sealed-ledger-state.md) for changes to Compact syntax to support immutable ledger state
- [0010: Composable Contracts Syntax](./0010-composable-contracts-syntax.md) for changes to Compact syntax to support composable contracts
- [0011: Contract Interface Types](./0011-contract-interface-types.md) for changes to Compact syntax to support contract interface types
- [0012: Upgrades with Forks](./0012-forks.md) for upgrading the Midnight chain
- [0013: Midnight HD Wallet](./0013-hd-wallet-options.md) HD (Hierarchical Deterministic) wallets for Midnight
- [0014: Compact Syntax Changes](./0014-compact-syntax-changes.md) for a batch of changes to Compact's syntax
- [0015: Functional Structure Update Syntax](./0015-spread-syntax-md) spread syntax for `struct` and vector creation
- [0016: Governed Parameters and Their Update Mechanics: Phase 1](./0016-governed-parameters-and-their-updates-phase-1.md) for mechanics of enacting governed parameters updates
- [0017: Flexible Network Identifier](./0017-flexible-network-id.md) for change network id structure and usage
- [0018: cNIGHT generates DUST](./0018-cnight-generates-dust.md) for DUST generation from NIGHT tokens on Cardano
- [0019: Cost Model](./0019-cost-model.md) for ledger cost model methodology
