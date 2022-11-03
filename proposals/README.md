# Proposals for Midnight Architecture
Here is a list of proposed changes captured in proposal documents.  We
deliberately keep the proposal format lightweight as any changes will eventually
be captured as ADRs.

## Naming and Numbering Scheme
The proposals should follow sequential numbering scheme, stating from `0001`.
File names should use `kebab-case` without any non-ASCII characters.

## List of proposals
- [0001: Template Proposal](./0001-template.md) for writing new proposals.
- [0003: A Language for Public Oracles](./0003-public-oracle-language.md) for the high-level options for public oracles.
- [0004: Micro ADT language](./0004-micro-adt-language.md) for the details of our initial public oracle language.
- [0005: Transaction Structure v1](./0005-transaction-structure-v1.md) for the initial specification of Midnight's transaction structure.
- [0006: Coins in Abcird](./0006-abcird-coins.md) for specifying how coins should be used in Abcird.
- [0007: Contract Interfaces in Abcird](./0007-abcird-contract-interfaces.md) for handling private oracle calls and calls to other contracts in Abcird.
- [0008: Signatures of Knowledge in Abcird](./0008-abcird-sok.md) for noting that we want to target SoKs.
