# 24 - PACT: Wallet Contract Services

## Status

Proposed

---
| -         | -                                       |
|-----------|-----------------------------------------|
| date      | March 22, 2026                          |
| deciders  | TBD                                     |
| consulted | TBD                                     |
| informed  | TBD                                     |
---

## Context and Problem Statement

Midnight DApps own private execution: they store private state, execute circuits, connect to proof
servers, and manage contract maintenance. This creates three problems:

1. **Irrecoverable state.** Private state in LevelDB (IndexedDB in browsers) is destroyed by cache
   clears, extension uninstalls, or device resets. It cannot be reconstructed from on-chain data or
   seed. For contracts holding shielded tokens, this means permanent loss of funds. State is
   fragmented across N DApp stores with no unified backup.

2. **Hard fork fragility.** Ledger version changes (v6 → v7 → v8 across midnight-js v3.0 → v4.0)
   require every DApp to independently update dependencies, regenerate ZK artifacts, and update
   on-chain verifier keys. If a DApp is abandoned, signing keys locked in its LevelDB make verifier
   key updates impossible — contracts are stranded.

3. **Uncontrolled privacy.** DApps directly access private state and control proof server
   connections. Users trust each DApp individually with no centralized policy.

Aztec solves this with a PXE (Private eXecution Environment) that moves circuit execution into the
wallet. Analysis of complex Midnight DApps (Seabattle) shows this is not viable: DApps construct
domain-specific private state, provide witness functions called during execution, call pure circuits
for UI, and orchestrate multi-contract flows. Moving execution to the wallet means running arbitrary
DApp code in a privileged context.

This ADR proposes **PACT** (**P**roving, **A**uthority, **C**ustody & main**T**enance) — wallet
services that solve these problems without absorbing DApp logic.

## Decision Drivers

* Private state loss permanently destroys access to funds — must support backup and recovery
* Abandoned DApps must not strand contracts at hard forks
* Proof server policy should be wallet-controlled
* Complex DApps need direct access to private state — the wallet cannot replace DApp logic
* Ecosystem alignment: wallet-sdk and DApp Connector API already support proving delegation
* Headless/CLI DApps must continue working without a wallet

## Considered Options

* Option A: PACT — wallet provides custody, proving, and maintenance services
* Option B: Wallet-embedded PXE — wallet absorbs execution, state, and proving
* Option C: Library facade — unified API over existing DApp-owned providers

## Decision Outcome

Chosen option: "Option A: PACT", because it solves durability, hard fork, and privacy problems
without requiring the wallet to execute arbitrary DApp code.

| Service | Wallet | DApp |
|---------|--------|------|
| **Custody** | Stores state + signing keys. Encrypts, backs up, recovers. | Constructs/mutates state via API. Provides witnesses. |
| **Proving** | Proves, balances, signs, submits. Controls proof server policy. | Executes circuits locally. Provides ZK artifacts. |
| **Maintenance** | Updates verifier keys. Manages authority. Reports health. | Provides new artifacts after recompilation. |

The wallet is a service provider, not a runtime. DApps retain circuit execution, witnesses, state
construction, and multi-contract orchestration.

### Positive Consequences

* Durability — single managed store with unified backup for all contracts (state + signing keys)
* Hard fork resilience — wallet batch-updates verifier keys, even for abandoned DApps
* Extension storage survives browser cache clears
* DApp autonomy preserved — no arbitrary code in wallet
* Proof server policy centralized in wallet

### Negative Consequences

* DApp still sees private state in memory (unavoidable for witnesses and state construction)
* DApp Connector API needs new custody and maintenance methods
* Wallet complexity increases
* Maintenance depends on availability of new ZK artifacts for abandoned DApps

## Validation

* **Custody**: Uninstall wallet → reinstall → import backup → all contracts accessible. Browser
  cache clear does not affect wallet-held state.
* **Proving**: DApps no longer import `httpClientProofProvider`. E2E tests pass.
* **Maintenance**: After simulated hard fork, wallet updates verifier keys without DApp involvement.

## Pros and Cons of the Options

### Option A: PACT

DApps read/write state through the wallet API. Wallet provides storage, proving, and maintenance.
DApps retain circuit execution and domain logic.

* Good, because solves durability, hard forks, and proof server policy
* Good, because preserves DApp autonomy
* Good, because no arbitrary code in wallet
* Neutral, because DApp still sees state in memory
* Bad, because DApp Connector needs new methods
* Bad, because wallet complexity increases

### Option B: Wallet-Embedded PXE

Wallet absorbs circuit execution, private state, and proving. DApps send intent + artifacts.

* Good, because full DApp isolation
* Bad, because wallet runs DApp-provided witness functions (arbitrary code in trust boundary)
* Bad, because complex DApps need direct state access (witnesses, pure circuits, multi-contract)
* Bad, because not viable without sandboxing

### Option C: Library Facade

Unified API over existing DApp-owned providers. Reduces boilerplate.

* Good, because simplest to implement
* Bad, because durability unchanged — N fragile LevelDB stores
* Bad, because hard forks still require N DApp upgrades
* Bad, because signing keys scattered across DApp stores

## Hard Fork Impact

| Concern | Current | With PACT |
|---------|---------|-----------|
| Private state migration | Each DApp independently | Wallet — single operation |
| Verifier key updates | Signing keys in DApp LevelDB | Wallet — batch-updates, works for abandoned DApps |
| Proof system changes | Each DApp's proof server | Wallet's ProvingService |
| Ledger/runtime upgrade | Each DApp | Still each DApp (circuit execution remains DApp-side) |

PACT does not eliminate DApp upgrades for circuit execution. It removes the critical failure:
signing keys locked in abandoned DApps.

## Open Questions

* **ZK artifacts for abandoned DApps.** Wallet needs new artifacts to update verifier keys. Options:
  public artifact registry, on-chain hashes for community recompilation, compiler determinism.
* **Backup mechanism.** Encrypted cloud backup, seed-derived re-encryption, or on-chain fragments.
  Current API splits state and signing key exports; PACT should unify. Follow-up ADR needed.
* **Proof server trust.** Proof server sees circuit witnesses. Mitigations: wallet-enforced policy,
  future in-process WASM proving.
* **State migration.** Existing DApp LevelDB stores need migration to wallet custody. Existing
  export/import API is a starting point.
* **Headless DApps.** Server/CLI DApps continue using direct providers. PACT is for wallet-mediated
  interactive contexts. Both coexist indefinitely.

## Related ADRs

- [[ADR-0016]]: Forks and change management
- [[ADR-0017]]: Signature scheme
- [[ADR-0020]]: Key sampling / derivation
- [[ADR-0021]]: Contract maintenance authorities
