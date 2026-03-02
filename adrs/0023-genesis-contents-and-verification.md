# Genesis contents and verification

## Status

accepted

---

| -         | -                                                                            |
| --------- | ---------------------------------------------------------------------------- |
| date      | November 2025                                                                |
| deciders  | Andrzej Kopeć                                                                |
| consulted | Thomas Kerber, Oscar Bailey, Ignacio Palacios Santos, Jon Rossie, Giles Cope |
| informed  |                                                                              |

---

## Context and Problem Statement

Usually blockchains start with a genesis file(s) capturing hard-coded values impossible (or
infeasible) to verify their origin. Much of Midnight's initial configuration falls into this
category. Though, there are some areas of the genesis configuration, which are unique to Cardano
Partner chains, Midnight's tokenomics and its governance too.

## Decision Drivers

- identify the data needed in genesis configuration
- identify ways to validate the genesis configuration values
- identify flow of data validation for 3rd parties

## Decision Outcome

### Genesis configuration

Following data need to be present in genesis configuration supporting generation of the chainspec:

- seed for RNG
- network id
- Cardano reference block hash; this block is the one at which data dependent on Cardano state is
  obtained and verified against; It is particularly important for verification of the treasury
  initialization, as well as for bootstrapping the cNight Dust generation;
- cNight generating Dust (`cnight-genesis.json`):
  - references to resolve and observe (`cnight-addresses.json`):
    - mapping validator address (to observe Dust address mapping)
    - Glacier Drop redemption validator address (to observe cNight assignments still locked there)
    - auth token asset name (to follow on-chain governance)
    - cNight policy id and asset name (to observe cNight movements)
  - generation gestures in Cardano blocks up to the reference one (inclusive)
  - pointer to the reference block, to let the process restart from that point
- Governance (`federated-authority-config.json`):
  - contract addresses for the council and technical committee
  - policy ids associated with the council and technical committee
  - both Midnight and Cardano public keys of the authorities registered
- Treasury (treasury will be initialized by a Cardano transaction moving significant amount of Night
  to the _Illiquid Circulation Supply_ contract - one, which locks cNight as illiquid on Cardano, so
  that it can become liquid on Midnight):
  - ICS contract address
  - detected Night UTxOs held in the ICS at the reference block
  - computed amount of Night to be assigned to treasury (equal to the sum of all cNight held in the
    ICS)
- Reserve - to maintain the
  [cross-chain token invariants](https://docs.google.com/document/d/125qhMYG_1Gha80jVIM0kkCmRctdRiJRyxbcnCdChPSM/edit?tab=t.0#heading=h.nw57vzbuo6wv)
  - Reserve contract address
  - detected Night UTxOs held in the reserve at the reference block
  - computed amount of Night to be assigned to reserve (equal to the sum of all cNight held in the
    reserve)
- Ledger
  - initial parameters: cost model, limits, fee parameters, Dust parameters
  - the cost model needs to be captured on a reference spec machine prior to genesis preparation
  - the global ttl value needs to be explicitly set to a duration of 2 weeks
    (`2 * 7 * 24 * 60 * 60s`) as it is not a default value as of time of writing
- Ariadne (`pc-chain-config.json`)
  - contract address and policy id for the permissioned validators
  - contract address for the permissionless validators
  - initial validators configuration based on the contract state at the reference Cardano block

### Chainspec

So that the chainspec, which actually contains data Substrate uses to initialize the chain,
contains:

1. Hashes of additional configuration files (listed below). These hashes _must_ be computed based on
   their contents normalized according to [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785), so
   that their formatting does not impact hashes. The hashes also have to be verified when processing
   the genesis block or on node boot.
   1. `cnight-addresses.json`
   2. `cnight-genesis.json`
   3. `federated-authority-config.json`
   4. `pc-chain-config.json`
   5. `pc-resources-config.json`
2. Initial ledger state, fully initialized, that is:
   1. Locked, reserve and treasury pools initialized accordingly to the amounts of Night in
      different pools on Cardano, so that cross-chain token invariants are maintained.
   2. All Cardano-based Dust generations initialized
   3. Ledger parameters matching the input (as described in
      [Genesis Configuration](#genesis-configuration))

> [!NOTE] The populated locked pool and reserve are protected at the node level. System transactions
> that move funds between pools (e.g. `DistributeNight`) can be submitted only through observation
> pallets with validator consensus, not through the governance extrinsic path. This ensures
> cross-chain correspondence cannot be broken by a governance action alone.

The cross-chain invariants mentioned above are related to the fact that Night does exist both as a
Cardano asset and as Midnight asset. Both chains have a total supply of 24B Night split across 3
pools: reserve, locked and unlocked. Unlocked pool includes all liquid Night on a particular chain -
wallet-held UTxOs, treasury, block rewards, etc. Tokens unlocked on one chain must be locked on the
other one.

The cross-chain safety relies on 3 rules, accounting for observation delay (need to wait for
finalization):

- Unlocked Night on Midnight never exceeds locked cNight on Cardano
- Unlocked cNight on Cardano never exceeds locked Night on Midnight
- Cardano's reserve never exceeds Midnight's reserve

Main theorem: The combined unlocked supply across both chains never exceeds 24B.

In order for these invariants to hold forever, \_we need an inductive proof of protocol correctness
starting from a correctly configured "base case" in the Genesis block.

Base case (genesis): At launch, each Midnight pool exactly equals its Cardano counterpart. The
cross-chain safety inequalities start as equalities. The treasury is the only unlocked pool on
Midnight populated at launch, so it is initially equal to the locked pool on Cardano. The treasury
is not explicitly part of the cross-chain invariants, so its initialization is merely a reflection
of the locked/unlocked invariant.

Genesis must get this right because every subsequent protocol action preserves the inequalities
inductively — if the base case is wrong, the safety guarantees are unsound from block zero.\_

### Genesis block contents

Extrinsics in the genesis block are present only on testnets to perform initial token assignments.
Manifested by

1.  `SystemTransaction::DistributeReserve` to unlock the Night tokens on Midnight
2.  `SystemTransaction::DistributeNight` transaction(s) with the desired assignments
3.  Regular transactions to mint shielded tokens and/or start Dust generations

### Generation and verification

Operationally, the generation process requires all the mentioned Cardano contracts to be deployed,
configured with the right data, and the reference block finalized. This dependency is particularly
important for the permissionned validators, as they need to be ready to start producing blocks when
the chain is launched.

Much of these is based on Cardano data, hence 2 related processes are needed: for creation of
chainspec and for verification of whole genesis configuration and genesis block. A critical design
property is that the genesis creation is fully deterministic - given the same Cardano reference
block and other inputs - any party must be able to independently produce an identical genesis block
and verify it.

Additionally, governance authorities may choose to publish a Cardano transaction containing
Midnight's genesis block hash, signed unanimously, as an additional trust anchor.

#### Chainspec&genesis creation

The process for creation of chainspec _must_ be automated to reduce likelihood of a human error or
data consistency issues.

It takes information listed below as an input, and fetches Cardano based information using the same
logic as the running chain to produce full genesis configuration as listed above, as well as the
chainspec. It must verify that the Cardano block provided as reference is already finalized one. It
must also verify that the contract references provided are already deployed.

Inputs:

1. connection to a Cardano indexer like db-sync
2. seed for RNG
3. network ID / chain Id
4. timestamp - it is not strictly needed for the creation process itself (since a wall-clock time
   should be used for such purpose); it must be an available input for the verification and
   reproducibility purposes though; At the very least it has to be at least 24h after the reference
   Cardano block timestamp
5. Ledger initial parameters
6. Cardano reference block hash
7. Cardano references (contract addresses, minting policy IDs, etc.):
   1. Night asset details: policy id and label
   2. Governance (contract addresses and policy ids for the Counsil and Technical Comittee)
   3. ICS contract address (for treasury, and in future - protocol bridge)
   4. Reserve contract address (for reserve)
   5. Ariadne (Permissioned/permissionless comittee contract addresses, Ariadne governance contract
      address, genesis UTxO, Cardano parameters)
   6. Dust generation contract addresses (mapping validator address, redemption validator address)
8. List of initial assignment extrinsics (for mainnet MUST be empty!)
9. Boot nodes list

> [!NOTE] During some testing period (and some testnets), it may be the case that Reserve and ICS
> contracts are not deployed or do not hold the expected amount of Night. In such a situation it is
> allowed to provide as an input amounts of Night to assign to treasury and reserve pools on a basis
> of temporary workaround. These options hinder the ability of independent verification though, and
> as such - must not be used for generation of mainnet genesis. In testing, they should not be used
> as soon as the tokens are properly distributed between relevant Cardano contracts.

#### Genesis verification

The process for verification should be automated in as big part as possible. The verification
process has to be well-documented, so that:

- Midnight users can verify data integrity
- It acts as a part of a network deployment checklist (not only mainnet, but also new testing
  networks deployed in the future)

It takes as an input the genesis configuration and connection to a Cardano indexer like db-sync. It
performs following steps to perform verification:

1. Extract the data, which is input to genesis creation
2. Re-create the Cardano-based genesis configuration contents by querying the provided Cardano
   indexer (which also verifies the reference Cardano block too for its presence and finality)
3. Verify utxos:
   - (mainnet only) Verify that initial ledger state contains empty unshielded UTxO set
   - (testnet only) Verify that initial ledger state contains only expected Night UTxOs
4. (mainnet only) Verify that all of 24B Night is distributed between locked pool, reserve and
   treasury
5. Verify that the Dust generations match the ones specified in `cnight-genesis.json` file
6. Verify that sudo and glutton pallets are not present in the runtime (this check can be skipped in
   testing environments)
7. Verify that chainspec hashes of genesis configuration files (as listed in
   [Chainspec](#chainspec))
8. Verify that the upgradeable Cardano contracts (ICS, Federated authorities for governance and
   permissioned validators) are all configured with the right authorization script, it must be the
   same value for all the contracts.
9. (mainnet-only, only as a potential future extension) Verify that there exists a Cardano
   transaction with the genesis block hash in its contents (metadata?), which is signed unanimously
   by the governance authorities. Due to the nature of the process, it is impossible for the
   transaction to be published earlier or in the same block that serves as the reference.

## Alternative options considered

### Verify by re-generating chain-spec file

This option assumes following changes compared to the chosen one:

1. No integrity hash in the genesis
2. The genesis verification is a 3-step process:
   1. Re-generate genesis configuration based on the configuration present
   2. Using the fresh data, re-generate chain-spec
   3. Compare present and freshly generated chain-specs

This option is rejected, because it would be very brittle in presence of runtime changes or ledger
upgrades. It would significantly increase maintenance burden or it would require changes in soon
future.

### Include `SystemTransaction::CNightGeneratesDustUpdate` extrinsics in genesis

This option would likely exceed genesis block size limit.

## Validation

- given indicated input data, contents of the genesis configuration can be independently verified
  and re-created when it comes to data coming from Cardano and Ledger parameters

## Negative consequences

Proposed approach may incur additional maintenance burden on the node, as the specific format of
genesis configuration used to generate long-lived chain specifications needs to be maintained.

## Positive consequences

There exists an assurance that the contents of the genesis block accurately reflect Cardano-based
data

## Open questions

**Should identity of parties performing setup actions on Cardano be captured (e.g. their public
keys)?**

It does not seem to be worth the effort if there are multiple different wallets involved. But it
would be a powerful check if only 1 or 2 public keys (sets) perform all setup transactions on
Cardano.

Actually, it seems that _all upgradeable_ contracts in use should refer to the same governance.
Thus, the check if they are configured to refer to the same governance contract/policy id is the
desired one.
