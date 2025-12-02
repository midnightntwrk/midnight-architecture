# Genesis contents and verification

## Status

proposed

---

| -         | -                                                    |
| --------- | ---------------------------------------------------- |
| date      | November 2025                                        |
| deciders  | Andrzej Kopeć                                        |
| consulted | Thomas Kerber, Oscar Bailey, Ignacio Palacios Santos |
| informed  |                                                      |

---

## Context and Problem Statement

Usually blockchains start with a genesis file(s) capturing hard-coded values impossible (or
infeasible) to verify their origin. Much of Midnight's initial configuration likely falls into this
category too. Though, there are some areas of the genesis configuration, which are unique to Cardano
Partner chains, Midnight's tokenomics and its governance too.

## Decision Drivers

- identify the data needed in genesis configuration
- identify ways to validate the genesis configuration values
- identify flow of data validation for 3rd parties

## Decision Outcome

Following data need to be present in genesis configuration:

- seed for RNG
- network id
- hash of its entirety for integrity check:
  - the hashing needs to be performed on data normalized according to
    [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785)
  - for the hashing purposes, the hash itself needs to be removed from the data, similarly to how
    signature needs to be removed for verification
    ([RFC 8785 Appendix F](https://www.rfc-editor.org/rfc/rfc8785#impl.guidelines))
  - given the configuration spans across multiple files, the final hash is SHA-256 of a normalized
    JSON document, where keys are filenames, and values are their SHA-256 hashes hex-encoded (like:
    `{"cnight-genesis.json": "abcdeef...00", "federated-authority-config.json": "12435445...beea"}`)
- Cardano reference block hash
- Protocol bridge:
  - ICS contract reference
  - bridge transactions made in Cardano blocks up to the reference one (inclusive)
- cNight generating Dust
  - contract reference
  - generation gestures in Cardano blocks up to the reference one (inclusive)
- Governance
  - contract references for the council and technical comittee
  - both Midnight and Cardano public keys of the authorities registered
- Treasury (treasury will be initialized by a Cardano transaction moving significant amount of Night
  to the ICS contract)
  - ICS contract reference
  - detected treasury movements in Cardano blocks up to the reference one (inclusive)
- Ledger
  - initial parameters: cost model, limits, fee parameters, Dust parameters
  - it has to be done through `OverrideParameters` system transaction, in order to enable Indexer to
    learn the exact values
- Ariadne
  - contract references
  - initial validators configuration based on the contract state at the reference block

Much of these is based on Cardano data, hence 2 tools are needed:

1. Genesis creation; It takes information listed below as an input, and fetches Cardano based
   information using the same logic as the running chain to produce full configuration as listed
   above. It must verify that the Cardano block provided as reference is already finalized one. It
   must also verify that the contract references provided are already deployed.
   - inputs:
     1. connection to a Cardano indexer like db-sync
     2. seed for RNG
     3. network ID / chain Id
     4. Ledger initial parameters
     5. Cardano reference block hash
     6. Cardano references (contract addresses, minting policy IDs, etc.), for:
        1. Governance (contract addresses and policy ids for the Counsil and Technical Comittee)
        2. Protocol Bridge (ICS contract address, Night policy id, Night label)
        3. Treasury (same as for Protocol Bridge)
        4. Ariadne (Permissioned/permissionless comittee contract addresses, d-param contract
           address, Ariadne governance contract address, genesis UTxO, Cardano parameters)
        5. Dust generation contract addresses (mapping validator address, redemption validator
           address, Night policy id, Night label)
     7. List of initial assignment extrinsics (for mainnet MUST be empty!)
     8. Boot nodes list
2. Genesis verification; It takes as an input the genesis configuration and connection to a Cardano
   indexer like db-sync. It performs following steps to perform verification
   1. Extract the data, which is input to genesis creation
   2. Re-create the Cardano-based genesis contents by querying the provided Cardano indexer (which
      implicitly verifies the reference Cardano block too for its presence and finality)
   3. Compute the integrity hash of newly generated genesis configuration, then compare the hash
      present in the configuration already
   4. Verify if the extrinsics being part of the genesis block contain matching:
      1. bridge transactions
      2. Dust generations
      3. treasury transaction
      4. Ledger parameters setup

## Alternative options considered

### Verify by re-generating chain-spec file

This option assumes following changes compared to the chosen one:

1. No integrity hash in the genesis
2. The genesis verification is a 3-step process:
   1. Re-generate genesis configuration based on the configuration present
   2. Using the fresh data, re-generate chain-spec
   3. Compare present and freshly generated chain-specs

This option is rejected, because it would be very brittle in presence of runtime changes or ledger
upgrades. It would significantly increase maintenance burder or it would require changes in soon
future.

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
