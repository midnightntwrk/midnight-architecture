# Genesis contents and verification

## Status

proposed

---

<!-- These are optional elements. Feel free to remove any of them. -->

| -         | -                                                                                                                            |
| --------- | ---------------------------------------------------------------------------------------------------------------------------- |
| date      | November 2025                                                                                                                |
| deciders  | {list everyone involved in the decision}                                                                                     |
| consulted | {list everyone whose opinions are sought (typically subject-matter experts; and with whom there is a two-way communication}) |
| informed  | {list everyone who is kept up-to-date on progress; and with whom there is a one-way communication}                           |

---

## Context and Problem Statement

{Describe the context and problem statement, e.g., in free form using two to three sentences or in
the form of an illustrative story. You may want to articulate the problem in form of a question and
add links to collaboration boards or issue management systems.}

Usually blockchains start with a genesis file(s) capturing hard-coded values impossible (or
infeasible) to verify their origin. Much of Midnight's initial configuration likely falls into this
category too. Though, there are some areas of the genesis configuration, which are unique to Cardano
Partner chains, Midnight's tokenomics and its governance too.

## Decision Drivers

- identify the data needed in genesis configuration
- identify ways to validate the genesis configuration values
- identify flow of data validation for 3rd parties

## Decision Outcome

Following data need to be present in genesis:
- seed for RNG
- network id
- hash of its entirety for integrity check:
  - the hashing needs to be performed on data normalized according to [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785)
  - for the hashing purposes, the hash itself needs to be removed from the data, similarly to how signature needs to be removed for verification ([RFC 8785 Appendix F](https://www.rfc-editor.org/rfc/rfc8785#impl.guidelines))
  - given the configuration spans across multiple files, the final hash is SHA-256 of a normalized JSON document, where keys are filenames, and values are their SHA-256 hashes hex-encoded
- Cardano reference block:
  - block height
  - block hash
- Protocol bridge:
  - ICS contract reference
  - bridge transactions made in Cardano blocks up to the reference one (inclusive)
- cNight generating Dust
  - contract reference
  - generation gestures in Cardano blocks up to the reference one (inclusive)
- Governance
  - contract references for the council and technical comittee
  - both Midnight and Cardano public keys of the authorities registered
- Treasury (treasury will be initialized by a Cardano transaction moving significant amount of Night to the ICS contract)
  - ICS contract reference
  - detected treasury movements in Cardano blocks up to the reference one (inclusive)
- Ledger
  - initial parameters: monetary policy and cost model
- Ariadne
  - contract references
  - initial validators configuration based on the contract state at the reference block

Much of these is based on Cardano data, hence 2 tools are needed:
1. Genesis creation; It takes information listed below as an input, and fetches Cardano based information using the same logic as the running chain to produce full configuration as listed above. It must verify that the Cardano block provided as reference is already finalized one. It must also verify that the contract references provided are already deployed.
   - inputs:
      1. connection to a Cardano indexer like db-sync
      2. seed for RNG
      3. network ID
      4. Ledger initial parameters (or name to resolve them in the code)
      5. Cardano reference block hash
      6. ICS contract address
      7. cNight generating Dust contract address
      8. governance contract address
      9. Ariadne contract reference
 2.  Genesis verification; It takes as an input the genesis configuration and connection to a Cardano indexer like db-sync. It performs following steps to perform verification
     1.  Verify data integrity by computing and comparing the genesis contents hash
     2.  Extract the data, which is input to genesis creation
     3.  Re-create the genesis contents by querying the provided Cardano indexer
     4.  Verify if exactly the same data was created by comparing the hash of their contents
  

## Validation

- given certain input data, contents of the genesis block can be independently verified and re-created
- 


## More Information

