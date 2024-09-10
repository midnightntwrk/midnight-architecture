# Metadata

Metadata in Midnight follows design principles from Cardano's [CIP-26](https://cips.cardano.org/cip/CIP-0026), namely:
- no requirement is stated for location of metadata or decentralization of the solution - different implementations are free to provide their services based on different policies
- server API is standarized, so clients and users are empowered to choose the service, which matches their criteria, regardless of preference of software authors
- metadata is standarized to a certain extent, so that well-known metadata can be thoroughly validated for well-formedness, but new, emerging metadata formats can still be accepted and standarized after getting adoption

For that reason this specification splits into 2 parts - abstract one, which leaves implementation details unspecified, and second, concrete one, which specifies specific implementation of the abstract part according to requirements stated in the [Token Minting/Burning & Metadata PRD](https://docs.google.com/document/d/1uhVGU7iV9OHMdo_HrMYVFAO-gvlnHkdHrkUvm0-hP3c/edit).

*TODO*: Should here be the reference to [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119) and [RFC 8174](https://www.rfc-editor.org/rfc/rfc8174)?

## Abstract protocol

Metadata management involves a couple of processes, which together provide all functionality:
- authoring metadata (new or an update)
- canonicalize metadata
- signing metadata
- submitting metadata
- serving metadata
- querying metadata

Metadata, regardless of its kind or subject must contain pre-defined common elements, they are defined as the [`CommonMetadata` interface](../apis-and-common-types/metadata/API.graphql) in API:

| name             | required | type                          | description                                                                                                                                                                               |
|------------------|----------|-------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| type             | ✅        | string                        | constant indicating what kind of metadata is being described (and what specification it follows)                                                                                          |
| subject          | ✅        | bech32 / hex-string / bytes   | reference to object being subject of the metadata, most often it will be a hash of on-chain object (like token type or contract)                                                          |
| version          | ✅        | positive integer              | a sequence number, increased with each update; registry should reject updates which do not increase version                                                                               |
| signatures       | ✅        | non-empty array of signatures | a signature and signer's public key, it needs to be reset whenever an update is made, adding own signature to the array is the only update, which does not require updating version field |

And format of a signature is:

| name       | required | type               | description                                                          |
|------------|----------|--------------------|----------------------------------------------------------------------|
| signature  | ✅        | hex-string / bytes | serialized signature over all of data excluding the signatures array |
| public_key | ✅        | bech32             | public key to use for verification                                   |

### Authoring metadata

All metadata types need to follow these common rules to pass well-formedness check:
- `version` field starts with 1 in the first metadata definition
- whenever an update to data other than signatures is made, version field needs to be increased by 1 and signatures array cleared
- at least one valid signature is needed
- all signatures present need to be valid

TODO: does requirement of increases by 1 lead to issues? Is the contention it may create a bad thing? Given the version is scoped to 32 bits, would requirement of it being non-zero and increased at all lead to issues? Would it be bad if someone chosen 2^32-1 as initial version number?
No, it solves them actually, because the contention created forces people to adjust the metadata, so that important updates are not unknowingly lost

TODO: Would any form of hashing/Merkleization be useful here? Hashes of canonical form seem to make sense in some possible implementations
TODO: Should one version of metadata for a subject refer to its parent? Why? If yes - should servers be able to resolve metadata for a subject going back to the version 1?

### Metadata canonicalization

1. Remove `signatures` field (so that each signature can be added and verified independently)
2. Canonicalize remainder according to [RFC8785](https://www.rfc-editor.org/rfc/rfc8785)

### Signing metadata

Once metadata JSON document is ready, it can be signed. Signing must be performed only on a canonical document.

Exact steps to follow in order to sign metadata are:
1. Ensure metadata document is in canonical form
2. Produce signature using Schnorr scheme over secp256k1 curve (as defined on ADR)

TODO: Link signature ADR

### Metadata submission

Specific to metadata submission are entirely implementation-dependent. There is only one invariant to be held and respected by receiving and submitting parties - well-formedness checks as defined in [Authoring flow](#authoring-metadata).

### Serving metadata 

Regardless of underlying storage, update mechanics, etc., metadata server needs to implement the [API](../apis-and-common-types/metadata/API.graphql) and serve it over HTTP(S) with JSON as serialization format. Implementations are allowed to serve the API using different protocols and using different serialization formats in addition to HTTP(S)+JSON. 

### Querying metadata 

Clients interact with the [API](../apis-and-common-types/metadata/API.graphql). Regardless of implementation, clients should perform well-formedness checks (as defined in [Authoring flow](#authoring-metadata)). Clients are free to perform additional checks, depending on their implementation, trust assumptions, etc., like:
- verifying signer's public key against allowed/prohibited list
- checking metadata against different source or an anchor (being hash of metadata canonical form published in a different place, like on-chain)

Clients should allow their users to freely adjust URI of the server used.

TODO: what are possible trust roots? What would be needed to e.g. employ DIDs or have an attestation DApp?

## Concrete implementation

### Components

Do in icepanel

- Mn.js metadata utils
- Run by Indexer:
  - Metadata server
  - Metadata repo synchronizer
- Repo automation (CI step for uploads, using the mn.js utils)

### Steps

__Cross-linked with icepanel__

#### Authorship

- mn.js has well-formedness checks, exposed both as a function taking POJO as an argument as well as a CLI command taking a path to file to check

#### Canonicalization

- mn.js has function to canonicalize metadata object (passed as a POJO)

#### Signing

- mn.js has function to sign canonical metadata object (passed as a POJO) 
- mn.js has a CLI to sign arbitrary metadata (which performs well-formedness check, canonicalize metadata and then signs them):
  - it takes path to metadata file as an argument
  - it takes argument indicating, where to write the output - either path to file to write signed metadata, to stdout or to overwrite the source file
  - it takes argument indicating source of key material - stdin or file containing raw bytes/bech32 
- mn.js has function to verify a signature as well as CLI to verify all signatures
- the function to sign is able to work with a directly-passed keypair or delegate signing to instance of  wallet-api or wallet-dapp-connector, so that more automation/integration
- Wallet should implement an API to sign data using chosen key (by choosing role only, see the HD-wallet proposal)

TODO: link HD wallet proposal

#### Submission and CI process

- repo layout follows the structure, where each metadata file is present in "data" directory, and filename follows pattern "<subject>.json"
- each file needs to pass well-formedness check
- each file name needs to match its subject
- no metadata file removals are allowed
- no direct pushes to the main branch are allowed
- preferably, metadata signers meet contract maintenance authority of contract linked


TODO:
Should a designated moderator team be held to review and merge entries?
Should name and ticker should be checked for being unique (as well as within ~1 hamming distance to others in the repository), and flagged if failing this check, so manual intervention is needed?
Should a Merkle tree be built out of all metadata, so that server can provide merkle proof when serving metadata? How would client learn the root? Would it be usable and reasonable? How to scale those mechanics for other forms of attestation?

#### Serving

- Indexer serves the API, either straight from files or by indexing the contents into DB
- Indexer also has a syncing component, so that it can serve the data soon after they reach a specific point in the repository
  - it can be based on polling, e.g. by performing regular git fetches
  - it can also be based on a webhook from the repository, followed by git fetch - this case though requires that:
    - proper webhook verification is performed
    - polling still needs to be used as a fallback (e.g. in cases of misconfiguration, or to simplify test deployments)

#### Querying

- mn.js exposes a simple client similar to existing one to get contract data, which matches the most common queries

## Security and risks

There is little present to help to build trust in the metadata. In the concrete design - it is provided in the submission process. In the abstract one, similarly to CIP-26 - it is deferred to implementations. This seems to pose a risk, that servers won't be able to provide verification information in a universal way, because each server implementation might use different data, from different source, in different format, to attest served data validity. Signatures themselves do not mean much if there is no mechanics present to build trust against public keys used. On the other hand - improving trust and security posture of the concrete design significantly increases amount of time needed to deliver the solution, because it needs to make sure that the abstract one nicely accommodates for it, and other kinds of verification too. Letting clients base their trust only in servers though, while being a simple approach, it becomes somewhat limiting in some cases.

## Related

CIP-26
CIP-72
