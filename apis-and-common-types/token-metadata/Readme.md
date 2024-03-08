# Token metadata

This document describes the shape of token metadata. This is one of foundational interfaces, that indicate to wallet users, what DApp/contract/network is the origin of the token and what the token might be used for.

## Problem statement

As mentioned in [ADR #12 Manual token names in wallet](../../adrs/0012-manual-token-names.md), the solution, where wallets users enter names for tokens they interact with, is only a stop-gap, until a different one is proposed. It is recognized, that such manual process is not very portable - token names would need to be entered by users on each fresh installation of a wallet, and it is hard to require from users to fill in any more data than the name, and maybe a DApp URL.

Contracts using multiple token types simultaneously and/or bridged tokens require even more metadata, like the metadata from the source chain and metadata for Midnight. For that reason compatibility with multiple standards need to be considered: 
  - Midnight-native
  - Ethereum's ERC-20 and ERC-721 (https://ethereum.org/developers/docs/standards/tokens)
  - Cardano's CIP-25, CIP-26, CIP-60 (https://cips.cardano.org, https://developers.cardano.org/docs/native-tokens/token-registry/cardano-token-registry/)
  - Solana's Token Metadata https://developers.metaplex.com/token-metadata/token-standard

## Tokens on Midnight

Tokens on Midnight are supported natively, using a pattern called "colored coins", that is - each token type is seen equally by ledger and each coin has a token type assigned.

These token types are calculated as a hash of contract address and contract-defined string. Single contract can mint multiple types of tokens, but they will all be related to that contract. There are no ledger-imposed restrictions in sending and receiving existing tokens.

Token metadata is held off-chain as mentioned in the [Off-chain token metadata ADR](../../adrs/0015-off-chain-token-metadata.md).

It is also known, that Midnight will have unshielded tokens, which needs to be reflected in the API described. 

## Basic Token metadata

Following the requirements and other standards it can be said, that the minimum metadata needed for a Midnight token would be:

| name             | required | type                         | description                                                                                                                                                                                           |
|------------------|----------|------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| subject          | ✅        | hex-string / bytes           | ledger-serialized token type, it is the default identifier of token and its metadata                                                                                                                  |
| contract_address | ✅        | hex-string / bytes           | ledger-serialized contract address                                                                                                                                                                    |
| domain_separator | ✅        | hex-string / 32 bytes        | domain separator as passed to `mint_token` standard library function                                                                                                                                  |
| shielded         | ✅        | boolean                      | flag, whether the token is a shielded one or not                                                                                                                                                      |
| name             | ✅        | string                       | name of a token, as should be displayed in e.g. wallet                                                                                                                                                |
| version          | ✅        | positive integer             | a sequence number, increased with each update; registry should reject updates which do not increase version                                                                                           |
| signatures       | ✅        | array of objects (see below) | a signature and signer's public key                                                                                                                                                                   |
| description      | ❌        | string                       | description of the token, it's very common, so should be present in many cases, though there are standards, which do not require description, so it would be impossible to be converted automatically |
| image            | ❌        | string                       | an URI (including a data base64 one) of an image representing the token, it's also very common, but many existing tokens do not have the image attached                                               |
| decimals         | ❌        | non-negative integer         | how many decimals are allowed to split token "units", e.g. for decimals value `3`, a coin with value `1`, would be `0.001` of a token "unit"                                                          |
| types            | ❌        | array of variant identifiers | additional types given token implement, described in [extenstions section below](#extensions)                                                                                                         |

And format of a signature:

| name       | required | type               | description                        |
|------------|----------|--------------------|------------------------------------|
| signature  | ✅        | hex-string / bytes | serialized signature               |
| public_key | ✅        | hex-string / bytes | public key to use for verification |

Metadata like above would satisfy a wide range of needs already. 
Type "hex-string / bytes" means that in languages having good support for byte strings (like Rust or Java), a byte string/byte array type is allowed, in JSON APIs the bytes data should be hex-encoded.  

Some examples, in JSON:
```json
{
  "subject": "f00abc",
  "contract_address": "010000cda",
  "domain_separator": "foo_token",
  "shielded": false,
  "name": "Foo",
  "version": 1,
  "signatures": [
    {
      "signature": "abcdef",
      "public_key": "012345"
    }
  ]
}
```

```json
{
  "subject": "f00abc",
  "contract_address": "010000cda",
  "domain_separator": "foo_token",
  "shielded": false,
  "name": "Foo",
  "version": 1,
  "signatures": [
    {
      "signature": "abcdef",
      "public_key": "012345"
    }
  ],
  "description": "My foo token",
  "image": "ipfs://aaa/image.png",
  "decimals": 0,
  "types": []
}
```

## Extensions

The metadata listed above is the basic, core one, that is likely to be provided by all tokens and easily converted from tokens from other chains, when bridged. For that reason there exists "types" field, which includes list of identifiers of token standards implemented/defined for a given token. And then, under a key of the same name, there is expected an object following given standards schema fully. Even if that means duplication of some information. 

Such format allows not only to support multiple standards simultaneously (e.g. for bridging in multiple directions) but also allows to define specific metadata types in future without changing the common format.

For example, there may be an ERC-20 token, that is bridged from Ethereum, in such case complete metadata on Midnight could look like this:
```json
{
  "subject": "f00abc",
  "contract_address": "010000cda",
  "domain_separator": "foo_token",
  "shielded": false,
  "name": "Foo",
  "version": 1,
  "signatures": [
    {
      "signature": "abcdef",
      "public_key": "012345"
    }
  ],
  "description": "My foo token",
  "image": "ipfs://aaa/image.png",
  "decimals": 0,
  "types": ["erc-20"],
  "erc-20": {
    "name": "Foo",
    "symbol": "FOO",
    "decimals": 3,
    "totalSupply": 10000000
  }
}
```

## Questions / concerns

### Should the domain separator be included in the metadata?

Yes. Having the domain separator in the metadata would allow clients to perform consistency checks (as the triple contract address, domain separator, shielded allows to calculate token type) and thus - verify if token is related to a contract, this might be useful in a situation, where contract asks for some tokens to perform an operation, it would be highly suspicious if it also asks for e.g. some high-value NFT, so wallets would have a tool available to grade transaction risks depending on tokens involved in a transaction.

### Should the domain separator be token name/ticker?

No. That would allow to verify token type against contract address, on the other hand though domain separator is an identifier, which should be stable in code, and the same domain separator used across multiple contracts could result with tokens with different names in the metadata.

### Should signature include information about algorithm used to sign and hash message? How should such metadata look like?

TBD. Having upgradeability in mind - should this information be encoded and how? Should it be left for later and tackled as a dedicated effort? Is there an existing standard that would define identifiers of algorithms we would like to use or are likely to use?

### Should fungible and non-fungible tokens be differentiated? 

No. It is already being observed with various token types, e.g. on Solana or Ethereum, that there are assets, which are not clearly fungible or non-fungible, and it is their usage/contract that tells about what they are. For that reason it would make sense to not distinguish token's fungibility in any way in the basic metadata, but instead accomodate both cases in the common metadata and define clear extension points if very specific types arise in the future.

No indication of fungibility also makes it easier to accommodate varying shapes of tokens across ecosystems. 

### This API focuses on metadata, should it be re-defined to allow possibility of attaching metadata to other kinds of objects?

No. This API defines token metadata only. Though server of the metadata may provide separate endpoints to provide APIs specific to other kinds of data.

### Why not signing metadata entries independently, like CIP-26 describes

In many cases, metadata are considered a single entity, thus it makes it easier to sign whole entity.

### "domain_separator" is an unintuitive term to people not knowing it. Is there a better name, which could be used across the code, APIs and documentation?

TBD.
