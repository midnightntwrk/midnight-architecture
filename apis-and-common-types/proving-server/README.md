# Proving server

The proving server is a HTTP REST service, running on port 6300 by
default. It primarily provides means to turn transactions into using zero-knowledge proofs.

__Status__: Draft

__Version__: 0.1

## API descriptions

Interaction with the proving server occurs through the primary endpoint
`/prove-tx`. This accepts POST requests, with a body consisting of a
binary blob describing the unproven transaction (see [the Format
Description Section](#format-description), and the response consists of a binary blob describing the _proven_ transaction.

## Format Description

This document *will not* detail the format of transactions in-depth, as
this will change with the transaction format. It will assume that
*transactions*, *proving keys*, *verifying keys*, and *zk IR source* have
an established binary format. For *transactions*, it is assumed this is a
[Borsh](https://borsh.io) format, for the rest, it is assumed this is a
byte string, serialized as a Borsh dynamic-size byte array.

The request blob consists of a concatenation of:
* A Borsh serialized `UnprovenTransaction`
* A Borsh serialized map mapping key identifiers used in the unproven
  transaction to a tuple of proving key, verifying key, and zk IR source.
