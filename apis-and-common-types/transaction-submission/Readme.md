# Transaction submission

[Repo](https://github.com/input-output-hk/midnight-mocked-node)

This protocol allows to submit transactions to the node, so that they eventually can 
be included in the chain. It is heavily inspired by the [Ouroboros Transaction 
Submission protocol](https://github.com/input-output-hk/ouroboros-network/).

## Special Needs

In order to offer good user experience, the protocol offers a reliable error 
information in case of transaction being rejected. This, eventually requires a 
reliable source of information about rejected transactions as in the majority of cases 
block minter is not the same process as the server, which received original transaction 
request.

From client perspective it is a simple request-response API. Though presence of
dedicated error reporting makes it possible to clearly distinguish a transaction which
cannot be included in chain from networking/performance issues in the network.  

## Server

This API is primarily and eventually meant to be implemented by the node. It is easy to 
imagine a load-balancing facade in front of a group of nodes implementing this API in a 
non-distinguishable way. Specifically, at various stages of Midnight development, various 
components are expected to be the default server implementation of this protocol:
  - end-of-2022 - it's the mocked node
  - end-of-2023 testnet - it will be the mempool
  - after testnet - node

## Clients

Most natural client of this API is the Wallet (backend, browser or headless). By 
extension and nature of transactions in Midnight, some DApps are expected to use this 
API too.

Timeout indicates unclear transaction status due to networking/performance issues in 
the network. The transaction may still wait for being included in a block, as well as 
not reach the minting node at all. It is up to client to decide what to do next.

### Data Types

It's 4 of them:
  - transaction to be submitted
  - confirmation of submission - the transaction was received by server and it is added 
    to the local mempool, scheduled to be broadcasted over the network
  - confirmation of inclusion - the transaction is included in block
  - error

## Sequence diagram

![](./sequence.svg)
