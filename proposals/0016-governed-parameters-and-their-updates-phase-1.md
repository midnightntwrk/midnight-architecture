# Proposal 0016: Governed Parameters and Their Update Mechanics: Phase 1

## Problem Statement

Phase 1 of Midnight's governance involves running actual governance on Cardano (because it is where NIGHT lives). It raises a couple of issues:
- What are the parameters to be managed by the governance system? Should all ledger parameters be updateable this way?
- How to perform their update for Midnight node and Midnight ledger once the governance action succeeds on Cardano?
- Does Substrate allow to have selected parameters dynamically updateable at all?
- What (if any) changes are needed in the Main Chain Follower? How to use the same tooling as partner chains code uses without making their code Midnight-specific (so that e.g. a migration from db-sync does not require Midnight to do significant changes in our code)?

## Proposed Changes

Following parameters are proposed to be managed under governance:
- maximum block length - to allow tuning it based on consensus benchmarks or network activity; Various personas might be interested in adjusting it in relationship to observed usage patterns. It directly affects performance and costs of operating a Midnight node.
- maximum block weight - to allow tuning it based on ledger benchmarks or network activity; Various personas might be interested in adjusting it in relationship to observed usage patterns. It directly affects performance and costs of operating a Midnight node. 
- protocol version (together with a hash of the runtime meant to be used) - to manage Midnight protocol updates. It is crucial one to manage, as not only it decouples protocol upgrades from consensus, but also is the means of possibly changing other parameters
- ledger parameters - to allow fine-tune transaction fees based on new benchmarks and network activity. Similarly to block length various personas might be interested in adjusting these and the impact on transaction fees and costs of operating a Midnight node is very big:
  - cost model
  - transaction limits
  - ticket cost factor
- Ariadne parameters - to allow both increase and decrease of decentralization in Midnight consensus, as well as to avoid separate keys to manage consensus. SPOs might be particularly interested in those, and personas looking at Midnight through compliance angle (like DApp Commissioner). Mostly because of the number of chances d-parameter allows, and its impact on system decentralization:
  - permissioned keys
  - d-parameter
  - governance authority

4 mechanics are needed to be in place, to effectively allow managing those parameters:
1. To allow Ariadne parameters being governed by Midnight's governance
2. To observe their changes from Cardano
3. To update them in Midnight based on observed changes
4. To expose cost model to clients (wallets)

### Allowing Ariadne parameters being governed by Midnight's governance

Cardano smart contracts managing Ariadne parameters are modular and flexible with emphasis on those scripts already being prepared to use different flavors of governance. This means, that only a bridge between Midnight governance and the managing scripts needs to be implemented to allow updating Ariadne parameters with Midnight governance. 

### Observing changes from Cardano

It is proposed to be done by turning some internals of the main chain follower into a public API. Namely, - to expose methods to query for utxos owned by an address at specific block height/epoch. Such interface could have shape like below:
```rust
enum Height {
  EpochStart(EpochNumber),
  EpochEnd(EpochNumber),
  Block(BlockNumber)
}


trait MainChainDataSource {
  fn resolve_epoch(&self, reference_timestamp: Timestamp) -> Result<EpochNumber, DataSourceError>; 
  fn resolve_stable_block(&self, reference_timestamp: Timestamp) -> Result<BlockNumber, DataSourceError>;
  fn get_utxos(&self, height: Height, address: Address) -> Result<Vec<Utxo>, DataSourceError>;
}

```

Such interface seems to serve the purpose well:
- it is not a Midnight-specific API
- it is easy to imagine using it for other cases than governance, both in Midnight and outside of Midnight
- it is not a data source-specific API, so it does not bind Midnight code to db-sync

Note - this kind of interface is used internally by main chain follower already to observe current Ariadne parameters (d-parameter, permissioned keys and permissionless candidates). Exposing this kind of API will also require exposing functions to parse datums.

### Updating parameters in Midnight based on observed changes

With the Cardano observability in place, it is possible for Midnight node to observe the desired parameters from Cardano and react to their changes (e.g. by comparing values from end of the last epoch and one before it). This can be done by adding an inherent transaction (the type of Substrate transaction, which can be included by a block authoring node) to update specific parameter.

Nodes need to react to those transactions with verification against data source (to reject blocks trying to execute parameter updates not being result of main chain action) and then performing the change in one of 3 ways:
1. For block length - by saving it into storage, so that it can be read from there
2. For protocol version change - by signalling it can be performed, so that both the voting threshold (see the [ADR](../adrs/0016-forks-change-management.md) and the [Proposal](./0012-forks.md)) and a signal for upgrade coming from governance are required
3. For ledger parameter - by applying relevant ledger transaction. It requires `frame_system::Config::BlockWeight` to be updateable in response to ledger cost model.

### Exposing cost model to clients

The cost model plays a crucial role in wallet properly balancing transactions, for that reason dynamic changes of it require it being delivered to wallet based on on-chain data. This requires node to expose relevant event and indexer to provide query, which can be used by clients.



## Desired Result

Set of governed parameters and all mechanics needed to update them are identified, so that it is possible to ask for feedback and continue with a more detailed design work.

## Additional notes

### Excluded parameters

Following parameters were taken into consideration for being managed under governance, but were rejected:
`MaxAuthorities` - despite being needed internally for configuration, it feels like a parameter, which should be set once to a relatively high, yet safe, value, and not touched until absolutely necessary, in which case in can be done by runtime upgrade/hard-fork; SPOs might want to increase it, but in such case Midnight might be ready to become a fully decentralized and independent network.
`SessionLength` and `SlotsPerEpoch` - aura/Partner chains documentation explicitly mentions they should not be changed on a running network (likely to not mess with calculations between timestamp and session/slot number)

### Parameter dependencies

With a certain degree of simplification, following table presents parameters that should be considered for adjustment, if other parameters are being changed:

<table>
  <thead>
    <tr>
    <th>Related parameters</th>
    <th>Description</th>
</tr>
  </thead>
  <tbody>
    <tr>
      <td>maximum block length</td>
      <td rowspan="5">
        These parameters together affect how many and what kind of transactions can be included in a block. Since block is a transaction execution unit, they affect node performance, cost of operating Midnight infrastructure (node, but also indexers and wallets are affected too). Ticket cost factor is somewhat independent here, but eventually it affects how transaction weight turns into actual fee to be paid, which turns into rewards received by the block author.
      </td>
    </tr>
    <tr>
     <td>maximum block weight</td>
    </tr>
    <tr>
     <td>cost model</td>
    </tr>
    <tr>
     <td>transaction limits</td>
    </tr>
    <tr>
      <td>ticket cost factor</td>
    </tr>
    <tr>
      <td>protocol version</td>
      <td>Protocol version is largely independent parameter on its own. But since it is a parameter, whose change leads to a hard-fork - content of the changes introduced might be related to other parameters.</td>
    </tr>
    <tr>
      <td>permissioned keys</td>
      <td rowspan="2">In many situations permissioned keys and d-parameters can be updated independently, though changes to the set of permissioned keys might require changes to the d-parameter in order to let Ariadne form a healthy committee.</td>
    </tr>
    <tr>
      <td>d-parameter</td>
    </tr>
    <tr>
      <td>Governance authority</td>
      <td>Governance authority on its own is independent of other parameters, though in cases, where its change involve changing they way of governance - other consensus parameters should be revisited too. </td>
    </tr>
  </tbody>
</table>
