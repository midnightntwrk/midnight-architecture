# Midnight, The Cardano Side-Chain
The Midnight PoS blockchain platform will be implemented as a side-chain of the Cardano blockchain platform. The Side-Chain Bridge between Cardano and Midnight consist of serveral components which require orchestration to allow PoS validator election and cross-chain transactions. Some of these components are implemented outside of the Midnight project or in cooperation with the Midnight team.

## Components
### Cardano node
Standard node running the corresponding Cardano Network. No special changes need to be introduced into the node besides the configuration of the node itself. Data will be pulled from the node and processed by the bridge when observing transactions.

### Chain Follower
The Chain Follower reads transactions (and it's metadata if necessary). So the Bridge can observe and process relevant transactions for the side-chain. It provides a query interface to access the main chain state (ledger).

### Bridge
This component is in charge of processing and storing the observed transaction to let the side chain node perform queries on them.
Incoming transactions will be processed in a way that they will be enhanced with contextual information that will help the consumer (SC node) to understand the action to perform. This data can be used to determine consensus rules.

> The term "Bridge" is ambiguous or overloaded. It can relate to the passive part where events are observed (via the Chain Follower) on the Main-Chain. On the other hand, the bridge is also the active part of transmitting transactions (signed with an ATMS) from the Side-Chain to the Main-Chain.

### Side-Chain Node
The Side-Chain Node retrieves information from the Bridge component and acts accordingly in order to

1. determine the current block producer committee,
2. include cross-chain transactions, and
3. validate cross-chain transactions included by other Side-Chain Nodes.

On the other hand, the Node initiates periodically the process of signing and transmitting batches of cross-chain transactions to the Main-Chain.

## Assumptios

- All the nodes running the side-chain (validators and block producers) will also run the bridge (which includes a Cardano node).

- Cross network communication will be executed by the same members that are running the side-chain.

- Side-chain block producers are an honest majority.

- Tokens will be minted on the side-chain and used to incentivize block producers. They can be moved to the main-chain by locking them on the network where they were originally minted.

- Side-chain consensus algorithm (including block producers' election)  depends on each side-chain implementation. That being said, side-chains will run based on the premise that the block generation is linked to the main-chain block producers therefore their identity needs to be proven.

- There will be an ATMS scheme that can be validated in Plutus.


## Technical considerations

### Main-Chain Follower
Between the different alternatives to implement the Main-Chain Follower, db-sync is proposed due to:
- Several production ready tools are using it like cardano-graphql, cardano-rosetta being used to support ADA on major exchanges.
- It's easy to extract information from it.
- It's constantly evolving and it’s going to be subject to a major refactor in the upcoming months.
- There is no other known alternative that's better in the before mentioned items either because they are not production ready or because they need to be coded (for example an Ogmios based one).


### Side-Chain Validator Election
[TBD]

### Cross-Chain transactions

The current approach assumes that Side-Chain tokes originate from the Side-Chain. So in the initial setup all of the tokens are on the Side-Chain and there are none on the Main-Chain. Tokens sent to the Main-Chain are getting locked on the Side-Chain, and tokens sent from the Main-Chain are getting unlocked on the Side-Chain. On the other hand, token sent to the Side-Chain are getting burned on the Main-Chain, and tokens sent from the Side-Chain are getting minted on the Main-Chain.

#### Main-Chain to Side-Chain

Each Side-Chain Node can observe cross-chain transactions on the Main-Chain by querying its local Bridge component. All cross-chain transaction need to be eventually added to the blockchain. Block Producers on the Side-Chain need to be incentivized to add these transactions.

> Jon: There is no actual assurance that a finalized burn on the MC will become finalized on the SC.  SPO’s are vaguely incented to propose the corresponding transactions (via the bridge), but nobody is incented to ensure the tx isn’t lost in some way.

#### Side-Chain to Main-Chain

Close to the end of each Side-Chain epoch all pending cross-chain tranactions are gathered and put into a Merkle Tree. The root hash of this Merkle Tree must be signed by the majority of all registered block producers in the same epoch. This ATMS certificate, once posted to a Plutus contract on the Main-Chain, acts as a basis to mint later tokes for reciepients. Each receipient must claim his token transfered from the Side-Chain.

> Jon: ATMS checkpointing depends on committee members being willing to spend real money, in the form of Ada paid to run the Plutus contract, to perform a responsibility for which they are compensated only in the perhaps-less-valuable sidechain token.  We might have to either (a) expect some checkpoints won’t happen or (b) subsidize the Plutus contract by loading it with sufficient funds to refund some or all of those fees (for how long?).  Neither seems like a very happy place.

> Sebastian: A solution could be a combination of posting the ATMS and claiming tokens. Each claim would include the full SC Certificate and Merkle proof for the specific claim. As an optimization, the Plutus contract could validate the entire ATMS only once, on the first claim and cache the result. However, I assume this solution would result in higher claim Tx fees. At least for the first receiver.

> Sebastian: One more thing. The Plutus contract needs to know the current committee hash (their public keys) to validate the ATMS for an epoch. AFAIK the Plutus contract maintains an NFT with the current verification key. So the old NFT gets burned whenever the committee changes, and a new NFT is minted. But it’s unclear to me which party is paying the fees for this update.
> Consequently, the ATMS for the current epoch must be posted and validated before the committee for the next epoch gets updated. One possible solution to this problem is to merge the two contract calls into one. I think the Mamba side-chain team (via MLabs) is considering this solution. That way, the fees for posting the ATMS would be part of the committee rollover procedure.

> Jon: Update just now from @andrew.sutherland
> about availability of the elliptical curve primitives needed for ATMS in Plutus contracts:  October hard fork.  (Which may or may not be October.).  Incidentally, Mithril probably has the same dependency.  So some of the “correct” implementations of these technologies are delayed by that.

## References
- [Side-Chain Miro board](https://miro.com/app/board/uXjVOvxAMd4=/)
- [PoS Sidechains - Technical Specification](https://docs.google.com/document/d/1UJs4ews1wnKIv4RMyPjFtJcyniyRHi7GmU2JPdUfbQk)

