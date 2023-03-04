# Wallet backend - indexer gap analysis

## Context 

As this document is being written, there is ongoing discussion & design of a PubSub 
Indexer - component for sharing messages and indexing data. Some expected use-cases 
for such component in the most general version are:
  - Midnight DApp state synchronization/fetching
  - Block explorers for various chains
  - Letting end-users know about important events in dapps they use
  - Broadcast important messages regarding Catalyst funds
  - Let Atala Prism parties synchronize and be notified wrt issuing credentials

Assumed indexer characterstics as for starting point (looking at
[Catalyst Athena](https://input-output-hk.github.io/catalyst-core-neo/athena-design/03_athena/00.html#athena-cardano-overlay-network-node)
and 
[Catalyst Hermes](https://input-output-hk.github.io/catalyst-core-neo/athena-design/02_hermes/00.html)
) are:
  - anyone can technically run own instance for own purposes (contributing to 
    "indexer network" or not - remain open)
  - little concerns about privacy - most (if not all) of the data indexed is public
  - trust to data served is rooted at either ability to independent verification or 
    form of cryptographic proof (depending on data type and source)
  - 

It is observed that wallet backend has a similar responsibilities to an indexer, and 
thus could even be called "wallet indexer". It is unknown though, what kind of 
requirements or constraints on the indexer this approach brings.

## Desired state

Wallet backend is a form of a filter in the Pubsub Indexer, which:
  - receives a viewing key (or other form of a cryptographic key) as a user input, 
    that key is a private data in a way, that it allows to at least identify 
    transactions related to it
  - consumes events/messages related to all transactions on the Midnight chain 
    (specifically: inputs and outputs) and tries to decrypt them in order to learn 
    which ones are related to received key
  - returns list of transactions matching the key upon authenticated session, list of 
    matching transactions is a private data, which leads to possibility of linking 
    behavior of specific wallet of group of them

Ideally all operations are conducted in a trustless and privacy-preserving way to the 
extent that end-users do not have to run their own infrastructure in order to maintain 
privacy.

## Details

### Trust & Privacy

Athena & Hermes provide quite strong trust baseline by:
  - cross validating data from each connected Cardano node, which even allows for using public Cardano nodes
  - (initially )requiring IOG to be the custodian of the data served in Athena network 
    and sign them; Outlined path to a more decentralized solution is (rolling) 
    committee of custodians who should sign data processed in the network

In that setting the only concern for privacy left on the Athena is networking, 
which can be provided by using i2p networking stack (or parts of it).

The trust model of Atena+Hermes seems to be reasonable and applicable to Midnight at 
least for cases of serving Dapps data or indexing the blockchain. Midnight Wallet has 
bigger requirements though both areas of trust and privacy:
1. The viewing key itself cannot be freely disseminated over the network, unless rest 
   of the wallet protocol allows for that / takes that into account
2. Node, which receives the viewing key and processes transaction data, should be trusted 
   to operate in a way that preserves privacy, either by design (preferable option, e.g. 
   TEEs, cryptography) or by trust in its operator 
3. List of matching transactions can be disseminated over the network only if it is 
   done in a way that preserves privacy (e.g. encrypted)

### Operating costs

Hermes+Athena operating costs seem to lie mostly in storage. A pressure to be able to 
process significant amount of data in a short time appears when voting phase of a fund 
starts.

Midnight Wallet adds a significant processing overhead - for each wallet every 
transaction needs to be processed independently. Additionally, when a new wallet is 
started - it needs to process all historic transactions too. 

### Incentives

Hermes+Athena's incentive to run nodes lies in networking privacy. For fund custodians 
it lies in being funded from the treasury.

For Midnight Wallet one possibility is to collect processing fees (similarily to what 
MyMonero does). 

__TODO: consult tokenomics documentation__

### Data integrity

Hermes can promise data integrity by cross validation.
Athena deliver data integrity by making it relatively easy to independently verify the 
data and by trust in the custodian.

In case of Midnight Wallet, a form of cryptographic proof would be required that all 
transactions were processed and that all related transactions were listed. At the very 
least it should make it possible to verify that information independently to 
disincentive dishonest parties.

### Installing wallet filter

It would need to be an interactive process of:
1. Discovering nodes, which meet desired criteria (like capacity to run wallet, fee 
   level, owned by specific party, co-location)
2. Connection negotiation - to make sure found node will accept the filter to be 
   installed 
3. Keys Exchange - node receives the viewing key, responds with a key that allows 
   further discovery/decryption of processed transactions

Peer-to-peer nature of Athena seems to support this style of communication by design. 
Functionalities like DHT or PubSub seem to be complementary to ease receiving 
processed data or node discovery after client restart (e.g. reducing amount of data 
needed to stored by client). 

### Uninstalling wallet filter



### Selecting instance to connect

### Switching instance

### Service restarts
