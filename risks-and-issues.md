# Architectural Issue Tracking

| Name                            | Owner | Priority | Short Status |
|---------------------------------+-------+------------+-------------|
| [Gas for Public Oracles](#gas-for-public-oracles) | | | |
| [Rent for Public State](#rent-for-public-state) | | | |
| [Wallet Backend Fees](#wallet-backend-fees) | | | |
| [Proof Server](#proof-server) | | | |
| [Wallet Backend Privacy](#wallet-backend-privacy) | | | |
| [Private Data Recovery](#private-data-recovery) | | | |
| [Ada / Dust Exchange](#ada-/-dust-exchange) | | | |
| [Network-Layer Security](#network-layer-security) | | | |
| [Choice of Consensus Mechanism](#choice-of-consensus-mechanism) | | | |
| [Is a Sidechain Launch More Secure?](#is-a-sidechain-launch-more-secure) | | | |
| [What Stake Does Midnight Consensus Use?](#what-stake-does-midnight-consensus-use) | | | |
| [Dilution of Security Using Ada SPO's](#dilution-of-security-using-ada-spos) | | | |
| [Slashing Considered Harmful](#slashing-considered-harmful) | | | |
| [Decentralized Settlement](#decentralized-settlement) | | | |
| [Contracts and Dust](#contracts-and-dust) | | | |
| [Who Holds the Ada?](#who-holds-the-ada) | | | |
| [What is the preferred style of query API?](#what-is-the-preferred-style-of-query-api) | | | |
| [Must we go through Cardano query API?](#must-we-go-through-cardano-query-api) | | | |
| [Is Proof of Burn in Scope?](#is-proof-of-burn-in-scope) | | | |
| [Is Glacier Drop in Scope?](#is-glacier-drop-in-scope) | | | |
| [Where Does Trusted Setup Run?](#where-does-trusted-setup-run) | | | |

# Detailed Descriptions

## Incentives Concerns
### Gas for Public Oracles

Is it possible to avoid gas in public oracles?  Gas entails significant implementation effort and tuning for incentives.

Possibilities we have explored involve bounding the time/space complexity of oracle operations, which would entail limiting the expressive power of the language.

An extreme version of restricting the expressive power is to provide only a standard library of (composable) data structures that can be used for public state.  The library could grow through decenralized governance (somehow)  and would be updated in a future hardfork.  Less extreme versions allow user-defined data structures and algorithms that are verified to be, say, log time/space as part of their validity check.  (Think: proof-carrying code.)

### Rent for Public State

Should Midnight launch with a built-in rent model to incentivize frugal use of on-chain state?

### Wallet Backend Fees

Who runs wallet backend severs?  Why?  How are they compensated?  Should there be fees of any kind?  Do we need gas fees to deal with filter expressions? (And what's better, a wide or narrow filter?)  What about the cost of data buffering per client?

## Privacy Concerns

### Proof Server

### Wallet Backend Privacy

### Private Data Recovery

### Ada / Dust Exchange

Is the exchange simply an instance of the Midnight privacy bridge, or are there deeper concerns to examine?


### Network-Layer Security

Where does this fit into the sidechain story?  Does our SPO-facing component use NYM to talk to the mempool?  Do Midnight Nodes use Nym for the mempool and P2P?  Do we insert NYM between Wallet Backend and either the front-end clients or the back-end Midnight network?


## Consensus and Security

### Choice of Consensus Mechanism

* Ouroboros?
* OBFT?
* Other?

### Is a Sidechain Launch More Secure?

A significant part of the rationale for making Midnight a sidechain of Cardano is that it removes the need for Minotaur consensus or some other mechanism to secure the launch.  Does this hold up to scrutiny?  Does it require any special conditions or extra mechanisms or incentives?

### What Stake Does Midnight Consensus Use?

The two options are Ada and Dust.

Mamba is using the Cardano's Ada ledger as the stake oracle for its OBFT implementation.  It seems like Midnight should do the same because it's the obvious trust anchor for launch.  If we use Dust instead, we are back to handling two problems we were hoping to avoid in accelerating Midnight:

1. Complex, multi-phase launch to slowly achieve safe PoS as more stake accrues.
2. The need to research, design, and implement private stakepools.  (And the need to create a user interface SPO's and another for Dust-holder stakepool assignment.)

A hybrid options might be the best choice:

1. Launch with Ada stake.
2. At a predetermined threshold of Dust stake or stake diversity, switch to Dust.  (Assuming that by then we have built the necessary user experiences as well.)

### Dilution of Security Using Ada SPO's

(A question of incentives?)

If Midnight relies on Ada stake to secure its mining pool, that means Midnight miners are a subset of Ada miners.  It seems that the security we gain from this arrangement relies on a significant part of the stake of Ada being "used" to secure Midnight, but this would require a significant portion of the largest SPO's to agree to participate.  

What does SPO participation require?  Does it require running a Node and actually verifying transactions, or is it simpler matter of voting in a BFT quorum to establish a strict orderging independent of the validity of the ordered transactions?

Is all of this an argument that [Sidechain Launch](#is-a-sidechain-launch-more-secure) is not inherently more secure, and/or that using Dust for stake is a better choice?

### Slashing Considered Harmful

Depending on our choice of consensus mechanism, might there be antagonistic behaviors that an SPO might practive on the sidechain without repercussions on the main chain?  If so, how does their SPO stake really "secure" their good behavior?  Can we avoid a slashing mechanism?  From a broader incentives standpoint, it would seem we *must avoid* slashing because of its potential to discourage honest SPO's from participating due to risk of ill-founded Ada slashing.  So what does that tell us about the consensus and incentives model on the sidechain?

## Sidechain Integration

### Decentralized Settlement

Which approach will Midnight use to allow sidechains to agree on the version of truth that they checkpoint to the main chain (the settlement layer)?

## Ledger Interaction

Discussion of interactions amont the key ledgers:

1. Ada
2. Dust
3. Lares smart contracts

### Contracts and Dust

How exactly does a Lares contract receive/hold/spend Dust?  What specific concerns will users hava about liquidity (e.g., liquidity should not rely on any external party to provide a spending key).

### Who Holds the Ada?

Who holds the ADA's when they become Dust?  Burn? (Presumably we don't want to burn Ada.). 

Is it all just held by the exchange contract?  One fat honeypot Plutus contract?

## Query API

### What is the preferred style of query API?

### Must we go through Cardano query API?

If Midnight nodes use the Cardano stack, does that include the query API?  Do wallets inquire about Dust using the same API's they'd use on the main chain to inquire about Ada?  If not, how strange a perversion of normal Cardano flows does this require?  How much hidden work?

## Launch

### Is Proof of Burn in Scope?

There is an early implementation, but it requires a major update.  We have considerable material about the update and it's a non-trivial amount of work.  Moreover, would we continue with a Solidity implementation and run on Mamba, or should we code it in Plutus?

### Is Glacier Drop in Scope?

We probably want something very much like the existing design of Glacier drop, but how much of that drop's design was predicated on factors that are now changing?  We need to perform a thorough review.

If we do implement something like this, should it be in Solidity on Mamba or in Plutus on the main chain?

### Where Does Trusted Setup Run?

Plutus on the main chain?


