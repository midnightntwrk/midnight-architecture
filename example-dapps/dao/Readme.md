# DAO DApp

This document defines the target architecture of the DAO example DApp. It takes into account actual state and capabilities of various components of Midnight as of time of writing and thus - some details will need to updated as Midnight development progresses.

## Purpose of the DApp

DAO is a natural extension to the e-voting use-case. Not only it still requires the separation between private and public state of a contract to maintain privacy, but also it requires support of native tokens from a contract in order to offer functionality of funding a proposal. 

## State, roles, actions and phases

There are 3 roles defined in the DApp:
  - organizer, who can set voting token price, initialize proposal and advance voting to next stage
  - beneficiary, who can collect tokens in case of voting result being in favor of a proposal 
  - voter, who can vote after buying voting tokens

When contract is deployed, deploying party sets organizer's public key in the public state of a contract, at the same time, voting token price is being set.
Organizer initializes a proposal by setting its topic and beneficiary address. After proposal initialization it is automatically advanced to "commit" phase - that is one, where eligible voters can commit to their votes (without revealing them). Then, at organizer's will, proposal advances to a "reveal" phase - votes are being revealed (by each voter separately) and counted at the same time. When organizer decides, they advance contract to "final" phase - voting result become known and finalized. If it is in favor of a proposal, beneficiary can withdraw tokens, causing contract to move to initial stage, where no proposal is active, otherwise organizer can advance contract back at the initial stage, keeping tokens in the contract's treasury.

A Midnight user can become a voter at any time by buying DAO voting tokens. Though voter can only cast a vote in the first observed "commit" phase of a proposal.

### State diagrams

What is described above, in more detail is presented in diagrams below

#### Public (ledger) state

Public (on-chain, ledger) state of the contract consists of data that is used for synchronization purposes, as well as to limit certain actions only to parties, which can prove that are eligible to execute them (e.g. only organizer can advance state)

![Public State](./public-state.svg)

#### Private state 

Private state (is present only on user's machine) consists of 3 independent components, each of them enables certain set of actions.

![Private State](./private-state.svg)

#### Combined (dApp) state

When combined, from DApp instance perspective (where both private and public state are accessible), we get following state machine. Please note that:
  - the combined state is closer in its structure to private state
  - each of combined states can be derived from public and private state deterministically

![Combined State](./combined-state.svg)

## Components

Component diagram of the dapp and its neighbours needed to run it. 
Supporting components, like Wallet, Midnight.JS, etc. are present on this diagram mostly for completeness, and some details are omitted to keep the diagram readable.

![Components](./components.svg)

### DAO State and its API

It implements the combined state machine as presented above basing on data from contract instance. 

The Dao State API exists to offer flexibility during development and make it easier to migrate into a target architecture, which does not require a dapp-specific server to be run.

### Wallet

Implementation of [Browser Extension Wallet](../../components/WalletBrowserExtension/README.md)

### Ledger Libs

This is the component that implements the ledger logic and related counterparts, which need to be following the same rules:
  - wallet (for being able to create transaction that ledger accepts)
  - Midnight.js (for being able to generate contract call metadata and proofs that ledger accepts)

  Ledger Libs are being implemented in Rust language, but expose a TypeScript interface that can be used in Node.js and browsers through targeting WASM.

## Deployment

Diagram below shows in more detail, where different components are being actually run:

![DApp Instance](./dapp-instance-deployment.svg)

## Important decisions made / shortcuts taken / known issues

### Who and when calls zkir to generate prover and verifier keys?

It's abcird compiler, prover and verifier keys are part of compiler output.

### Minting start tokens

There's a flag in ledger code which allows non-balanced transactions to be accepted. 

This allows to configure substrate's genesis block to include a lot of tokens pre-minted for specific wallet, which later can be used as a faucet (automated or not).

### No voting token balance available to the DApp

DApp usability is affected by not having access to user's Voting Token balance. This is a result of a decision made earlier, that DApps should not have a way to know user's balances to protect privacy. This means that DApp does not have a way to check its own voting token balance before voting.

