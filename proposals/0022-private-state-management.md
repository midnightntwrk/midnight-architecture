# Proposal 0022: Private State Management

## Problem Statement

At the time of writing, the browser environment is the focus to enable Midnight DApps, with mobile
around the corner. The browser as an environment is not equipped though with tools to persist data
onto user's machine in a seamless way. Specifically - there are APIs allowing to use user's files,
but they are only implemented in Chrome. Brave and Firefox consistently reject requests to implement
them based on the concerns for privacy and security. The only API allowing Brave or Firefox to use
files is a regular form input/drag&drop action for reading and a trigger to download file to saving,
which are designed to be controlled by user each time such interaction is needed. Although it may be
perceived as a good-enough workaround - it really leads to a subpar UX to many of potential Midnight
users (given the alignment on privacy and user data protection/ownership).

This, in turn leads to an issue, where simple action of clearing browser's cache leads to user
losing their data, access to their DApps as well as tokens locked in the DApps. Of course, DApp
developers can implement their way of backup&restore functionality, but this can very quickly lead
to scenarios being in contrast to the Midnight's values: users effectively losing ownership of their
data (DApp uploads data to their server), users losing their data entirely (DApp does not implement
any backup&restore functionality), or users being exposed to very unfriendly UX (DApp implements
backup&restore, but in a non-intuitive way).

With issues like this present, there is a need for a platform-wide standarised approach for state
management. Ideally so that:

- DApp developers do not necessarily have to implement the support themselves, or can rely on simple
  integration
- Users have very little setup to do, ideally a one-time action
- Same or very similar mechanics and patterns can be utilized across different modalities:
  - desktop browser
  - desktop native app (Electron or native)
  - mobile browser
  - mobile native app
  - mobile in-wallet browser

## Proposed Changes

Initially introduce a JSON-RPC-based DApp-connector-like API for state management, a standard
client, by-default integration to Midnight.js, with a fallback to an alternative, but persistent
storage option (like filesystem or file downloads). The API can be implemented by host environment.
It can be wallets, password managers (or their integrations), or dedicated extensions. Such approach
covers well the desktop browser, it works for mobile in-wallet browsers, and can work for desktop
native apps or mobile native apps.

As a second stage - enable WalletConnect-like flows, where:

1. an ephemeral secret is shared between wallet and DApp (e.g. by typing short code, scanning QR, or
   something like that)
2. that secret is used to derive ephemeral encryption key and session id
3. a p2p session is established using a well known gateway; the keys used in step 2. are used in
   discovery and connection initialization
4. A form of DApp attestation is needed here.
5. the APIs like the State Management one or DApp Connector are enabled using established p2p
   session

The implementations of the State Management API need to compartmentalize state on a per-domain
basis. While it is far from perfect from a perspective of user wanting to use multiple DApp
frontends for a single set of contracts, or a DApp wanting to call another DApp/contract (e.g. to
attest some facts about user identity), it enables a quick implementation with a proven security
model, as employed by password managers (a website do not have a way to fake their URL in the
browser). In fact - there seem to be many similarities with password managers, and many
functionalities may be similar or the same. Security model trying to operate on a per-contract basis
would introduce many questions which can not be answered without owning the contract execution too.
Like - which is the dapp that really "owns" particular contract? If there is a DApp A and DApp B
using the same contract, do they use compatible witness definitions? What if a malicious DApp claims
ownership of a very-important-contract in the ecosystem? How would the user recognize contract
addresses? A partial solution to that could be leveraging metadata like for tokens, but for
contracts, but first, that would require solving witness compatibility issue.

Such approach also provides a good starting point for experimentations with the contract kernel -
the idea of a one application, which holds contract states, contract implementations, and is able to
execute contracts, including the contract-to-contract calls, while maintaining proper state
boundaries.

### The API

There are multiple concerns a storage API like this needs to address. It is amount of data exchanged
in varius scenarios, the transactionality-related: atomicity, consistency, isolation, durability. An
important factor is also trust assumptions. As of time of writing - Midnight.js does encrypt private
data at rest. If using this state management API - should it continue to do so (limiting API
capabilities, reducing trust assumptions, but requiring _all_ DApps to perform the encryption) or
should it become responsibility of implementors of this API (so data in-memory are mostly
unecrypted, should be encrypted in transit, DApps are freed from encryption burden, but encryption
at rest becomes a concern of the API implementor)

While a minimal API surface of a simple key-value storage would be enough for a proof of concept, it
will not be a solution scalable enough. Eventually complexity and amounts of data will become too
much to use efficiently in this way. It is particularly important for this API to be possibly
future-proof, because backward incompatible changes will be very costly to perform.

Very likely requirements for a production implementation will be (assuming it's API implementor
concern to offer encryption at rest):

- ability to iterate over nested keys, etc. so that after
  `set('foo.bar', 'a'); set('foo.baz', 'b');`, an operation `listKeys('foo')` returns
  `['foo.bar', 'foo.baz']`
- ability to manage storage transactions, so that the private data is not left in an inconsistent
  state if e.g. contract call rehearsal fails
- ability to understand JSON documents, so that `set('foo', {bar: 'baz'});` is equivalent to
  `set('foo.bar', 'baz')`, so `get('foo.bar')` returns string `baz`;

## Desired Result

The risk of DApp users losing data is mitigated, without necessarily leaning on a centralized
service. A minimal to no setup on user's side is required if they decide to use wallet integration,
but particularly cautious users have options for going an extra mile and having their setups
tailored to their needs.
