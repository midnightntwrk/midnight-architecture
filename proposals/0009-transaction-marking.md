# Proposal 0009: Cryptographic transaction markers
This is a template for writing new Midnight Architecture Proposals.  We want
this template to be lightweight, so that it does not impede the process of
capturing the proposals, and we to evolve this template over the time, as we
figure out the process of proposing changes to our architecture.

# Context & Problem Statement

ZSwap, similarily to other Cryptonote-based protocols, essentially requires wallet software 
to process every single transaction on chain:
  - to learn about nullifiers of spent coins
  - to try decrypt transaction outputs in order to learn about new coins

This process requires significant amount of resources (network, compute, time), 
to the extent the user experience suffers a lot and thus - makes it almost prohibitive to use wallet for more casual users or in more casual situations, like:
  - opening wallet just for purchase of some gorceries online
  - when paying in a cafe
  - just opening wallet to perform action in a DApp, like making a move in an online game

Because of this - we want to offload this expensive synchronization and computation to a specialized online service, which receives some cryptographic material, performs indexing for user and serves amount of data necessary for non-interactive client operations. This service is called wallet backend in this repository at the time of writing, but in upcoming updates it is known to become part of PubSub Indexer service.

Assuming such service to be the default way of running a Midnight wallet, we need:
  - that it keeps indexed wallets privacy as much as possible, by design - preventing malicious implementations or malicious service operators from learning encrypted details about coins owned by wallets being indexed. All with assumption that linkability is inherently present when using such service
  - not use TEEs if only possible
  - reduce computational overhead if possible

# Proposed Changes

For each address _A_, there is related encrypting marking key (_A_emk_) and decrypting marking key (_A_dmk_), such that:

  - _A_emk_ can be derived directly from address and is considered public
  - _A_dmk_ can be derived for address using private component, does not allow calculating address _A_ it is generated for, and is considered semi-private, as this is the key that would be shared with the PubSub Indexer.

Then, a transaction would be adjusted to require that if there is any output created for an address, the transaction has to contain a marker encrypted with related _A_emk_ in a way, that prevents known ciphertext attacks.

Such scheme seems to:
  - keep privacy in the context of PubSub Indexer as coin ciphertexts are not decrypted at all
  - impose an overhead on transaction size though to be of size ~64-100bytes per marker
  - be (significantly?) less computationally expensive than trying to decrypt every single output

# Desired Result

Short-term result is to identify how feasible, secure and privacy preserving such scheme is as well as discuss possible alternatives. Specifically in context of affecting coin structure and ZSwap security argument.
Mid- to long-term is a complete specification, argument and implementation, which allows services like PubSub Indexer index wallet data without compromising privacy.

# Open questions

1. What are specific algorithms that could be used here? How common or related to other algorithms used in ZSwap they are?
2. If and how does it affect coin structure or spending circuits? How does it affect security argument of ZSwap?
3. What are alternative cryptographic techniques to achieve similar result? How common they are (minding feasibility/easiness of implementation)?
4. Does this reduce trust enough so that decentralized PubSub Indexer, with less control on choose of service operator, becomes a thing that may be reachable if there exists a way to prove data integrity, completeness and consistency with chain?
5. How big of a risk is potential malicious actor collecting all _emk_ he can? Would user need to migrate to use different address when in doubt? What could be ways to prevent that? Some form of key rotation that invalidates key every "epoch"? How would that affect complexity of whole scheme (and user experience)?