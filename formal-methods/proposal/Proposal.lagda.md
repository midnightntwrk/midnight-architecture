---
monofont: DejaVuSansMono
title: Proposal - Formalizing the Compact Language
subtitle: (and beyond)
author:
  - Cas van der Rest
date:
  - August 14, 2024
output: pdf_document
bibliography: references.bib
---

# Preface {-}



# Motivation and Goals 

How could formal methods benefit the user (i.e., DApp developer)? Since smart
contracts may potentially large funds, it is crucial that they behave as
intended and cannot be tampered with. 

## Correctness of Smart Contracts

First of all, we have to identify what kind of undesirable behaviour can be
exhibited by smart contracts. We characterize three classes of properties of
smart contracts

### Functional Properties {-} 

_Functional properties_ specify a contract's intended behaviour, and can be used
to assert that a contract's implementation conforms to its own
specification. For example, for a contract that conducts an auction we might
want to prove properties such as:

* the asset is transferred to the highest bidder, 
* for all bidders except the winner, a number of tokens equal to their bid is transferred back to them after the auction, or
* a number of tokens equal to the highest bid is transferred to the seller. 


### Security Properties {-}

_Security properties_ refer to properties that establish the absence of the
possibility for certain exploits, such as reentry vulnerabilities that made the
infamous hack of the \textsf{TheDAO} [@TheDAO23] contract possible causing a
hard fork of the Ethereum blockchain. In general, security properties establish
the absence of certain patterns in a contract's execution that, while permitted
by the programming model, are considered to be undesirable.

There is some overlap between functional and security properties, in the sense
that functional properties might imply security properties. That is, if
functional properties are established that assert that funds are transferred in
the right way by a contract, it is also implied that the contract is secure in
some sense: if we have proved that all funds that the contract deals with are
transferred to the right place, funds cannot be transferred to an adversary by
exploiting a security vulnerability. We must qualify this statement, however,
since it only applies to vulnerabilities modelled by the contract's semantics. 




Programming model permits certain exploits, such as reentry vulnerabilities

For example, @Bhargavan16 does blah

Reentry vulnerabilities such as occured when \textsf{TheDAO} [@TheDAO23] was hacked. 

@Mavridou18 remark "In practice, these vulnerabilities often arise due to the
semantic gap between the assumptions contract writers make about the underlying
execution semantics and the actual semantics of smart contracts" 

@Luu16 "... these flaws arise in practice because of a semantic gap between the assump-
tions contract writers make about the underlying execution semantics and the
actual semantics of the smart contract system."

### Privacy Properties {-} 




This is a proposal.

* Ledger
* Impact VM
* ZK
* Compiler

## Trusting the System 

* Ledger
* Compiler
* ...? 

## Who Verifies?

* Us, by providing an ecosystem/libraries of smart contracts with verified
  correctness guarantees.
* The users, if they are knowledgeable about FM, or they could hire someone to
  verify their SCs. 



# Formal Methods



<!--
```agda
module Proposal where 
```
-->



```agda
f : ∀ {A : Set} → A → A
f x = x 
```


# References 
