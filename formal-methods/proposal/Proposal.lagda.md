---
monofont: DejaVuSansMono
title: "Proposal: Formal Methods for Midnight"
author:
  - Cas van der Rest
date:
  - August 28, 2024
output: pdf_document
bibliography: references.bib
fontfamily: merriweather
geometry: margin=4.5cm
header-includes:
  \usepackage{setspace}
  \renewcommand{\baselinestretch}{1.25}
  \usepackage[usenames,dvipsnames]{xcolor}
---


\newcommand{\Q}[1]{{\color{BrickRed}\textbf{(Q)}\hspace{1em}#1}}

# Preface {-}

This document sketches a proposal for applying formal methods in the Midnight
project. We start (in Section 1) by considering the user's perspective and what
kind of guarantees they might want to establish about the contracts they develop
or entrust with their funds. Then (in Sections 2 and 3), we discuss what could
be potential deliverables to convince potential users that Midnight is
trustworthy and secure, and what could be the first immediate steps to get there. 

If you do not feel like reading the entire document, but would like to be
involved with formal methods, consider skipping ahead to Section ??, which
documents considerations and open questions for deciding next steps.

Points that I would like feedback/input on are explicitly marked in
red: 

\Q{This is a question I'm asking to you, the reader.}

# Motivation and Goals 

Users entrust Midnight with their money and private data, hence it is crucial
that they can count on the system to not "misplace" any tokens, or leak private
information to the public in ways that are not disclosed beforehand. This
applies both to smart contracts developed by other users, as well as the
infrastructure developed by us. By using formal methods, we can guarantee the
absence of certain problems with a high degree of certainty, giving users the
confidence that their funds and data are in safe hands.

## Correctness of Smart Contracts

Smart contracts may handle funds or sensitive data, so their correctness is
paramount. But what does it actually mean for a smart contract to be correct?
We identify three kinds of undesirable behaviour can be exhibited by smart
contracts.

* _Functional properties_, which reason about the correctness of a contract's
 functionality. For example, an auction contract should transfer the sold asset
 to the highest bidder after the auction is concluded.

* _Security properties_, which reason about a contract's security. In general,
security properties establish the absence of certain patterns in a contract's
execution that, while permitted by the programming model, are considered to be
undesirable. For example, re-entry attacks such as used in the infamous hack of
the \textsf{TheDAO} contract [@TheDAO23].

* _Privacy properties_, which reason about what parts of the private state are
  "leaked" to the public when a circuit is called. For example, purchasing an
  asset should not require us to reveal our account's balance to the rest of the
  world.

\Q{Are there other aspects to a smart contract that a user might care about?}

## Trusting Midnight's Infrastructure  

All the above three classes of properties concern mistakes made by the _contract
developer_. That is, they cover problems that arise because of the so-called
_semantic gap_ [@Luu16]: developers may have a wrong or incomplete understanding
of a contract's semantics, which could lead to exploitable mistakes.

Another potential point of failure is the underlying infrastructure, which
encodes the semantics of smart contracts in several places. In these places, a
different kind of semantic gap may occur, where the _implementated semantics_ is
different from the _intended semantics_. For example, 

* the _compiler_ may emit a public transcript with a different semantics than
  the source program,

* the _compiler_ may emit a zk circuit that encodes a different semantics than
  the source program,

* the _Impact VM_ could interpret instructions in a way that differs from their
  intended semantics, or 

* the _implementation of the ledger_ could contain mistakes such that it
  e.g. violates preservation of funds.  

Beyond this, there are other parts of Midnight (such as the wallet, indexer, or
proof server) where programming mistakes could theoretically be exploited by an
adversary to extract funds or data in ways they should not be able to.

\Q{Can we identify other potential points of failure?}

\Q{Can we say something about the relative probability that any of these will
cause a problem?}

# Formal Methods for Midnight

We identify the following ways inf which formal methods, and PL techniques in a
broader sense, could be applied within Midnight to safeguard against exploitable
mistakes:

* Formal specifications
* Language design
* Proofs of meta-theoretical properties
* Verification tools for end-users
* Conformance testing againts reference implementations
* Deriving implementations from specifications
* Static analysis
* Run-time analysis

While this is by no means an exhaustive list, it should give a pretty good feel
for the wealth of different possible approaches to formal methods that could be
applied within Midnight. Which approach makes the most sense will depend on
which part of Midnight it is applied to, but more so on what we would like to
achieve by applying formal methods. 

We will discuss each of the items in the list above in more detail in the
remainder of this section. But first we must add a disclaimer: **the current
amount of resources available for formal methods is entirely insufficient to
cover all potential ideas/projects outlined in this document**. As a result
there are choices to be made when it comes to choosing where to expend the
resources that are available.

\Q{What parts of Midnight would benefit the most from formal verification?}

## Formal Specifications

Writing a formal specification forces us to be crystal clear about how something
is _supposed to work_. If a design is under-specified, ad-hoc, or even
fundamentally flawed in some way, this is likely to present itself already when
writing a formal specification. Furthermore, for many other formal methods,
having a formal specification is a necessary prerequisite. There are several
parts of Midnight's infrastructure that we could produce a specification for.

* Compact
  * Static semantics
  * Operational semantics
  * Denotational semantics 
  * Compiler 

* ZK
  * ZKIR/Circuits
  * Proof server

* Impact
  * Impact VM

* Ledger
  * Token model
  * Consensus algorithm

These specifications can serve to communicate the intended behavior of parts of
Midnights infrastructure, both internally and externally, or provide the
foundation to support formal reasoning about and/or testing of their
correctness.

\Q{What are other parts of Midnight could benefit from a formal specification?}

## Language Design 

* Type system

11 17 22 36

Michael Backes, Hritcu Catalin, and Matteo Maffei. 2014. Union, Intersection
and Refinement Types and Reasoning About Type Disjointness for Secure Protocol
Implementations

Jesper Bengtson, Karthikeyan Bhargavan, Cédric Fournet, Andrew D. Gordon,
and Sergio Maffeis. 2011. Refinement Types for Secure Implementations.

Affine Refinement Types for Secure Distributed Programming

Types for Security Protocols


Turing completeness: tension between expressivity and safety/determinism. A cost
model ought to protect against DoS attacks. But, from a usability perspective,
costs should be as low as possible.

Current state of compact: cost should be deterministic if we know the contract's
input. But what about non-terminating witnesses? Calling a witness is 0 cost (it
won't show up in the transcript), so for the purpose of the cost model we can
ignore it and rather treat them as coroutines.




## Proofs of Meta-Theoretical Properties

_Proving meta-properties_ about our specification (e.g., preservation of funds
   or soundness properties) establishes with a high degree of certainty that a
   design is absent of certain flaws.

* Preservation of funds
* Soundness
* Privacy properties

\Q{What are other properties of (parts of) Midnight that we might care about?}

## Verification Tools for Users

Having a formal specification provides a necessary foundation for the
   development of IDE support or SMT based verification tools that help users
   identify mistakes in their contracts or verify that they behave as intended.

## Conformance Testing  

## Analysis

# Roadmap

## Why is Formal methods 


<!--
```agda
module Proposal where 
```
-->



```agda
f : ∀ {A : Set} → A → A
f x = x 
```

# What's Next?



# References 

