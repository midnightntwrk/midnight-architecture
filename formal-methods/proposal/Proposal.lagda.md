---
monofont: DejaVuSansMono
title: "Formal Methods for Midnight"
author:
  - Cas van der Rest
date:
  - September 9, 2024
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

Midnight's users will entrust the platform with their money and sensitive data,
so it is important that they trust it to be in good hands. Formal methods can
help to foster this trust, by guaranteeing, with a high degree of certainty, the
absence of certain problems. This document outlines possibilities for applying
formal methods in the Midnight project. It aims to answer three core questions:

1. What are the places that problems can arise? 

2. How can we use formal methods to mitigate these risks? 

3. What are potential deliverables that could help to create more trust in
   Midnight?
   
The main purpose of this document is to convey my own understanding of the
design space, to clarify any misconceptions that I might have about the project,
it's goals and stakeholders, or underlying technology, and to map out a more
concrete direction for the application of formal methods in Midnight. Please do
point out if you think I am mistaken about something, your input is vital.

If you cannot make the time to read the whole document but would still like to
give some input, I have marked some items that I would like feedback on in red,
like so:

\Q{Questions are marked in red.}

\newpage
# Motivation and Goals 

Mistakes in smart contracts, or the infrastructure on which they are deployed,
can be exploited by adversaries to extract funds or sensitive data. Formal
methods can, with a high degree of certainty, establish that certain problems
cannot occur. By using formal methods, we may help Midnight's users trust that
their funds and sensitive data is in good hands when they interact with smart
contracts that are deployed on Midnight's network.

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

\Q{Are there other aspects of a smart contract's execution that a user might
care about?}

## Trusting Midnight's Infrastructure

All the above three classes of properties concern mistakes made by the _contract
developer_. That is, they cover problems that arise because of a so-called
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

\Q{Is this list complete?}

\Q{In order to determine priorities, can we say something about the relative
probability that any of these will cause a problem?}

\newpage
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

This list is not intended to be exhaustive, but it should give a pretty good
feel for the wealth of different possible approaches to formal methods that
could be applied within Midnight. Which approach makes the most sense will
depend on which part of Midnight it is applied to, but more so on what we would
like to achieve by applying formal methods.

We will discuss each of the items in the list above in more detail in the
remainder of this section. 

\Q{Current resources for formal methods are limited, so we have to choose. Where
would formal methods have the most impact, and which techniques would be
suitable there?}

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
  * ZKIR and its semantics
  * Encoding of circuits as PLONKs [@GabizonWC19]
  * Proof server

* Impact
  * Impact VM

* Ledger
  * Contract deployment/interaction
  * Zswap/Token model
  * Consensus algorithm

* Midnight JS 

\Q{Are there other parts of the platform we should consider?}

These specifications can serve to communicate the intended behavior of parts of
Midnights infrastructure, both internally and externally, and are a necessary
prerequisite for further verification of the system. 

## Language Design 

Help to rule out problems _by construction_. Problematic contracts are ruled out
upfront because they're invalid programs. First line of defense: make it
impossible to make certain errors rather than proving after the fact that you
have not made them. 
Work on solidity FM suggests this is useful --> fsm dsl [@MavridouLSD19], F*
translation [@Luu16]

### Type system

* Type-and-effect systems to statically track side-effects (checked
  exceptions/ledger interactions)
  
* Model Non-interference and or information flow

Michael Backes, Hritcu Catalin, and Matteo Maffei. 2014. Union, Intersection
and Refinement Types and Reasoning About Type Disjointness for Secure Protocol
Implementations

Jesper Bengtson, Karthikeyan Bhargavan, Cédric Fournet, Andrew D. Gordon,
and Sergio Maffeis. 2011. Refinement Types for Secure Implementations.

Affine Refinement Types for Secure Distributed Programming

Types for Security Protocols

### Expressivity

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
* Type soundness --> may imply stronger properties if using a
  type-and-effect-system or modelling information flow at the type level
* Privacy properties

\Q{What are other properties of (parts of) Midnight that we might care about?}

## Verification Tools for Users

SMT-based verification
Audited smart contracts a la openzeppelin
IDE support 



## Conformance Testing

Test implementation against reference (e.g., using property-based testing tools
like QuickCheck) 

* Compiler 

* Ledger

* Impact 

* Midnight JS

## Analysis




### Static 

### Dynamic 

* Taint analysis 
* Runtime monitoring



\newpage
# Roadmap

Here, we briefly go over the immediate next steps. Each step may be accompanied
by one or more (optional) deliverables. The main objective is to enable formal
reasoning about the execution of smart contracts. Initially, the goal is to
support reasoning about smart contracts within a proof assistant such as Agda,
but ultimately we should bring verification to users of midnight through IDE
support, verification tools, and/or auditing services.

\Q{Is this the right objective? How high of a priority is verification of the
platform itself in relation with smart contracts?}

\Q{Do we need to reorder, add, or remove steps?}

## Step 0: collect examples of smart contracts and properties {-}

As a prequisite step, we compile a small collection of smart contracts, some of
which may intentionally contain mistakes.Writing down example contracts together
with their desired properties will help us determine what aspects of a
contract's execution are important to model and should be supported by any
reasoning infrastructure we develop for smart contracts.

For example, we may care about time sensitive aspects (_the sold asset is not
transferred to the highest bidder until **after** the auction concludes_),
liveness properties (_the auction is guaranteed to **eventually** conclude_),
which part(s) of the contract's state affect a circuit call (_placing a bid has
no effect on any of the **pre-existing bids**_), or how private data affects
the public state (_placing a bid does not **reveal the bidder's account
balance** to the public_).

Modelling these would respectively require our model of smart contracts to
support connectives/modalities from temporal logic, the modal \textmu-calculus
[@Kozen82], or separation logic, and perhaps more. If we seek to support this
kind of reasoning, a denotational model of smart contracts should also model the
required logic toolkit.

**Deliverable**: a (small) collection of Compact smart contracts, together with
desirable correctness properties. 

## Step 1: specifying compact's type system {-}

Crucial step, because it forces us to give a formal definition of the set of all
   valid smart contracts. This formal spec should be published as part of or
   along with the existing language reference, and act as a source of truth for
   which compact programs are and are not valid.
   
**Deliverable**: A formal specification of Compact's type system written in
literate Agda, published as part of Midnight's documentation. 

## Step 2: specifying Compact's run-time behavior {-}

Specifying the run-time behavior of smart contracts has several purposes: 

* Act as a source of truth for how smart contracts _should_ behave at
  run-time. Can be used as a reference both internally and externally for how
  the execution of smart contracts is intended to proceed. 
  
* Provide a reference against which we can cross-check the bytecode transcripts
  and circuits outputted by the compiler.
   
* Any properties of smart contracts are validated _with respect to their
  run-time semantics_. 

**Deliverable**: A formal specification of Compact's operational semantics
written in literate Agda, published as part of Midnight's documentation. 

**Deliverable**: A denotational model for Compact, specified in Agda. 

**Deliverable**: A proof that the operational model is _sound_ [@WrightF94] with
respect to type system. (Optional) 

**Deliverable**: A proof that the operational model is _sound_ and _adequate_
[@CamposL18] with respect to the denotational model. (Optional)

The denotational model and potential proofs relating the operational model to
the type system/denotational model should be public, but do not necessarily have
to be part of Midnight's documentation, as their purpose is not to communicate
the intended behavior of smart contracts, but rather to support reasoning. 

## Step 3: reasoning about smart contracts {-}

Once we have defined our semantics, we should validate that it supports the
required kind of reasoning. That is, we show in Agda that we can: 

* prove functional properties about the behavior of smart contracts, 

* demonstrate the absence of certain security problems, and 

* reason about privacy/non-interference. 

Ideally, we would loop back to **Step 0** here, and show that we can validate
the examples defined there. 
  
**Deliverable**: toy/example proofs embedded in Agda, to illustrate that the
semantics of smart contracts supports the kind of reasoning we care about. 

## Step 4: specifying the semantics of low-level representations of contracts {-}

When submitting transactions that call a contract, we provide (1) a bytecode
transcript describing the call's effect on the public state, and (2) a ZK-proof
that the transaction is valid w.r.t. the private state. To generate this proof,
the compiler generates an _arithmetic circuit_ from the contract's source which
encodes it's program logic. Since the bytecode transcript and circuit
representation of a contract ultimately determine its effect on the ledger
state, it is important that these accurately reflect the semantics of contracts.

**Deliverable**: A formal specification of (well-formed) bytecode, writen in
  (literate) Agda, together with a denotational semantics in the same domain as
  smart contracts

**Deliverable**: A formal specification of (well-formed) circuits, written in
  (literate) Agda, with a denotational semantics.

**Deliverable**: a reference translation of smart contracts into
  circuits/transcripts, with a proof that these respect the semantics
  (Optional).

## Step 6: what's next? {-}

All the previous steps capture in some sense "necessary" specification work to
claim that we have a formal definition of the (intended) semantics of smart
contracts. From this point there are several things we could do.

### Verification of infrastructure {-} 

* Conformance testing to check that different parts of the system correctly
  implement the intended semantics of smart contracts, such as the compiler,
  Midnight JS, or the ledger.

* Certified compilation

* Formal specificaiton of ledger

### Making verification of smart contracts available to users {-} 

* Auditing

* Reasoning tools

* IDE support


  


# References 

