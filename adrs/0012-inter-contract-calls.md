# Composable Contracts - Simple

## Status

{status}

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                                                                                                                            |
|-----------|------------------------------------------------------------------------------------------------------------------------------|
| date      | {date}                                                                                                                       |
| deciders  | {list everyone involved in the decision}                                                                                     |
| consulted | {list everyone whose opinions are sought (typically subject-matter experts; and with whom there is a two-way communication}) |
| informed  | {list everyone who is kept up-to-date on progress; and with whom there is a one-way communication}                           |
---

## Context and Problem Statement

Modular composability is a fundamental characteristic of scalable and maintainable software systems. It suggests that a
complex software system should be constructed from a set of reusable, functionally complete software modules, each with
a limited scope of responsibility.

The initiative to support contract composability in the Compact language is motivated by the following example:



The previous example can be generalized to the following user stories:

> As a DApp developer, I want to add an undeployed contract `A` to the ledger:
> 1. I want to directly add `A` to the ledger by submitting a deploy transaction for `A`.
> 2. I want to indirectly add `A` to the ledger by submitting a call transaction for a contract `B` that deploys an instance of `A`.

> As a DApp developer, I want to update the ledger state of a deployed contract `A`:
> 1. I want to directly update the ledger state of `A` by submitting a call transaction for `A`.
> 2. I want to indirectly update the ledger state of `A` by submitting a call transaction for a contract `B` that calls `A`.

With the following additional requirements.:

> When Alice, a DApp developer, calls a contract `A` that creates an instance of contract `B`, the return data of the contract
> call should allow Alice to reference the new contract `B`, perhaps by returning the address of `B`.

For 
{Describe the context and problem statement, e.g., in free form using two to three sentences or in the form of an illustrative story.
You may want to articulate the problem in form of a question and add links to collaboration boards or issue management systems.}

<!-- This is an optional element. Feel free to remove. -->
## Decision Drivers

* To be useful, Compact must have a mechanism for smart contract reuse.
* {decision driver 2, e.g., a force, facing concern, …}
* … <!-- numbers of drivers can vary -->

## Considered Options

* {title of option 1}
* {title of option 2}
* {title of option 3}
* … <!-- numbers of options can vary -->

## Decision Outcome

Chosen option: "{title of option 1}", because
{justification. e.g., only option, which meets k.o. criterion decision driver | which resolves force {force} | … | comes out best (see below)}.

<!-- This is an optional element. Feel free to remove. -->

### Positive Consequences

* {e.g., improvement of one or more desired qualities, …}
* …

<!-- This is an optional element. Feel free to remove. -->

### Negative Consequences

* {e.g., compromising one or more desired qualities, …}
* …

## Validation

1. The Compact standard library can be incorporated into any contract using standard composition mechanisms; it is not
   a special case.

{describe how the implementation of/compliance with the ADR is validated. E.g., by a review or an ArchUnit test}
{measurable and easy to automate metrics are preferred, like: less bugs, less churn,
specific performance metric, etc. }

<!-- This is an optional element. Feel free to remove. -->

## Pros and Cons of the Options

### {title of option 1}

<!-- This is an optional element. Feel free to remove. -->
{example | description | pointer to more information | …}

* Good, because {argument a}
* Good, because {argument b}
<!-- use "neutral" if the given argument weights neither for good nor bad -->
* Neutral, because {argument c}
* Bad, because {argument d}
* … <!-- numbers of pros and cons can vary -->

### {title of other option}

{example | description | pointer to more information | …}

* Good, because {argument a}
* Good, because {argument b}
* Neutral, because {argument c}
* Bad, because {argument d}
* …

<!-- This is an optional element. Feel free to remove. -->

## More Information

{You might want to provide additional evidence/confidence for the decision outcome here and/or
document the team agreement on the decision and/or
define when this decision when and how the decision should be realized and if/when it should be re-visited and/or
how the decision is validated.
Links to other decisions and resources might here appear as well.}


### Acceptance Criteria (?)

1. The Compact standard library is accessed through standard composition mechanisms; it is not a special case.

   Solidity has a `library` keyword that allows contracts to be deployed as libraries. Library functions do not modify
   state.

### Open Questions

### Design Open Questions

1. Must all circuits be declared in a contract scope?

   Some circuits implement functionality that does not modify the state of a contract. These are analogous to static
   functions in Java. The Compact standard library contains such functions.

   How are "pure" functions implemented? Are keys created for them? Is their execution proven?

### Other Open Questions

1. What account API is available to contracts?
 
2. How do imports work?

3. Can declarations be made and used freely between different contracts, or must all declarations a contract
   uses be declared in the contract itself?

4. What is the purpose of modules? Are they just a way to organize declarations, or do they have some other purpose?

5. Can interfaces be declared inside of contracts?

6. If calling a contract cedes control to another contract, how can that be exploited?

7. There should be access modifiers for ledger data and circuits that default to the most restrictive access possible. For example, a function
   should default to private, and a variable should default to private. This is to prevent accidental exposure of
   sensitive data.

8. All contracts must be passed as parameters or created at runtime. It must not be possible to store a contract type in 
   the ledger. This is to prevent users from accidentally invoking a contract for which they do not have the source code.

9. How do we represent the structure in Javascript?

10. Disallow casting of `ContractAddress` values. Ensure that the runtime has distinct representations for contract addresses
    and other types. There should be no way to create an instance of `ContractAddress` in the source language.

11. The role of checkpoints / pre-conditions / post-conditions. As contract systems grow larger, their behavior becomes more difficult
    to predict. It is important to have a way to verify that a contract is behaving as expected.

12. Can contracts be instantiated in contract constructors?

------------------------------------------------------------------------------------------------------------------------

# Proving Dynamic Contract Instantiation

The main question is:

> What does it mean to prove correct computation of a contract constructor?

At minimum this should mean:

1. The shape of the ledger state is correct; _exactly_ the ledger fields defined in the contract are present in the new
   contract state.
2. The ledger and witness queries performed in the constructor are provably correct.
3. The contract address returned by the constructor is provably correct.















## Calls corresponds call transactions and instantiations corresponds to deploys

In this scenario, contract calls and instantiations are represented by call transactions. Each dynamic contract instantiation
produces data required to construct a deploy transaction. Each inter-contract call produces data required to construct a
call transaction. All deploy transactions _D_ precede all call transactions and all transactions are merged into a single
transaction _T_. This raises the following questions.

### Transaction Atomicity

For this approach to be viable, we must guarantee the following:

1. Either all of _D_ and _C_ succeed or fail.


2. _T_ is never merged with another transaction.

   This property is particularly important. If deploy $D_1$
   
3. _D_ and _C_ are executed in sequence.

## Constructors are circuits

In this scenario, contract constructors are circuits. They accept Compact values and return a contract address. The
body of the circuit consists of a set of public and private oracle queries that initialize the ledger and witness state.
Contract constructors proofs use the same message-passing commitment scheme as inter-contract calls do. This raises the 
following questions.

### Generating Fresh Addresses

Can a fixed circuit generate a fresh address each time?

### Prover and Verifier Keys for Constructors

Since prover _P_ and verifier _V_ keys need to be attached for each circuit to verify proofs, what does it mean that _P_
and _V_ would exist for the constructor circuit? Does this mean call transactions can be can target constructors?

   















