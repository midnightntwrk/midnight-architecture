# 10. Contract Kernel

## Status

Proposed

---
<!-- These are optional elements. Feel free to remove any of them. -->
| -         | -                                        |
|-----------|------------------------------------------|
| date      | March 17th, 2023                         |
| deciders  | Jon Rossie, Andrzej Kopeć, Thomas Kerber, Joseph Denman |
| consulted | -                                        |
| informed  | -                                        |
---

## Context and Problem Statement

This ADR is a counter-proposal to [ADR-9](./0009-dapp-to-dapp-communication.md).

### Terminology
 Throughout this document *application* means *decentralized application*. Assume that the user accesses applications by navigating to a URL using a web browser. To *call a contract* means to invoke a transition function defined in the contract. An application must *install* a contract in the browser computing environment before the contract can be called.

### Problem Statement
Contract functionality should be reusable across other contracts and applications running in the user browser. The mechanism of reuse should not compromise the private data of the contract. There are at least two reuse scenarios we must support.

1. An installed contract may call another installed contract.
2. An application may call a contract another application installed.

In both cases, the calls should be evaluated using the current private state of the contract.

<!-- This is an optional element. Feel free to remove. -->
## Decision Drivers

The solution should have the following properties.
* Security
* Privacy
* Reliability
* Usability
* Testability
* Performance
* Auditability
* Debuggability
* Upgadeability


## Considered Options

There are two main contenders for the reuse scheme.

* Inter-application Messaging (IAM)
* Contract Kernel (CK)

## Decision Outcome

Chosen option: Pending

<!-- This is an optional element. Feel free to remove. -->
### Positive Consequences

* TODO

<!-- This is an optional element. Feel free to remove. -->
### Negative Consequences

* TODO

## Validation

{describe how the implementation of/compliance with the ADR is validated. E.g., by a review or an ArchUnit test}
{measurable and easy to automate metrics are preferred, like: less bugs, less churn, 
specific performance metric, etc. }

<!-- This is an optional element. Feel free to remove. -->
## Pros and Cons of the Options

### Contract Kernel

<!-- This is an optional element. Feel free to remove. -->
{example | description | pointer to more information | …}

* Good, because {argument a}
* Good, because {argument b}
<!-- use "neutral" if the given argument weights neither for good nor bad -->
* Neutral, because {argument c}
* Bad, because {argument d}
* … <!-- numbers of pros and cons can vary -->

### Inter-application Messaging

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
