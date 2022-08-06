# 1. Use ADRs and adrgen

## Status

accepted

---

| -         | -                                                                |
|-----------|------------------------------------------------------------------|
| date      | 2022-07-08                                                       |
| deciders  | Midnight team, on initiative of Jakub Zalewski and Andrzej Kopeć |

---

## Context and Problem Statement

There is a need to document decisions made in a single place, so not only they are not
lost, but also it is possible to rebuild context.

Another, closely related, problem to be addressed is a need for repeatable, easy to follow
process of making and documenting high-level technical and architectural decisions.

## Considered Options

* use established ADR template and tool to manage ADR documents
* use PR template as a form of ADR, manage ADRs manually

## Decision Outcome

Use ADR as "Any Decisions Record" tool. Implement a process of making decisions, where 
(in most cases):

- tickets, decisions to be made, questions, doubts, etc. are first added to the Jira
  Architecture
  board: https://input-output.atlassian.net/jira/software/c/projects/PM/boards/799
- during Tech Assembly calls, items on the board are being reviewed and refined, most
  notably - stakeholders of particular ticket are being identified, so that they can make
  the decision off-line, and ticket is being moved to in-progress
- once the decision is made - an update to this repository is meant to be made - as an ADR
  or other form of documentation
- once the update is ready - the ticket is moved to "in review" column to collect feedback
  from stakeholders who didn't create the documentation and rest of Midnight team as
  well
- when update PR is merged, during a Tech Assembly call - decision with accompanying 
  documentation is shortly presented to the whole Midnight team for visibility, 
  accompanying ticket is moved to "done" status

Use established ADR template from [madr project](https://github.com/adr/madr/), because it
is a complete one that matches well many scenarios and implicitly forces to prepare a good
decision documentation.

Use adrgen tool, since it does its job in managing ADR documents, and is easy to add to
nix development shell.

### Positive Consequences

- there is a clear process which ties Architecture repo, Jira Architecture board and 
  allows whole Midnight team to participate
- there is a dedicated place for documenting decisions in the Arch repo
- there is tooling present for easier management of ADR documents

### Negative Consequences

I'm not aware of any

## Validation

When new people join the team, or someone forgets about some decision - it becomes
possible to refer to a related ADR document so that person can (re)build the context.

Tech assembly calls become relatively short (up to 30 minutes) if no additional topics 
are discussed.
