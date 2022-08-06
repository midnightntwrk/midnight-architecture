# 2. Architecture Repository Purpose and Format

## Status

accepted

---
| -         | -                   |
|-----------|---------------------|
| date      | 2022-07-14          |
| deciders  | Jon Rossie (mostly) |
| consulted | Midnight team       |
---

## Context and Problem Statement

There was some misalignment about different aspects of this repository. 
This document is an attempt to document outcome of discussions held on the topic.

Especially important is to define target audience and the way the contents of this 
repository are meant to be consumed and authored.

## Decision Drivers

* clearly state, how the contents of this repository is meant to be authored and consumed
* clearly state, how diagrams are meant to be rendered

## Considered Options

* Use GitHub as the "rendering engine", create diagrams using GitHub-supported Mermaid
* Use GitHub as the "rendering engine", create diagrams using PlantUML
* Use a documentation engine like mdbook with additional plugins

## Decision Outcome

Chosen option: "GitHub + PlantUML", because:
* the ultimate goal of this repository is to be documentation for internal purposes 
  only - engineering, product. But no developer relations, or end-user facing docs  
* is a lightweight approach - no need for additional operations needed for 
  compilation/deployment/etc. of a dedicated tool
* works well for many people for reading
* provides direct feedback when authoring - many preview engines in editors are 
  compatible with the way GitHub renders pages
* supports OrgMode
* PlantUML is a really advanced and powerful engine, Mermaid in many aspects is 
  too simplistic for our needs 
* misses only an integrated way of rendering PlantUML files, though this is 
  relatively easy to address with Cicero

There is a risk, that to address different shortcomings of navigating through
contents of this repository, different "small" and "easy" automations will be added,
which together lead to a full-fledged documentation system. This doesn't have to be a 
bad thing though.

### Positive Consequences

* Easy to write and read documentation
* Good support across editors to render PlantUML diagrams - quick feedback loop when 
  creating a diagram
* No additional compilation step
* No additional deployment step to access documentation
* There is still an open way towards migrating to a different tools in the future

### Negative Consequences

* Navigation through repository contents is limited in GitHub, though way better in 
  local filesystem

## Pros and Cons of the Other Options

### GitHub + Mermaid

* Good, because Mermaid is supported directly by GitHub - no need for separate diagram 
  rendering
* Bad, because Mermaid lacks a lot in power and functionality

### Documentation-specific solution

* Good, because it does automate many aspects of writing documentation
* Bad, because it adds overhead of deployments and rendering steps (for whole 
  documentation), which is perceived unnecessary complication in this context at this 
  moment

## More Information

Related Jira ticket: https://input-output.atlassian.net/browse/PM-3856

Slack thread touching on the topic: https://input-output-rnd.slack.com/archives/GEH5A0YLR/p1654775704471689
