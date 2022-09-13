# 4. Workshops without browser support

## Status

accepted

---
| -         | -                             |
|-----------|-------------------------------|
| date      | 2022-09-13                    |
| deciders  | Architects team, Product team |
| informed  | Whole team                    |
---

## Context and Problem Statement

After performing an analysis of components and flows necessary to deliver the 
Workshops, it became apparent, that browser support may get into way of timely 
delivery, distract from what is important for the workshops - developer 
experience and provide a false sense of finished product (because of presented UI).

## Decision Drivers

* Timely delivery of workshops
* Showcase only components that are required in development/demo flows
* Have solid foundations for claims made during workshops
* Send a clear message that the product is not finished one
* Send a clear message that browser support is as essential part of the roadmap

## Considered Options

* Support browser (with optional wallet browser extension), with a very raw UI and 
  potentially some components communicating over remote calls
* Drop browser support, with terminal UI and all components needed linked together 
  (either by FFI or a single binary)

## Decision Outcome

Chosen option: "Drop browser support", because
  - it allows components like ledger or zero knowledge system (which are implemented in 
    Rust) connect through an FFI interface to node.js (which is simpler than 
    WebAssembly) - this is essential for claims that private data stays on the device
  - it means fever components need to be ready by the time of workshops, which makes 
    timely delivery less risky
  - with usage of node.js and [ink library](https://github.com/vadimdemedes/ink) it is 
    possible to showcase at the same time that the product is still not finished and 
    that we're serious about eventual browser support
  - there is still possibility to implement UI part of the demo DApps in browser, while 
    keeping the mechanics running in node.js so that the separation of wallet from DApp
    is more pronounced and the DApp UI can be later connected to a browser-native mechanism

### Positive Consequences

* Clear path to deliver workshops, with less moving parts and a big potential for 
  polishing

### Negative Consequences

* Need for follow-up efforts after the workshops, to put everything back on track wrt. 
  desired architecture

## Validation

The best validation of this decision is relatively early integration (end of September)
of major components needed for the workshops, so from that point incremental 
improvements are being implemented.

## More Information

Tracked on Midnight Architecture JIRA Board as:
- [[PM-4910] Generating zk proofs in browser?](https://input-output.atlassian.net/browse/PM-4910)
- [[PM-4955] Browser support for the workshops](https://input-output.atlassian.net/browse/PM-4955)
- [[PM-4950] Rust ledger implementation for native tokens support for the workshops](https://input-output.atlassian.net/browse/PM-4950)
