# 9. Dapp-to-dapp communication

## Status

Proposed

| &ndash; | &ndash; |
| -----------                     | ------------------------------------------ |
| date                            | March 17th, 2023                           |
| deciders                        | Andrzej Kopeć, Joseph Denman, Jon Rossie   |
| consulted                       | -                                          |
| informed                        | -                                          |

## Context and Problem Statement

### Example use-case

There are 3 DApps, each of them having unique private state, which should not be
leaked in any form to the others:

1. Game - state of current game
2. Games Scoring - record of player games and player's "reliability"
3. Identity - personal details

Before a new game starts in Game DApp Game asks Games Scoring DApp for player's score, 
and Games Scoring DApp asks Identity for player's existence or being over 13 years old
(but not identity itself!).

Once game ends - Game lets Games Scoring DApp know the result and Games Scoring DApp
needs to verify identity details again. In a very high-level fashion whole flow looks as below:

![Dapp2Dapp communication sequence](./dapp-to-dapp-communication/Dapp%20Communication.svg)

### Problem Statement

To satisfy this use case (and similar), DApps need to be able to use
functionality of other DApps and contracts they are built upon, without
accessing their private state at all.

Another dimension for this problem is API availability - browsers by design limit
access to system resources/functionalities and ability for websites to interact with
each other on user's machine because of security and privacy concerns.

This problem closely relates to a question - what is the relationship between a
DApp and a Kachina contract? Who, when, and on what basis should make a decision
which website to call if there are multiple ones for a single contract?

<!-- This is an optional element. Feel free to remove. -->

## Decision Drivers

* Overall user experience and user's ability to understand what is happening
* Security&privacy
* Amount of preparation needed to be able to run a DApp
* Complexity of implementation
* Decision about selecting DApp to be called - who, when, and on what basis
  makes the decision about which DApp to call in order to learn certain fact?

## Considered Options

Based on research on in-browser APIs for communicating between contexts, there seem to
be 2 options:

* Letting DApps to communicate directly (similar to
  how various websites can do it) using `window.postMessage` API
* Making DApps to communicate through an API injected by a Browser Extension (e.g.
  based on `tabs.sendMessage` )

There is also a 3rd option available on technical basis, but is not expanded on: a
native application, which registers custom protocol in the OS (similar to what slack, 
spotify, zoom or skype do). This limits communication in size (URL size) as well as
introduces a weird UX of switching between a native app and browser tabs.

4th option, of actually installing packaged DApp code in one way or another in e.g.
dedicated app or extension, etc. is not expanded because of security risks (limited or
non-existent sandboxing APIs) and implementation effort (stable&documented packaging
format, host app/extension implementation, unpackaging and running DApps in a
sandboxed context, like <https://developer.chrome.com/docs/extensions/mv3/manifest/sandbox/>).

5th option, captured in [Contract Kernel ADR](https://github.com/input-output-hk/midnight-architecture/blob/contract-kernel-adr/adrs/0010-contract-kernel.md), 
is similar to 4th, with the major difference being that DApp running in website
installs contract in a secure execution kernel.

## Decision Outcome

No decision yet.

<!-- This is an optional element. Feel free to remove. -->

### Positive Consequences

* {e.g., improvement of one or more desired qualities, …}
* …

<!-- This is an optional element. Feel free to remove. -->

### Negative Consequences

* {e.g., compromising one or more desired qualities, …}
* …

## Validation

{describe how the implementation of/compliance with the ADR is validated. E.g., by a review or an ArchUnit test}
{measurable and easy to automate metrics are preferred, like: less bugs, less churn, 
specific performance metric, etc. }

<!-- This is an optional element. Feel free to remove. -->

## Pros and Cons of the Options

### Direct DApp communication

In this option each DApp can call another one by either embedding its iframe or
opening its website in a new tab through `window.open` function and then using
`<targetWindow>.postMessage` function (<https://developer.mozilla.org/en-US/docs/Web/API/Window/postMessage>).

What is important to keep in mind - both sender and receiver can decide, with which
origins they want to communicate.

This option also allows to decide the style of user interaction, though a lot
depends on both DApps:

* no interaction if the callee allows for that
* interaction in an iframe-based widget
* interaction in a separate browser tab

While certain assumptions and expectations can be embedded in libraries we own, like
the DApp Backend - in the end of the day decisions on the API to communicate lie
solely in hands of DApp developers.

#### Pros and cons

* Good, because it limits amount of work on our side
* Good, because it leverages existing APIs web developers are rather familiar with
* Good, because it allows for various kinds of user experience
* Good, because it doesn't require specific preparation on user side
* Bad, because we loose control over the APIs being used to communicate, which may
  pose security and privacy risks
* Bad, because it may lead to form of centralization towards some DApps if they are
  popular target, with no easy way for user being decisive other than refusing to use
  specific DApps  

#### Fit to drivers

* Overall user experience and user's ability to understand what is happening - it is
  possible to create both great and terrible UX this way - all depends on DApp developers
* Security&privacy - depends on DApp developers. It is possible to have both, as
  well as make compromising mistakes
* Amount of preparation needed to be able to run a DApp - none, assuming called dapps
  are initialized
* Complexity of implementation - left to DApp developers, we might provide relatively
  simple helpers to streamline DApp developers efforts
* Decision about selecting DApp to be called - lies in the caller DApp, which, 
  depending on approach for persisting and accessing private state, which may be an
  issue for multiple DApps built on the same contract, as browser would see each of
  them as a separate origin

### Communication through a Browser Extension

This approach assumes existence of an API, which DApps, or the runtime even, can call
in order to request an information/proof from other DApps. Such API could be
established on top of `window.postMessage` and either [connection-based messaging](https://developer.mozilla.org/en-US/docs/Mozilla/Add-ons/WebExtensions/Content_scripts#connection-based_messaging)
or [ `tabs.sendMessage` API](https://developer.mozilla.org/en-US/docs/Mozilla/Add-ons/WebExtensions/API/tabs/sendMessage).

This option requires us to make additional decisions (some of them seem to be
possible to be deferred with right API design) like:

* whether to use Wallet extension or implement a dedicated one
* whether DApp indicate callee by URL or some identifier, the latter
    immediately requiring at least a form of discovery/registry of DApps user
    interacted with or available in the network

* what form of user interaction is needed or allowed

### Pros and cons

* Good, because it offers unification of communication across DApps in the ecosystem
* Good, because it allows to implement a system, that puts user in control, when needed
* Good, because it allows to integrate wallet permissions for DApps, with other user
  preferences
* Good, because it allows clear and relatively secure path for offloading proving by
  [ `runtime.connectNative` API](https://developer.mozilla.org/en-US/docs/Mozilla/Add-ons/WebExtensions/API/runtime/connectNative)
* Good, because it allows us to control part of user experience and/or set certain
  patterns
* Neutral, because it does not necessarily prevent other forms of communication
* Bad, because in case of embedding the extension in wallet - it may significantly
  limit 3rd-party wallet developments
* Bad, because it requires more work upfront to enable the use-case
* Bad, because it forces user to install Midnight-specific browser extension in order
  to use more complex/usable DApps

#### Fit to drivers

* Overall user experience and user's ability to understand what is happening - it
  depends on persona. People who are used to browser extensions should be fine with
  the UX this option may involve, others may not pass beyond installing the extension.
* Security&privacy - we have a way to enforce certain practices/designs here, so this
  rises possibility for a reasonable baseline. Aside malicious extensions (which is
  risk for whole web), the biggest risks seem to involve dishonest/poorly-written DApps, 
  which is a risk anyways.
* Amount of preparation needed to be able to run a DApp - installed and set-up browser
  extension
* Complexity of implementation - it is something, which can be a relatively simple
  implementation in a PoC-like stage (establish connection, when receiving a message
  open given url, pass response back once ready), but very complex to get absolutely
  right in a more advanced setup (tracking user dapps, discovering new ones, state
  persistence maybe?, proxy to proof server?)
* Decision about selecting DApp to be called - can lie in hands of user

<!-- This is an optional element. Feel free to remove. -->

## More Information
