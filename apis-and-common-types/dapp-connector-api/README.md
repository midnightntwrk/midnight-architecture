# Component Name

DApp Connector API

The DApp Connector is a component within the Wallet Extension, which uses Browser Extension APIs to build and expose its API to the DApp. The API allows the DApp to communicate with the Wallet and use its services i.e initiate transactions, query data etc.

## How does the DApp Connector API work?

The DApp Connector uses the browser extension Content Scripts to expose its API to the DApp, and Background Scripts to process the requests coming from the exposed API.

To elaborate this a little further, in the content script we define the API that will be exposed (injected) to the DApp. Once the exposed API is called (ex. DApp requests to sign a transaction), the request is sent to the content script, and from the content script it's sent to the background script.

The background script is where the we:

1. process the request - call the necessary APIs and return a response
2. ask for user action i.e open a popup, and once the user responds, depending on the response we either process or fail the request

There is a communication diagram below which visually explains the communication.

## Special Needs

Since the extension will support many different browsers (see Operating Environment below), we need to make sure that the Browser Extension APIs we use are supported across all browsers. This causes some bottlenecks in the development process, one of them being Messaging - which is the key API that handles communications from the DApp to the Extension and vice versa. [While Chrome supports a more modern way of communication](https://developer.chrome.com/docs/extensions/mv3/messaging/#external-webpage), [Firefox doesn't](https://developer.mozilla.org/en-US/docs/Mozilla/Add-ons/WebExtensions/manifest.json/externally_connectable), therefore, in order to have a consistent and working communication channel between DApp and Extension, we must use custom JavaScript events + Browser Runtime Messaging API.

In addition to that, we need to address the following security concerns:

1. All the requests that are handled externally (DApp -> Content Scripts) and internally (Content Scripts -> Background Scripts -> Wallet) needs to have the source of the request tested and matched in all steps of the communication.
2. Only requests from web pages (DApps) are allowed, requests coming from other extensions must be blocked.


## Neighbors & API Dependencies

DApp Connector API has three dependencies:

1. Browser Extension API
2. Background Scripts
3. Content Scripts

## Operating Environment

DApp Connector API is part of the Wallet Extension which is run in a desktop browser, potentially any that support the WebExtensions API. Specifically, the ones that are most likely to be used are:
  - Google Chrome
  - Mozilla Firefox
  - Apple Safari
  - other Chromium-based browsers like Microsoft Edge, Brave, Opera, Vivaldi, etc.

Possibly any desktop operating system that allows running some browser listed above may be used, the most popular
ones are:
  - Microsoft Windows
  - Linux distributions
  - macOS
  - BSD flavors

## Key Library Dependencies


## Logical Data Model

![](./communication.svg)

### Entities

Document the entities.

#### Entity 1

#### Entity 2

### Invariants

This MUST include state invariants expressed in terms of the ER model that describe the valid states of the system.

## Responsibilities

### Interface Data Types

What kinds of data are used in the API's, either as inputs or outputs?  Are they versioned?  Does the component have to support multiple versions at once?

### API's
What API's does the component support?  It's not necessary to include the actual code.  Rather, document the nature of the responsibility and any special constraints.

#### API 1

##### Event 1

- Name, input args, return type, kinds of failures
- Computational complexity
- Net effect on memory size or disk usage
- What ER-model structures are used to handle the event?

##### Event 2

## Architecture Characteristics

NOTE:  There is also a quick [reference list of architecture characteristics](../definitions.md#architecture-characteristics) available.

NOTE:  Choose wisely, the more architecture characteristics are identified for a component, the more complicated it will be.  Also, bear in mind that some architecture characteristics can be delegated to software design or UX.

Here is a list of sample architecture characteristics, please remember to update them to match the needs of the particular component.

### Configurability

Configurability is a cross-cutting responsibility that affects many API's.  The antidote to a regrettable constant in your code is proper configurability.  What are the configuration parameters (policy) supported by the component?

### Performance

- What is the expected complexity bound of each API function?
- For each API function, what is its net effect on memory growth and what mechanisms are included to prevent memory leaks?

### Availability

Is it ok for the component to "just let it fail" when things go wrong, or must this component fight to survive all errors?

### Security, Authentication, Authorization

How are the API's protected against unauthorized use?  What is the DDoS defense, for example?  Are there operations that require specific authorization using signatures or authenticated identities?

### Debugability, Serviceability

- What logging levels are supported and can they be dynamically configured?
- How does the component provide debug context on a crash?


## Life Cycle (State Machine)

The component MUST declare whether it has a lifecycle that can be described as a state machine.  This should include any state changes that affect things like the availability of the component or its resources.  A component that performs periodic expensive memory-refactoring, for example, should document this period of unavailability and high resource usage as a distinct state.

How will the component handle unavailability of required services, both at launch and in steady state?
