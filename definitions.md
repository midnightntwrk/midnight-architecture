# Definitions of Architectural Elements

A software architecture is documented in terms of building blocks and assemblies of those building blocks.  It helps to have a common understanding of those elements and of our responsibilities as architects and engineers in designing and documenting those blocks and their interations.

## System

A collection of cooperating components, perhaps distributed across a network.

## Deployment

A suppored collection of execution environments and their components.

## Flow

A flow is a complete interaction with the system by some external agent, which may be a human or some external client or system not under our control.  Flows should be documented as *sequence diagrams* of interacting components driven by events from external agents.  

## Feature

A feature is a collection of related flows that represent a coherent set of operations relating to a specific objective or specific type of information managed by the system.  Engineers should work with product owners to translate high-level feature requirements into a prioritized collection of flows.  Since flows cross component boundaries, each feature may involve updates to multiple components.

Document the important variants of each flow, including error cases.  The product team may prioritize some variants ahead of others to manage scope and effort, so it's good practice to document the simplest possible flows that enable the core feature as a first effort.  More elaborate flows could then be grouped classified as a deferred feature of their own.

## Component

*Protocol, Policy, Mechanism*

Components are the building blocks of the system.  A component is defined chiefly by its responsibilities and the data it must maintain to meet those responsibilities.  Each component is implemented to operate in one or more environments, such as a specific operating system (Ubuntu 20.14.1) or language runtime (Ecmascript 4.0).

### Special Needs

- Formal specification?
- Deterministic execution (perhaps on a variety of runtimes)?

### Neighbors & API Dependencies

- What components or versioned API's interact directly with this one?
- Divide these into *clients* (components that depend on this one) and *services* (components or API's this one depends upon).
- For clients, try to characterize the expected behavior.  Is the client trusted or not?  Is its usage heavy or light (try to bound this numerically).  Are its messages dynamically versioned?

### Operating Environment

List the assumptions about the operating environment.

- What OS or runtime?  (What supported versions?)
- What access to network resources?
- Is memory especially constrained?
- Are any services required in order to launch?

What are the assumptions about the messaging infrastructure?

- Are messages ever reordered?
- Are messages ever duplicated?
- Are messages ever lost?

What is the logging system?

What is the configuration infrastructure that delivers dynamic configuration to the component?

### Key Library Dependencies

If this component is specified to rely heavily on specific external libraries or specifications, perhaps for purposes of interop with other components, list those (versioned) dependencies and the reason for each dependency.

### Responsibilities

The greatest detail about a component are expressed as its *responsibilities*.  These include the API's it supports, the data it maintains to service those API's.  Note that the usual non-functional requirements are listed separately as _architecture characteristics_ for the component.

#### Responsibility: API's to Support

These may be expressed in different levels of detail, typically starting with natural language but eventually stabilizing into versioned, concrete API specs.

#### Responsibility: Data to Maintain

This MUST include an Entity-Relation model of the data maintained by the system.

This MUST include state invariants expressed in terms of the ER model that describe the valid states of the system.

This MAY include detailed design of data structures, since the ER model is rarely used directly for storing data.

### Component's Architecture Characteristics

NOTE:  Choose wisely, the more architecture characteristics are identified for a component, the more complicated it will be.  Also, bear in mind that some architecture characteristics can be delegated to software design or UX.

Here is a list of sample architecture characteristics, please remember to update them to match the needs of the particular component.

##### Configurability

Configurability is a cross-cutting responsibility that affects many API's.  The antidote to a regrettable constant in your code is proper configurability.  What are the configuration parameters (policy) supported by the component?

##### Performance

- What is the expected complexity bound of each API function?
- For each API function, what is its net effect on memory growth and what mechanisms are included to prevent memory leaks?

##### Availability

Is it ok for the component to "just let it fail" when things go wrong, or must this component fight to survive all errors?

##### Security, Authentication, Authorization

How are the API's protected against unauthorized use?  What is the DDoS defense, for example?  Are there operations that require specific authorization using signatures or authenticated identities?

##### Debugability, Serviceability

- What logging levels are supported and can they be dynamically configured?
- How does the component provide debug context on a crash?


### Life Cycle (State Machine)

The component MUST declare whether it has a lifecycle that can be described as a state machine.  This should include any state changes that affect things like the availability of the component or its resources.  A component that performs periodic expensive memory-refactoring, for example, should document this period of unavailability and high resource usage as a distinct state. 

How will the component handle unavailability of required services, both at launch and in steady state?

# Architecture Characteristics

[Richards and Ford (2020)](https://www.oreilly.com/library/view/fundamentals-of-software/9781492043447/) propose to use the term _architecture characteristics_ instead of the usual _non-functional requirements_ or _quality attributes_.

They specify that an architecture characteristic meets the following criteria:

- Specify a non-domain design consideration,
- Influence some structural aspect of the design,
- Be critical or important to appliaction success.

They also provide a partial list of architectural characteristics they identified.

## Operational Architecture Characteristics

Richards and Ford mention that "operational characteristics heavily overlap with operations and DevOps concerns, forming the intersections of those concerns in many software projects".

Following definitions taken verbatim from Richards and Ford (2020).

| Characteristic     | Definition |
| ------------------ | ---------- |
| Availability       | How long the system will need to be available (if 24/7, steps need to be in place to allow the system to be up and running quickly in case of any failure). |
| Continuity         | Disaster recovery capability. |
| Performance        | Includes stress testing, peak analysis, analysis of the frequency of functions used, capacity required, and response times. Performance acceptance sometimes requires an exercise of its own, taking months to complete. |
| Recoverability     | Business continuity requirements (e.g., in case of a disaster, how quickly is the system required to be on-line again?). This will affect the backup strategy and requirements for duplicated hardware. |
| Reliability/Safety | Assess if the system needs to be fail-safe, or if it is mission critical in a way that affects lives. If it fails, will it cost the company large sums of money? |
| Robustness         | Ability to handle error and boundary conditions while running if the internet connection goes down or if there’s a power outage or hardware failure. |
| Scalability        | Ability for the system to perform and operate as the number of users or requests increases. |

## Structural Architecture Characteristics

Following definitions taken verbatim from Richards and Ford (2020).

| Characteristic        | Definition |
| --------------------- | ---------- |
| Configurability       | Ability for the end users to easily change aspects of the software’s configuration (through usable interfaces). |
| Extensibility         | How important it is to plug new pieces of functionality in. |
| Installability        | Ease of system installation on all necessary platforms. |
| Leverageability/Reuse | Ability to leverage common components across multiple products. |
| Localization          | Support for multiple languages on entry/query screens in data fields; on reports, multibyte character requirements and units of measure or currencies. |
| Maintainability       | How easy it is to apply changes and enhance the system? |
| Portability           | Does the system need to run on more than one platform? (For example, does the frontend need to run against Oracle as well as SAP DB? |
| Upgradeability        | Ability to easily/quickly upgrade from a previous version of this application/solution to a newer version on servers and clients. |

## Cross-Cutting Architectur Characteristics

Finally, Richards and Ford identify some characteristics that cannot be easily categorized.

Following definitions taken verbatim from Richards and Ford (2020).

| Characteristic          | Definition |
| ----------------------- | ---------- |
| Accessibility           | Access to all your users, including those with disabilities like colorblindness or hearing loss. |
| Archivability           | Will the data need to be archived or deleted after a period of time? (For example, customer accounts are to be deleted after three months or marked as obsolete and archived to a secondary database for future access.) |
| Authentication          | Security requirements to ensure users are who they say they are. |
| Authorization           | Security requirements to ensure users can access only certain functions within the application (by use case, subsystem, webpage, business rule, field level, etc.). |
| Legal                   | What legislative constraints is the system operating in (data protection, Sarbanes Oxley, GDPR, etc.)? What reservation rights does the company require? Any regulations regarding the way the application is to be built or deployed? |
| Privacy                 | Ability to hide transactions from internal company employees (encrypted transactions so even DBAs and network architects cannot see them). |
| Security                | Does the data need to be encrypted in the database? Encrypted for network communication between internal systems? What type of authentication needs to be in place for remote user access? |
| Supportability          | What level of technical support is needed by the application? What level of logging and other facilities are required to debug errors in the system? |
| Usability/Achievability | Level of training required for users to achieve their goals with the application/solution. Usability requirements need to be treated as seriously as any other architectural issue. |


## Aggregate

A logical data entity that is an entry point for performing operations and protects its invariants.

The implementation of Aggregate should take into consideration that operations on entities that are part of the 
aggregate should always be implemented in a way that allows aggregate to protect its invariants. Preferably by 
initiating any operations on aggregate itself, and allowing it to delegate more granular operations on its 
comprising entities. 

The term arises from the [Domain-Driven-Design book](https://www.amazon.com/gp/product/0321125215/ref=as_li_tl?
ie=UTF8&camp=1789&creative=9325&creativeASIN=0321125215&linkCode=as2&tag=martinfowlerc-20) and below are links that 
provide some useful definitions or insights to what aggregates are: 
  - [Martin Fowler](https://www.martinfowler.com/bliki/DDD_Aggregate.html)
  - [Kacper Gunia](https://domaincentric.net/blog/tag/aggregates)

## Invariant

A property which remains unchanged after operations or transformations are applied to the objects it relates to.


