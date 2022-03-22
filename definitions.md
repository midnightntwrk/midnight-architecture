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

The greatest detail about a component are expressed as its *responsibilities*.  These include the API's it supports, the data it maintains to service those API's, and the nun-functional requirements associated with the API's.

#### Responsibility: API's to Support

These may be expressed in different levels of detail, typically starting with natural language but eventually stabilizing into versioned, concrete API specs.

##### Responsibility: Configurability

Configurability is a cross-cutting responsibility that affects many API's.  The antidote to a regrettable constant in your code is proper configurability.  What are the configuration parameters (policy) supported by the component?


#### Responsibility: Data to Maintain

This MUST include an Entity-Relation model of the data maintained by the system.

This MUST include state invariants expressed in terms of the ER model that describe the valid states of the system.

This MAY include detailed design of data structures, since the ER model is rarely used directly for storing data.



#### Responsibility: Non-Functional Requirements

##### Scalability

- What is the expected complexity bound of each API function?
- For each API function, what is its net effect on memory growth and what mechanisms are included to prevent memory leaks?

##### Availability

Is it ok for the component to "just let it fail" when things go wrong, or must this component fight to survive all errors?

##### Security

How are the API's protected against unauthorized use?  What is the DDoS defense, for example?  Are there operations that require specific authorization using signatures or authenticated identities?

##### Debugability, Serviceability

- What logging levels are supported and can they be dynamically configured?
- How does the component provide debug context on a crash?


### Life Cycle (State Machine)

The component MUST declare whether it has a lifecycle that can be described as a state machine.  This should include any state changes that affect things like the availability of the component or its resources.  A component that performs periodic expensive memory-refactoring, for example, should document this period of unavailability and high resource usage as a distinct state. 

How will the component handle unavailability of required services, both at launch and in steady state?

