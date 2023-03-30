# 10. Contract Kernel

## Status

Proposed

<!-- These are optional elements. Feel free to remove any of them. -->
|          |                                         |
|-----------|------------------------------------------|
| date      | March 17th, 2023                         |
| deciders  | Jon Rossie, Andrzej Kopeć, Thomas Kerber, Joseph Denman |

---

## Context and Problem Statement

This ADR is a counter-proposal to [ADR-9](./0009-dapp-to-dapp-communication.md).

### Terminology
 Throughout this document *application* means *decentralized application*. Assume that the user accesses applications by navigating to a URL using a web browser. To *call a contract* means to invoke a transition function defined in the contract. An application must *install* a contract in the browser computing environment before the contract can be called. A *local program* is either a transition function or a private oracle.

### Problem Statement
Contract functionality should be reusable across other contracts and applications running in the user browser. The mechanism of reuse should not compromise the private data of the contract. There are at least two reuse scenarios we must support.

1. An installed contract may call another installed contract.
2. An application may call a contract another application installed.

In both cases, the calls should be evaluated using the current private state of the installed contract.

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
* Upgradeability


## Considered Options

There are two main contenders for the reuse scheme.

* Inter-application Messaging (IAM)
* Contract Kernel (CK)

### Inter-application Messaging (IAM)

In this scheme, contracts and private oracles are assumed to be embedded within the web page containing the application; they are treated no differently than the application code. As a result, both of the reuse scenarios require interacting with the application that hosts the contract and private oracle. To support inter-application contract calls, there would be an *application mesh* that provides application discovery, messaging, and authorization services. Applications register with the mesh upon loading to make the contracts they host available to other applications. They provide an *access policy* to the application mesh upon registration to control which other other applications can access the contracts they host.

**Pros**:

1. No single point of failure
2. Independent contract executions are automatically concurrent

**Cons**:

1. Difficult to test
2. Difficult to debug
3. Difficult to use
4. Unreliable
5. Poor performance for inter-contract calls
6. Could be difficult to trace inter-contract calls
7. Not as easy to upgrade

### Contract Kernel (CK)

In this scheme, contracts and private oracles are not treated as application code; instead both are assumed to have a serializable executable representation. Rather than being stored in the web page, all contracts and private oracles reside in a single datastore guarded by a process, the contract kernel, dedicated to receiving, authorizing, and processing requests to use them. Applications install contracts in the kernel and specify an *access policy*. The access control policy is used to control which other applications can access an installed contract.

**Pros**:

1. Inter-contract calls are reliable
2. Inter-contract calls have a clear semantics
3. Inter-contract calls are fast
4. Inter-contract calls are traceable
5. All private data resides in one location, making it easy to export and inspect, create GUI for inspecting
6. Contract kernel maps cleanly to a single TEE
7. Reduced trusted computing base, all data is guaranteed to be encrypted
8. Structures the system such it can be extended to use remote private computing servers

**Cons**:

1. Not automatically concurrent, serializes contract calls across applications

**Neutral**:
1. Single point of failure / identified and minimized trusted computing base
2. Require a serializable representation for local programs / allow users more flexibility in their implementation languages

## Decision Outcome

Chosen option: Pending

## Validation

* TODO - Unsure of how to validate

<!-- This is an optional element. Feel free to remove. -->
## Pros and Cons of the Options

### Inter-application Messaging

**Security**

Security is preserved by the application mesh, which authorizes inter-contract calls. Similarly to the CK scheme, authorization is managed by a central entity.

**Privacy**

Privacy is preserved because each application has isolated storage and private transcripts are not returned to the calling application.

**Reliability**

The reliability of a contract is now predicated on the reliability of the dapp that hosts the contract and the correctness of the callee contract, rather than just the latter. In particular, this means that the availability of the caller contract (and all functionality that requires it) depends on the availability of the callee contract. Furthermore, fault-tolerance is difficult to achieve, since the application developer must anticipate and recover from errors that result from any interaction the inter-application call causes. This is a much larger error surface area than a direct contract call.

**Usability**

On one hand, embedding contracts and private oracles in the web page requires less setup than the contract kernel approach, since the developer can program both directly. On the other hand, the lack of reliability and performance of the scheme will require significant developer efforts to circumvent.

**Testability**

To test contracts which use inter-application calls, developers would need to mock the application hosting the calle contract. Even after doing so, there would be significant variation between the behavior of the contract in the test and production settings, since the latter depends greatly on the behavior of the hosting application in production.

**Performance**

Proof construction is now performed during the caller contract execution. This means if contract execution fails after the inter-dapp call returns, then significant time has been devoted to creating a proof that is not useful. To combat this, one could include a protocol that queues the intermediate proof and only initiates proving after the outer call has successfully returned, but this further complicates the inter-application call protocol, introducing additional messaging overhead.

If contract calls are frequent and desirable, then the application mesh may regularly experience high message volume, resulting in high latency for inter-application calls.

In a naive approach, inter-application call requests block the main thread of both applications, 
meaning that neither application can perform other important operations, e.g., UI updates based on external events. Application developers may circumvent this various ways, but any solution increases implmentation complexity and therefore decreases usability. Midnight may provide utilities for doing so, but this increases our delivery burden.

**Auditability**

Auditability for inter-contract calls requires care. Each application, in addition to the application mesh, needs intelligence monitoring and logging. It is not necessarily the case that different applications have access to the logs of other applications, so it could be difficult to assemble a coherent record of end-to-end interactions.

**Debuggability**

Debugging contracts becomes difficult for the same reasons that testing becomes difficult. A dedicated debugger for Abcird doesn't seem feasible in this scenario. Identifying the cause of a failure, as in the case of most web applications, must not be achieved by logging.

**Upgradeability**

Since contracts and private oracles are embedded in the web page, updating the behavior of either requires recompiling and redeploying the website. Contrast this to the CK approach, where upgrades can be performed dynamically.

### Contract Kernel

**Security**

Similarly to IAM, authorization is managed by a single entity that resides in the kernel, and each contract is guarded by an access policy specified by the installing application.

Recall the CK approach requires a serializable executable representation of local programs. In the case this representation is WASM, the `WebAssembly` Javascript API allows us fine-grained control over the system functions / external interactions available to transition functions and private oracles. For example, consider the following WASM module,

```wasm
(module
  (func $i (import "imports" "imported_func") (param i32))
  (func (export "exported_func")
    i32.const 42
    call $i))
```
which imports `imported_func` and exports `exported_func`. The only external call available to the module is `imported_func`. Hence, if the module above is analogous to the executable representing a private oracle, the only external interaction the private oracle is capable of would be `imported_func`, which is specified as follows:

```javascript
const importObject = {
  imports: { imported_func: (arg) => console.log(arg) },
};
```

```javascript
const privateOracle = WebAssembly.instantiateStreaming(fetch("private_oracle.wasm"), importObject).then(
  (obj) => obj.instance.exports.exported_func()
);
```

The result is a Javascript object exposing functions that execute WASM functions that are sandboxed. This is a much more controlled approach to third-party script execution, which is essentially what private oracles are, and one of the problems WASM is intended to solve.

**Privacy**

Since all private data resides in a central store, we can guarantee that all private data is appropriately encrypted. Contrast this to IAM, which requires developers to manage their own private data storage and encryption.

**Reliability**

Inter-contract calls are localized to the contract kernel, a single application. For any well-defined contract call to succeed, merely the contract kernel must be available. On the other hand, this means that no application can perform a contract call unless the contract kernel is available, meaning that it must be extremely fault-tolerant. It will become the target of attacks against the user.

**Usability**

Any contract call can be executed by a single call to the contract kernel, requiring no additional application logic besides installation of the contract. Contrast this to IAM, which requires additional application logic for responding to inter-application call requests.

**Testability**

Assuming a standalone contract runtime, which takes appropriate executables and arguments and produces an execution result, contracts that use inter-contract calls can be tested independently of the application using them, since all evaluation logic is localized to the runtime.

**Performance**

It avoids expensive inter-application messaging infrastructure and protocols. But, it will require effort to parallelize independent contract calls, since a naive implementation would process all call requests from all applications sequentially. 

**Auditability**

All events that occur during a call can be captured in a single event log and accessed in a manner consistent with the security policies of the kernel.

**Debuggability**

Assuming a standalone contract runtime, which takes appropriate executables and arguments and produces an execution result, it is feasible to implement a debugger that hooks into the runtime.

**Upgradeability**

The kernel can include facilities for updating the transition function and private oracle executables, so dynamical updates are feasible.

<!-- This is an optional element. Feel free to remove. -->
## More Information


### Inter-application Messaging

The following diagram is a sketch of the component structure of the inter-application messaging approach.

![](../user-flows/contract-interaction/inter-application-messaging/component-diagram/two-contracts-two-apps.svg)

The following scenario is the most general reuse scenario the platform should be able to support. It incorporates both reuse cases described in the [problem statement](./0010-contract-kernel#problem-statement.md) section.

**Scenario 1.0**:
1. Application `B` installs contract `0x02` which defines a transition function `bar`.
2. Application `A` installs contract `0x01` which defines a transition function `foo` that calls `bar`.
3. Application `B` calls `foo`.

The next diagram is a sketch of the behavior of the inter-application messaging approach for scenario (1.0).

![](../user-flows/contract-interaction/inter-application-messaging/sequence-diagram/two-contracts-two-apps.svg)

### Contract Kernel

The following diagram is a sketch of the component structure of the contract kernel approach.

![](../user-flows/contract-interaction/contract-kernel/component-diagram/two-contracts-two-apps.svg)

Likewise, the next diagram is a sketch of the behavior of the contract kernel approach in scenario (1.0).

![](../user-flows/contract-interaction/contract-kernel/sequence-diagram/two-contracts-two-apps.svg)