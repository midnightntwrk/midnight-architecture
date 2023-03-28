# Proposal 0009: Programmable Preconditions

This proposal is an elaboration of the [maximally programmable validation](../proposals/0003-public-oracle-language.md#maximally-programmable-v) alternative to ADTs. It draws on Cardano's [two-phase transaction validation](https://iohk.io/en/blog/posts/2021/09/07/no-surprises-transaction-validation-part-2/) process.

## Problem Statement

The general dynamic of transaction processing on Midnight involves the following steps.

1. Verify the transaction is constructed correctly.
2. Execute the transaction.

In the execution model of the public oracle language introduced in [ADR-0005](./0005-public-oracle-language-direction.md), transcript application is used to perform step two. All public oracle queries are assumed to be efficient enough that the node does not need to charge the user for compute, so [fairness](../proposals/0003-public-oracle-language.md#desired-properties-of-transactions) is preserved.

The above approach produces a public oracle language that is highly restrictive and dissimilar to any well-known programming paradigm. It also compels contract developers to use private oracles or circuits for iterative computations. The latter situation incurs a significant performance penalty due to increased circuit size and proving complexity. Furthermore, a public oracle language without function definitions lacks all of the traditional benefits of a language that supports them, code reuse in particular.

# Correctness Conditions

In addition to [these](../proposals/0003-public-oracle-language.md#desired-properties-of-transactions) five properties, the public oracle language should have the following properties.

* Usability - it should resemble a well-known programming paradigm
* Leveragability - it should should enable reusing public computations (functions)
* Expressability - it should should provide a non-circuit and non-private oracle mechanism for iterative computation (loops/folds)

# Solution

Building on [maximally programmable validation](../proposals/0003-public-oracle-language.md#maximally-programmable-v) alternative, introduce a public oracle language $\mathcal{L}_{pub}$ that supports function definitions and iterative computation. The precise language constructs are less relevant than the properties of the language itself. For example, rather than specifying whether $\mathcal{L}_{pub}$ provides looping or folding constructs, we require that it be decidable. In theory, it could even be identical to the existing Abcird circuit language. At a minimum, $\mathcal{L}_{pub}$ should provide:

* variable binding
* iteration/folding
* function definitions
* common data structures

 An example $\mathcal{L}_{pub}$ program is the following. Public variables and definitions are identified by the `statement` keyword. Variable declarations behave similarly to those in C++.

```rust
enum State {
  waiting
  started
  ended
}

statement tree: MerkleTree[4, Field]

witness secret_vec: Vector[10, Field]

statement state: State

statement x: Field = 10

statement foo (vec: Vector[10, Field]): Vector[10, Field] {
  if (state is State.waiting) {
    state = State.started
  } else return map(vec, i => i + 1)
}

circuit bar (z: Field): Vector[2, Field] { 
  x += z;
  return foo(secret_vec)
}

statement initialize () {
  state = State.waiting
  tree = MerkleTree.empty
}
```

Of course, transactions using $\mathcal{L}_{pub}$ may again suffer from issues of contention and transaction indeterminism. Therefore, contract authors must be able to state precisely when a transaction is applicable. Furthermore, said applicability check should be efficient enough to not pose DoS risks for nodes. Taking inspiration from TLA+ (please read [this](https://lamport.azurewebsites.net/pubs/state-machine.pdf)) $\mathcal{L}_{pub}$ would also provide a state-predicate construct. For the previous example, a state-predicate might be.

```rust
precond is_started (): Boolean {
  return state == State.started && !tree.is_full()
}
```

A call transaction would include an optional `precond` field that indicates whether and which defined state-predicate should serve as the applicability check. When the precondition succeeds, the transaction should be applied, and the user is charged for any subsequent computation. Naturally, the precondition language must be limited to a set of known predicates like equality checks and built-in data structure operations such as `is_full`. In particular, `statement` definitions cannot be used in preconditions. Notice that `statement` definitions cannot access `witness` definitions directly. Private values must be passed to `statement` definitions as parameters.

# Proof of Correctness

The language $\mathcal{L}_{pub}$ has constructs for reusing public computation (functions) and public iterative computation (loop/fold/map). It also has a construction that allows contract authors fine-grain control over the conditions in which a transaction is applied, thus giving them a tool to manage indeterminism. Furthermore, transcripts serve a single purpose rather than dual purposes, and the programming model resembles a procedural paradigm.

The compressability property of $\mathcal{L}_{pub}$ needs to be explored.