# Midnight formal methods 

This folder documents initial explorations into applying formal methods within
the midnight project. 

`src/Impact.agda` contains an exploratory formalization of the on-chain runtime,
based on the documentation
[here](https://github.com/input-output-hk/midnight-architecture/tree/main/apis-and-common-types/onchain-runtime). 

## Thoughts 

As a first approximation, sequences of transcript bytecode are given a semantics
in terms of Kleisli arrows of a cost-graded monad. In broad strokes, this means
that a bytecode sequence is interpreted as a function `Stack → M c Stack`,
describing its effect on the stack, where `c` is the cost of running the
computation, and any side-effects or interaction with the ledger are modelled by
the monad `M`.

This model gives a for how to create suitable abstraction barriers between
specification/formalization of the ledger, on-chain runtime, and smart
contracts. Since `M` is to be kept abstract, all interaction with the ledger
proceeds through an abstract interface, where the intended behaviour of these
interactions is specified in terms of algebraic theories over this interface. A
formalization of the ledger should _inhabit_ this specification, by giving an
implementation that conforms to `M`s interface and laws.

