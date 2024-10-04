---
monofont: DejaVuSansMono
title: "Integrating Compact's Compiler and Language Specification"
author:
  - Cas van der Rest
date:
  - October 4, 2024
output: pdf_document
bibliography: references.bib
fontfamily: merriweather
geometry: margin=4.5cm
header-includes:
  \usepackage{setspace}
  \renewcommand{\baselinestretch}{1.25}
  \usepackage[usenames,dvipsnames]{xcolor}
---

# Integrating Compact's Compiler and Language Specification

This text documents an initiave to integrate Compact's implementation,
the `compactc` compiler, and its specification, written in Agda.

## Goal

The goal is to force synchronization between the implementation and
specification the Compact language. More specificaly, the _version of
the Compact language_ used by the compiler and the specification
should be the same. If the compiler and specification are out of sync,
this should manifest as an error when building the compiler or
type-checking the specification, which can only be fixed by updating
the component that lags behind. Such errors should only be triggerd by
updates to the compiler or spec that change the _definition_ of the
language. 

Bridging the gap between implementation and specification is important
for several reasons. First and foremost, it ensures that the language
specification, as well as any proofs (e.g., type soundness) we develop
on top of the spec, actually pertain to the implementation of the
language that we distribute to users. Furthermore, developing a
mechanism to keep language definitions in sync between the compiler
and specification is an important prerequisite for future application
of formal methods to validate correctness of the compiler w.r.t. the
language specification, through e.g. certifying compilation or
verification of compiler passes performing core translations.
Ultimately, this will increase confidence that the compiler, which
acts as an intermediary between user-facing contract code and the
network, preserves the intended behavior of smart contracts.

## Implementation 

Both the compiler and specification internally maintain a
representation of context-free grammar that defines the languages
syntax. The compiler is developed with the **Nanopass** [@nanopass]
framework, meaning compilation is factored into translations between
different _intermediate representations_ (IRs) that define the
language's syntax. Simultaneously, Agda specifications use _algebraic
data types_ to represent the syntax of programming languages. We can
force synchronization between implementation and specification by
connecting IR definitions in the Nanopass framework to data type
definitions in Agda.

In an ideal setup, data type definitions in Agda and IR definitions in
Nanopass would be derived from a common source, in the spirit of the
**SpecTec** DSL. In this setup, the first step towards updating the
language would be to update this shared definition, which would prompt
both the compiler as well as the specification to be updated.  This
approach, however, would require significant effort, both to develop a
suitable shared representation that includes all non-shared
information that is specific to internal representations of th
compiler/spec, as well as re-engineering of the compiler to use this
shared representation instead of the current internal definitions of
intermediate representations.

Instead, we may consider a more light-weight approach where we
_derive_ a common representation from both the specification and
implementation, which we compare to force synchronization. Such a
derived representation would only include information that is shared
between the compiler and spec, leaving out any addtional internal
information.

On the specification side, we can generate the required JSON output
using a 2 step process, where we first compile data definitions to
Haskell using `agda2hs`, after which we use Haskell's reflection and
`Aeson` library to generate and serialize a description of the data's
shape. A similar pipeline emitting a JSON description of Nanopass IRs
whould have to be engineered on the compier side. 

This JSON representation maintains a list of all syntactic sorts of a
language, together with their constructors and their arguments. As
part of building the compiler/checking the specification, the IR
descriptions should be compared and an error should be raised if the
comparison uncovers any discrepancies. This way, any addition,
deletion, or modification of Compact's syntax in either place that is
not propagated properly will be caught automatically. 

# References 
