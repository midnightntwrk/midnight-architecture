# Compact Syntax Changes

## Status

proposed

---
| -         | -                                                                        |
|-----------|--------------------------------------------------------------------------|
| date      | 2024-08-13                                                               |
| deciders  | Kevin Millikin                                                           |
| consulted | Joseph Denman, Kent Dybvig, Thomas Kerber, Andrzej Kopeć, Jonathan Sobel |
| informed  | -                                                                        |
---

## Context and Problem Statement

Compact is marketed as "TypeScript-inspired" or "TypeScript-based".  There are
several good reasons to make the language like TypeScript:

* Developers who are used to reading TypeScript will find it easy to read
  Compact code.

* Developers who write both Compact and TypeScript code will find low friction
  from switching between the two languages.

* As the language designers, it gives us a guide for syntactic decisions that
  are somewhat arbitrary.

The current Compact language (version 0.8.1) has some differences from
TypeScript and some features that don't feel very "TypeScripty", which we've
decided to change.  We list all those features here, rather than making them
into separate ADRs.

## Overview of the Changes

Here is a quick summary of the changes we will make:

* `Foo[Bar, Baz]` becomes `Foo<Bar, Baz>`
* `null(Foo)` becomes `default<Foo>`
* `map add over v0 over v1` becomes `map(add, v0, v1)`
* `Unsigned Integer[32]` becomes `Unsigned<32>`

## Generics

Compact has generic types and circuits.  Generic types are structure types,
which can be user defined, and also builtin types like `Unsigned Integer`,
`Vector`, `Bytes`, `Opaque`.  Compact uses square brackets for generics, both
for their definition and for their instantiation.  For example, `Foo[Bar, Baz]`.

TypeScript also has generics, but they use angle brackets.  In TypeScript, we
would have `Foo<Bar, Baz>`.

### Considered Options

* No change to Compact
* Angle brackets: `Foo<Bar, Baz>`, `Opaque<'string'>`, `Vector<3, Field>`,
  `Unsigned Integer<<= 99>`
* "Curried" generics where natural number and string (and possible less than or
  equal bounds) are in square brackets: `Vector[3]<Field>` or else
  `Vector<Field>[3]`
  
The "curried" options were considered because we would like to distinguish between
parameters that are types, versus those that are natural numbers, strings, or
something else.  There are several reasons to distinguish these:

* Non-type structure parameters do not appear in the corresponding TypeScript
  type.  For unused type parameters, the compiler has to make an arbitrary
  choice to include or exclude them.

* Some generic structure definitions have a type error where there is no
  possible correct instantiation.  It's complicated to signal these errors at
  the definition, and the compiler currently signals them at each instantiation
  site.  This is awkward.  For instance, a library writer does not get a type
  error, but the library users do.

* A developer has to read the implementation of a structure to see whether a
  generic argument should be a type or not, and this can involve reading all the
  definitions of structures used in the implementation, and so on.

### Decision Outcome

We've chosen to use TypeScript-style angle brackets everywhere.

Developers can update their code by replacing the square brackets on generic
definitions and instantiations to use angle brackets.  This change could be
automated.

We've decided to make two additional changes to generics:

* In structure definitions, natural number parameters are indicated by prefixing
  the name with the number sign (`#`).  This is used at the definition, but not
  in the instantiation.  So for instance, the definition of a structure might be
  `struct Foo<#n, T> {...}` to indicate that the first parameter is a natural
  number.  It would be instantiated like `Foo<3, Field>`.
  
* Bounded unsigned integer types, currently written with a less than sign, like
  `Unsigned Integer<<= 99>` will change.  The double angle brackets look a
  little weird and the angle brackets are no longer balanced, so simple tools
  will have to be more complicated to handle this case.  Instead, we will write
  this as a closed interval using the token `..` to separate the upper and lower
  bounds.  Currently, lower bounds are always zero.  So the developer will
  instead write `Unsigned Integer<0..99>` to mean an unsigned integer with lower
  bound 0 and upper bound 99, both inclusive.
  
## Default values

Compact has a well-defined default value of every type.  The default value of a
type `Foo` is written `null(Foo)`.

This is distinctly different from `null` in TypeScript.  In TypeScript today,
types are non-nullable by default, so `null` isn't even necessarily a value of a
given type.

It also looks misleadingly like a circuit or witness invocation, passing the
type `Foo` as an argument.  Compact types are not first-class values, so this is
not a circuit or witness that a user could write.

### Considered Options

* No change to Compact
* Use a keyword like `default` or `empty`

### Decision Outcome

We will change Compact's default values to use the keyword `default` (like in
C#) instead of `null`.  We will also change them to look like a generic
instantiation by using angle brackets.

Developers can update their code by changing `null(Foo)` to `default<Foo>`.
This change could be automated.

## `map` and `fold`

Compact has `map` and `fold` to apply a circuit or witness to each element of a
vector in turn.  They allow multiple vector arguments.  For instance, a two
argument circuit can be mapped over two vectors (of the same length).

The compact syntax for this is `map add over v0 over v1` where `map` and `over`
are keywords, `add` is the circuit or witness (which could also be a circuit
literal, defined inline), and `v0` and `v1` are the arguments.

This does not feel very TypeScripty.  In TypeScript there are no keywords like
`map` and `fold` and infix keywords like `over` are unusual.  The TypeScript
equivalent would be the methods `map` and `fold` which are defined for data
structures like `Array`.  The developer would write `v0.map(add, v1)`.

### Considered Options

* No change to Compact
* Make `map` and `fold` into prefix unary operators with higher precedence than
  circuit/witness application.  The developer would write `map add(v0, v1)`.
* Same as above, but with lower precedence than application.  The developer
  would write `(map add)(v0, v1)`.  Note that `map add` is still not (yet) a
  first-class value with this option.
* Make `map` and `fold` syntactically into "methods" on circuits and witnesses.
  The developer would write `add.map(v0, v1)`.
* Make `map` and `fold` syntactically into "methods" on vectors.  The developer
  would write `v0.map(add, v1)`.
* Make `map` and `fold` syntactially into top-level builtin functions.  The
  developer would write `map(add, v0, v1)`.
  
### Decision Outcome

We have decided to adopt the last of these options: `map` and `fold` will
syntactically appear as top-level functions.  They are still builtin (not, for
example, defined in the standard library) and still treated as keywords for now.

Developers can update their code by changing `map f over v` to `map(f, v)` and
likewise for multiple vector arguments.  They can change `fold f i over v` to
`fold(f, i, v)`.

## Unsigned integer types

Compact writes `Unsigned Integer[32]` for a sized unsigned integer type (holding
values that can fit in 32 bits in this case) and `Unsigned Integer[<= 99]` for a
bounded unsigned integer type (holding values in the closed interval [0, 99]).

In this case `Unsigned` is not actually a modifier, but part of the name of the
type.  The name of the type is two words separated by a space.

This makes simple code completion difficult, and is verbose and awkward to read
in practice.

### Considered Options

* No change to Compact
* Use just `Unsigned` instead of `Unsigned Integer`
* Use the abbreviation `UInt`

### Decision Outcome

We will adopt the second of these options, replacing `Unsigned Integer` with
`Unsigned`.  Compact doesn't currently use abbreviations in its builtin types,
so we opted against the second of these.  (Note however, that Compact does
abbreviate the keywords `struct` and `enum`.)

Developers can update their code by changing `Unsigned Integer` to `Unsigned`.

## Validation

We will update our compiler tests and example DApps to use the new syntax, and
verify that they all compile and run exactly as before (except for the printing
of types in error messages).
