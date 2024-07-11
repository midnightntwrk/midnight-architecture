# Proposal 0014: Compact Syntax Changes

This document proposes a batch of changes to Compact's syntax.  They are
designed to make it more like TypeScript, or more pleasant for developers, or
both.

The changes proposed here could each be individually accepted or rejected.

## Problem Statement

In our marketing materials we describe Compact using the phrase "a
TypeScript-based" language or similar ones.  It is a selling that the language
is familiar to developers who can read TypeScript code.  We should also avoid
superficial syntactic differences that will only make it difficult for
developers to switch between the two languages when writing code.

Here we describe a batch of small changes to Compact's syntax.  Some of them
will serve to make it more like TypeScript.  Others will make it more pleasant
for developers.  We include the two kinds of changes together in the same
proposal because we should launch all the accepted ones together to minimize
disruption for developers.

## Proposed Changes

We identify ways in which Compact differs from TypeScript, or else ways that it
does not feel very "TypeScripty".  This latter criterion is obviously
subjective.

### 1. Generic Types and Functions

Both Compact and TypeScript have generic types and functions.  In Compact, there
are builtin generic types like `Unsigned Integer` and `Vector`.  Users can also
define their own generic struct types and generic functions.

In Compact, a generic struct type `Foo` with two type parameters named `T` and
`S` is written using the declaration
`struct Foo[T, S] { ... }`.  When used as a type
annotation, it is instantiated to types by writing, for example,
`Foo[Field, Boolean]`.  Likewise, generic functions are defined and
instantiated using square brackets for type parameters and type arguments.

In contrast, TypeScript uses angle brackets `<` and `>` instead of square
bracketws to enclose generic type parameters and type arguments.

> **We propose to change Compact to use angle brackets for generic definitions and
> instantiations.**

Compact generics can be parameterized over types or natural number values.
Natural number type parameters must be instantiated to literal natural numbers.
Fortunately, this is similar to TypeScript.  There, generics can *only* be
parameterized over types, but a number literal like `32` is actually a type.  It
is the "[literal type](https://www.typescriptlang.org/docs/handbook/2/everyday-types.html#literal-types)"
of number *literals* that are exactly equal to 32.

This change to compact syntax will include builtin types, so developers will
write `Bytes<16>` and `Vector<3, Field>`, for instance.  This also includes
the type `Unsigned Integer`.  Developers will write
`Unsigned Integer<32>`, for instance.

### 2. Default Values of a Type

Every type in Compact, both Compact types and ledger state types, has a
well-defined default value of that type.  The compact syntax for the default
value of a type `Foo` is currently `null(Foo)`.  `null` here is a keyword, not
the name of a function (say, one defined in the standard library).  A
consequence of this is that it is a syntax error use `null` as the name in a
compact definition.

This is a case where we are following TypeScript but going down the wrong path.
The default value of a Compact type does not correspond to the TypeScript value
`null`.  TypeScript types are generally non-nullable, unless they are in a union
type with the type `null`, like `Foo | null`; or if `strictNullChecks`, which is
enabled by default, is disabled in the TypeScript config file.

Even if we described Compact types as always being implicitly in a union with
`null` (note that Compact does not currently have union types), it is still not
quite right to use `null` for default values in Compact.  The default value of a
natural number type is the number zero, for instance, which is a distictly
different value from the `null` value in TypeScript.

> **We propose to use the keyword `default` instead of `null` for default values
> of a type.**

This is the
[syntax used in C#](https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/operators/default#default-operator)
for the same concept.

Note that Go has a similar concept ("zero values" of a type, which are not
necessarily zero).  However, there is no explicit syntax in Go for getting the
zero value of a type argument `Foo`, because generics were added only recently to
the language.  Programmers
[have settled on](https://stackoverflow.com/questions/70585852/return-default-value-for-generic-type/70589302#70589302)
writing `*new(Foo)` as the best alternative, which definitely does not feel like
TypeScript.

We note that `default(Foo)` looks like a call to a circuit or witness passing
the argument `Foo` (a type).  However, this suggests that types in Compact are
first-class values (they are not) which might be misleading to a developer.

> **We propose (separately) to use angle brackets for the type argument to the
> keyword used for getting the default value of a type.**

So, for instance, if we adopt both of these proposals a developer would write
`default<Foo>` and could view the `default` keyword as a sort of builtin generic
value.

### 3. Unsigned Integer Types

Compact has bounded unsigned integer types that can be written, for example,
`Unsigned Integer[<= 4294967296]` or equivalently
`Unsigned Integer[32]`.  These are very verbose to use in practice.  For
instance, a simple non-exported circuit that adds two numbers might be:

```
circuit add(m: Unsigned Integer[8], n: Unsigned Integer[8]): Unsigned Integer[9] {
  return m + n;
}
```

It is tempting to think of this as the modifier `Unsigned` affecting the type
`Integer`, but it's not.  In Compact, `Unsigned` is not currently a modifier and
`Integer` is not currently a type.  Rather, this is a single builtin type that
is spelled with a space.  This is unusual: most languages use a space character
as a delimiter between tokens.

Consequently, we might have difficulty with some developer tooling.  For
instance, a simple implementation of completion might see `Unsigned` and
`Integer` as two separate completions, requiring a programmer to type "`U`,
tab, space, `I`, tab" to complete the type name.

So we think it's desirable to use a shorter name for this type, and to make it a
single keyword.

> **We propose to use the keyword `UInt` for the unsigned integer type.**

We are following the convention that types are capitalized, even builtin ones.
They use CamelCase, and `U` and `Int` are "obvious" abbreviations in this case.

There was an earlier proposal to keep the longer names, but to introduce type
aliases to the language so that programmers could define their own short alias
if they wanted.  A convenient alias for `Unsigned Integer` could even be defined
in the standard library.  While type aliases is a useful feature that we should
add, it's not the best solution to this problem.

First, it would require us to work out how to make generic type aliases that
could be instantiated to a type argument like `<= 4294967296`.

Second, we would have to be careful to signal type errors both in terms of the
written type (maybe an alias) and the underlying (non-aliased) type.  This is
generally a problem with type aliases, but we should probably avoid doing it for
core parts of the language.

### 4. `map` and `fold`

Compact has keywords `map` and `fold` for the usual higher-order functions *map*
and *fold* (left) over, in Compact's case, vectors.  They use an infix keyword
`over` which is repeated when mapping or folding over multiple arguments.  So
for instance, to map the `add` function above over a pair of vectors `v0` and
`v1`, we would write: `map add over v0 over v1`.  Likewise, to fold this
function over `v0` using the initial value `0` (zero), we would write:
`fold add 0 over v1`.

Neither of these feels very much like TypeScript, where these would be defined
as higher-order functions, or else methods (possibly static ones) on an
appropriate class.  For instance, in TypeScript (and if `v0` and `v1` were
arrays), the equivalents would be `v0.map(add, v1)` (though, note,
`Array.prototype.map` only works for single argument functions) and
`v0.reduce(add, 0)`.

Proposals: [TODO: select one of these and describe it.

* `map add(v0, v1)` and `fold add(0, v0)`: they are unary prefx operators that
  have higher precedence than circuit/witness application.

* `add.map(v0, v1)` and `add.fold(0, v0)`: they are "methods" on circuits. 

* `v0.map(add, v1)` and `v0.fold(add, 0)`: they are methods on vectors.  This
  closely matches TypeScript.

There's probably only a small number of such combinators that we will need to
provide, but there might be others than these two.  The second and third
proposals above mean that adding more of them is not a breaking change.]

## Proposed Rollout Plan

[TODO: Describe how we plan to communicate these changes to developers, and how
we will roll them out.  We need to reach developers, and clearly explain why we
are making these changes and asking them to change their code.  Though these are
breaking changes, we might choose to just change the syntax rather than (1)
deprecate the old one and introduce the new oen and then (2) later remove the
old one.  Note also that we have to update documentation, example DApps, and
tests at the same time.  These changes (along with the ledger syntax changes,
which possibly needs identifier renaming) could be performed by an automated
tool that we could build and distribute.]

## Desired Result
[TODO: Finally, describe what you hope to achieve and how you can evaluate that you
have achieved it.]
