# Proposal 0014: Functional Structure Update Syntax

## Problem Statement

Compact values of structure type are immutable.  Instead of mutating an existing
`struct` value, developers create a new one with some of the fields updated.
This can be awkward to write for `struct`s with more than a few fields.  It can
be difficult to read to identify exactly which fields are changed and which ones
are unchanged.

## Proposed Changes

We will introduce syntax to Compact for functional update.  The syntax is based
on the "spread" (`...`) operator from JavaScript and TypeScript.  Instead of
writing, for example:

```
new Foo(foo.a, foo.b, foo.c, d, foo.e, f, foo.g, foo.h)
```

the programmer can write, for example:

```
Foo { ...foo, d: d, f: f }
```

The ellipsis (`...`) is the JavaScript spread (prefix) operator.  We propose to
allow it in a new "`struct` literal" expression, but not in (yet) other places
where it might be potentially useful (e.g., vector construction expressions,
circuit and witness arguments).

## Syntax

We introduce `struct` literal expressions as a _term_ production, at the same
level in the grammar as structure and vector construction expressions.  The
elements of the `struct` literal are zero or more comma-separated
_struct-field_s, which can be named expressions or spread expressions.

<table>
  <tr>
    <td><em>term</em></td>
	<td>&rarr;</td>
	<td><em>tref</em> <b><tt>{</tt></b> [<em>struct-field</em> {<b><tt>,</tt></b> <em>struct-field</em>}] <b><tt>}</b></tt></td>
  </tr>
  <tr></tr>
  <tr>
    <td><em>struct-field</em></td>
	<td>&rarr;</td>
	<td><em>id</em> <b><tt>:</tt></b> <em>expr</em></td>
  </tr>
  <tr>
    <td></td>
	<td>&rarr;</td>
	<td><b><tt>...</tt></b> <em>expr</em>
  </tr>
</table>

* The name of the `struct` is needed, unlike JavaScript object literals, so that
  we know the type of the `struct` being constructed.
  
* Generic `struct` literals require type arguments.  The grammar for _tref_
  allows optional type arguments.
  
* **It is a syntax error for a `struct` literal expression to have more than one
  spread _struct-field_**.  There is no `struct` subtyping in Compact (yet), so
  a spread subexpression is expected to have exactly the same fields as the
  struct being constructed.  Therefore, any subsequent spread subexpression
  would completely hide (or overwrite) the fields of a previous one.  For that
  reason, it's never necessary to have more than one.
  
* We allow the spread subexpression to appear anywhere in the list of
  _struct-field_s.  A programmer is allowed to put it wherever they find most
  understandable.  This implies that detecting multiple spread subexpressions
  happens in a pass after parsing.  A possible alternative would be to require
  it in a designated place like first or last in the list, which is not what we
  are proposing here.
  
* We allow the other fields to appear in any order.  Since they are named, there
  is never any ambiguity about which `struct` field they are.

## Static Typing

The static type checking rules are as follows:

* The static type of the spread subexpression must be (exactly) the same type as
  the type of the struct being constructed.  It is a static type error
  otherwise.
  
* It is a static type error if a generic `struct` type is constructed without
  fully supplying type arguments.  Additionally, the type arguments have to have
  the correct kind (a type or a size) for the corresponding parameter of the
  corresponding generic `struct` declaration.
  
* It is a static type error if a field name appears as a name in _id_:_expr_ in
  the list of _struct-field_s but is not a name of a field in the corresponding
  `struct` definition.
  
* It is a static type error if the type of an expression in _id_:_expr_ in the
  list of _struct-field_s is not a subtype of the corresponding field type in
  the corresponding `struct` definition.  Note that the type of a generic
  `struct` is instantiated to the type arguments (i.e., a non-generic type).
  
* The type of the entire expression is the `struct` type, instantiated to type
  arguments if generic.

## Evaluation

Evaluation of a `struct` literal expression proceeds as follows.  The
subexpressions are evaluated from left to right (i.e., in source text order).  A
value of the appropriate `struct` type is allocated.  For each field in the
struct, its value is initialized to be the value of the corresponding named
expression (if there is one) or else the value of the corresponding field in the
spread struct value.

**Notes:**

* Every field in the result will be initialized if evaluation of the expression
  succeeds.  There is either a named field in the struct literal, or else the
  field is present in the spread `struct` value because it has the same type as
  the result.
  
* The allocation of the result `struct` is generally unobservable.  A developer
  could potentially observe it by observing that the allocation occurred either
  before or after some side effect (including a runtime error) of one of the
  subexpressions.  We should probably specify it as happening before evaluating
  any subexpression or after evaluating all of them, but this proposal considers
  it an implementation decision.
  
* The order that fields are initialized is generally unobservable.  There is no
  way in Compact to use a `struct` literal value until after it is fully
  initialized.
  
## Possible Further Changes

This syntax is convenient.  It parallels vector (literal) construction
expressions.  That suggests two other changes we could consider making.

**`struct` literals are allowed to have zero or one spread subexpression.**
This would allow `struct` literals to construct `struct` values without being
based on an existing value.

If we allow this, we should require that all the `struct` fields are present in
the `struct` literal.  This ensures that if a field is added to a struct, there
will be a compile-time error if one of the construction sites is not updated to
initialize the new field.

An alternative would be to allow fields to be left out of `struct` literals, and
instead have them be initialized to the default value of thier type.  We
rejected that, because the interaction with default field initialization and
potential future `struct` subtyping seems subtle and error prone.

Developers who want such default initialization can do it explicitly with, for
example, `Foo { ...default<Foo>, x: e0, y: e1 }` or by defining a pure helper
circuit to construct a `struct` value that is partially constructed with default
field values.

If we choose this, we could even remove the `new Foo` structure construction
syntax, as it is redundant.

**`vector` literals can have spread subexpressions.**  The idea would be that a
vector (with the same or fewer elements) could be spread into a vector
construction expression.  Here it would make sense to allow multiple spread
subexpressions.  For example, `[foo, ...bar, baz]` is like `bar` with two extra
elements.  `[...foo, ...bar]` is a new vector that is like the concatenation of
a pair of existing ones.  `[...foo]` is a copy of an existing vector.

## Conclusion

None of these are breaking changes except removing the existing `new` syntax for
`struct` construction.

Spreading a vector or structure value as (some of) the arguments to a circuit or
witness call is also potentially useful, but it's more subtle.  We don't propose
that as a possible extension (yet).  One issue is to decide whether the names of
struct fields have any effect in a call like `foo(...bar)` where `bar` has
`struct` type.
