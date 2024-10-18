# Proposal 0014: Functional Structure Update Syntax

## Problem Statement

Compact values of structure and vector type are immutable.  Instead of mutating
an existing value, developers create a new one with some of the fields or
elements updated.  This can be awkward to write for `struct`s with more than a
few fields or vectors with more than a few elements.  It can be difficult to
read in order to identify exactly which fields or elements are changed and which
ones are unchanged.

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
allow it in a new "`struct` creation" expression and in vector creation
expressions, but not in (yet) other places where it might be potentially useful
(e.g., circuit and witness arguments).

## Syntax

For structure creation, we introduce `struct` creation expressions as a _term_
production, at the same level in the grammar as structure construction (`new`)
expressions and vector creation expressions.  The elements of the `struct`
creation are an optional spread expression and zero or more comma-separated
named expressions.

For vector creation, we modify the grammar so that the subparts can include
spread expressions.

<table>
  <tr>
    <td><em>term</em></td>
	<td>&rarr;</td>
	<td><em>tref</em> <b><tt>{</tt></b> <b><tt>...</tt></b> <em>expr</em> {<b><tt>,</tt></b> <em>struct-field</em>} <b><tt>}</b></tt></td>
  </tr>
  <tr>
    <td></td>
    <td>&rarr;</td>
	<td><em>tref</em> <b><tt>{</tt></b> [<em>struct-field</em> {<b><tt>,</tt></b> <em>struct-field</em>}] <b><tt>}</b></tt></td>
  </tr>
  <tr>
    <td></td>
    <td>&rarr;</td>
    <td><b><tt>[</tt></b> [<em>vector-element</em> {<b><tt>,</tt></b> <em>vector-element</em>}] <b><tt>]</tt></b></td>
  </tr>
  <tr></tr>
  <tr>
    <td><em>struct-field</em></td>
	<td>&rarr;</td>
	<td><em>id</em> <b><tt>:</tt></b> <em>expr</em></td>
  </tr>
  <tr></tr>
  <tr>
    <td><em>vector-element</em></td>
	<td>&rarr;</td>
	<td><b><tt>...</tt></b> <em>expr</em>
  </tr>
  <tr>
    <td></td>
	<td>&rarr;</td>
	<td><em>expr</em></td>
  </tr>
</table>

**Notes:**

* The type of a `struct` creation is needed, unlike JavaScript object literals,
  so that we know the type of the `struct` being constructed.
  
* Generic `struct` creation expressions require type arguments.  The grammar for
  _tref_ allows optional type arguments.
  
* **The grammar makes it syntax error for a `struct` creation expression to have
  more than one spread expression**.  There is no `struct` subtyping in Compact
  (yet), so a spread subexpression is expected to have exactly the same fields
  as the struct being constructed.  Therefore, any subsequent spread
  subexpression would completely hide (or overwrite) the fields of a previous
  one.  For that reason, it's never necessary to have more than one.
  
* The spread expression must appear first in the `struct` creation.  If it
  occured in other positions, it would overwrite previous fields.  This renders
  those previous fields useless (other than their side effects) and is probably
  not what the programmer intended.
  
* We allow the other fields to appear in any order in a `struct` creation.
  Since they are named, there is never any ambiguity about which `struct` field
  they are.
  
* Vector creation expressions can have spread subexpressions.  Here it does make
  sense to allow multiple spread expressions, because they can be used to
  construct a larger vector.

## Static Typing

The static type checking rules are as follows:

* The static type of the spread subexpression in a `struct` creation must be
  (exactly) the same type as the type of the struct being constructed.  It is a
  static type error otherwise.
  
* It is a static type error if a generic `struct` type is constructed without
  fully supplying type arguments.  Additionally, the type arguments have to have
  the correct kind (a type or a size) for the corresponding parameter of the
  corresponding generic `struct` declaration.
  
* It is a static type error if a field name appears as a name in the list of
  *struct-field*s but is not a name of a field in the corresponding `struct`
  definition.
  
* It is a static type error if a field name appears more than once as a name in
  the list of *struct-field*s.
  
* If there is no spread subexpression in a `struct` creation, it is a static
  error if the list of *struct-field*s does not include all the fields in the
  corresponding `struct` definition.  We rejected an alternative where struct
  fields were initialized to the default value of their type.  If a programmer
  desires such initialization, they can achieve it with a spread: `Foo {
  ...default<Foo>, x: e0, y: e1 }`
  
* It is a static type error if the type of an expression in _id_:_expr_ in the
  list of _struct-field_s is not a subtype of the corresponding field type in
  the corresponding `struct` definition.  Note that the type of a generic
  `struct` is instantiated to the type arguments (i.e., a non-generic type).
  
* The type of an entire `struct` creation is the `struct` type, instantiated to
  type arguments if generic.
  
* It is a static type error if the spread expressions in a vector creation do
  not all have vector types.
  
* The static type of a vector literal is a vector whose length is the sum of the
  lengths of all the spread vector types and the number of non-spread elements,
  and whose element type is the least upper bound of the element types of all
  the spread vector types and the types of the non-spread elements.  It is a
  static type error if this least upper bound does not exist or if it is `Void`.

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
  
Evaluation of a vector literal expression proceeds as follows.  The
subexpressions are evaluated from left to right.  A value of the appropriate
vector type is allocated.  The vector elements are initialized in order from
left to right.  A spread expression will initialize a range of vector elements
equal in number to the length of the spread vector.  A non-spread subexpression
will initialize a single vector element.
  
## Possible Further Changes

We can remove the `new Foo` structure creation syntax, as it is redundant.  This
is a breaking change.

Spreading a vector or structure value as (some of) the arguments to a circuit or
witness call is also potentially useful, but it's more subtle.  We don't propose
that as a possible extension (yet).  One issue is to decide whether the names of
struct fields have any effect in a call like `foo(...bar)` where `bar` has
`struct` type.
