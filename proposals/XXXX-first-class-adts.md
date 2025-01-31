# Proposal XXXX: Compact First-class ADTs

**Overview**: we describe a Compact source-to-source translation that implements
a feature which we have been calling "first-class ADTs".

In Compact, there are two different kinds of types:

- **Compact types**, which can be used as the types of parameters, return types,
  local `const` declarations, `struct` field types, and as type arguments in
  generic Compact type and ledger ADT type instantiations, and

- **ledger ADT types**, which can appear as the type of ledger fields in
  `ledger` declarations and which can appear as the value type in ledger `Map`
  ADT types.

The translation allows ledger ADT types to appear in all the same places that
Compact types can.  Ledger ADT-typed expressions can be used as values of ledger
ADT type.  (The current restriction in Compact is that expressions with ledger
ADT types can only appear as the ADT subexpression in an ADT operation
invocation, this translation removes that restriction.)

The Compact value of a ledger ADT-typed expression is a "reference" to the
ledger ADT.  These are full first-class values: they can be passed as arguments
to circuits and witnesses, returned from circuits and witnesses, bound to
constants, and stored in Compact data structures like `struct`s and tuples.

The insight underlying the source-to-source translation is the only place (other
than as ledger-field types themselves) where ledger ADT types can currently
appear is as the value type in ledger `Map` ADTs.  This allows us to allocate
ledger ADTs in a heap (in the sense of a mutable memory, not the heap data
structure) which is a map in the ledger.

The value of a ledger ADT-typed expression is the key associated with the ledger
ADT in the heap.  This acts as a reference to the ledger ADT.  Because it's a
Compact value, it is fully first-class.  When an ADT operation is applied to a
value of ledger ADT type, there is implicitly a dereferenced via a lookup in the
heap corresponding to the type.

## The Source Language

Because Compact does not currently have first-class ADTs, calls to `read` on
ledger `Cell` types are implicit, and assignment expressions are used as
shorthand for calls to `write` on ledger `Cell`s.  In the presence of
first-class ADTs these will be ambiguous.  For this reason we consider a source
language where ledger `Cell` reads and writes are explicit (in the form of calls
to the `read` and `write` operations).  For clarity, we use a fully
type-annotated source language in examples, though this is not necessary.

The source language is then extended so that ledger ADT types are Compact types
and can appear wherever Compact types can appear in the language.  Expressions
with ledger ADT types can appear anywhere (not just as the ADT subexpression in
a ledger ADT operation expression).

## Collecting First-class Ledger ADT Types

For the transformation, we need to collect the first-class ledger ADT types that
are actually used in the input Compact program.  A ledger ADT type is used as a
first-class type if it appears anywhere that it currently cannot appear: i.e.,
as a subterm of a Compact type (including the type itself) in a type annotation.
Type annotations occur for parameters, for return types, for local `const`
declarations, as `struct` field types, and as type arguments in generic Compact
type and ledger ADT type instantiations.  Recall that we are considering a fully
type-annotated source language.

There will be a bounded number of such types in a Compact program and we can
traverse the program to collect the set of them, which is used as input to the
transformation.

## The Translation

There is a translation on types, a translation on `ledger` declarations and the
constructor, and a translation on expressions.  We describe each of them below.

### Types

The translation `type[[_]]` operates on Compact and ledger ADT types.

If the type is a first-class ledger ADT type in the collected set, it is
replaced with `Addr`, which is a builtin Compact type we have introduced for the
purpose.  It is a Compact type which can be used as a `Map` key and which is
"big enough" in the sense of having enough values to represent many values of a
given type.  This is not a type which is available to the user.

Otherwise, the type is the same type with the subterms translated by
`type[[_]]`.

### Ledger

We add a heap ledger field per type in the collected set.  For a type `T`, we
will write this field with name `heap_T`, e.g., for `Cell<Field>` we will write
`heap_Cell<Field>` even though this is not a valid Compact identifier that a
programmer could write.

The type of this field is `Map<Addr, type[[T]]>`.  That is, the value type is
translated using the type translation described above.

We need the ability to allocate keys for these maps.  We assume a nullary
generic ledger kernel operation `allocate`,
e.g. `kernel.allocate<Cell<Field>>()` will return a value of type `Addr`.

If there is no constructor, we introduce one.  In the constructor, before any
other code, we add allocation and initialization for all the ledger fields with
first-class ledger ADT types (i.e., types in the collected set which are `Addr`
after the translation).  For a field `f` and type `T`, we introduce a fresh
identifier `a` and add the statements:

```
const a: Addr = kernel.allocate<T>();
f.write(a);
heap_T.insert(a, default<T>);
```

### Expressions

The translation `expr[[_]]` operates on Compact expressions looking for ledger
ADT operation invocations and translating the implicit dereference of the ledger
ADT value into an explicit one.  We write `expr*[[_]]` to indicate mapping this
translation over a sequence of expressions.

The translation recurs into expressions, simply translating the subterms using
`expr[[_]]` itself with the exceptions below:

- When it encounters a ledger ADT field reference to a field named `f` and where
  the field type is in the collected set, it produces `f.read()`.

- When it encounters a ledger ADT operation (i.e., an expression of the form
  `e.op(e*,...)` where the type `T` of `e` is in the collected set and `op` is
  an ADT operation) it produces `heap_T.lookup(expr[[e]]).op(expr*[[e*]],...)`.

## Examples

Here is a program in the source language which swaps the values in a pair of
ledger cells:

```
import CompactStandardLibrary;

ledger cell0: Field;
ledger cell1: Field;

circuit swap(c0: Cell<Field>, c1: Cell<Field>): [] {
  const tmp: Field = c0.read();
  c0.write(c1.read());
  c1.write(tmp);
}

export circuit test(): [Field, Field, Field] {
  const c: Cell<Field> = cell0;
  swap(c, cell1);
  return [cell0.read(), cell1.read(), c.read()];
}
```

The collected set for this program is {`Cell<Field>`}.  In `ledger cell0: Field`
the type is implicitly `Cell<Field>`.

Applying the translation defined above yields:

```
import CompactStandardLibrary;

ledger cell0: Addr;
ledger cell1: Addr;

ledger heap_Cell<Field>: Map<Addr, Cell<Field>>;

constructor() {
  const a0: Addr = kernel.allocate<Cell<Field>>();
  cell0.write(a0);
  heap_Cell<Field>.insert(a0, default<Cell<Field>>);
  
  const a1: Addr = kernel.allocate<Cell<Field>>();
  cell1.write(a1);
  heap_Cell<Field>.insert(a1, default<Cell<Field>>);
}

circuit swap(c0: Addr, c1: Addr): [] {
  const tmp: Field = heap_Cell<Field>.lookup(c0).read();
  heap_Cell<Field>.lookup(c0).write(heap_Cell<Field>.lookup(c1).read());
  heap_Cell<Field>.lookup(c1).write(tmp);
}

export circuit test(): [Field, Field, Field] {
  const c: Addr = cell0.read();
  swap(c, cell1.read());
  return [heap_Cell<Field>lookup(cell0.read()).read(),
          heap_Cell<Field>lookup(cell1.read()).read(),
		  heap_Cell<Field>lookup(c).read()];
```

If `cell0` contains 0 and `cell1` contains 1 and we invoke `test`, the result
will be `[1,0,1]`, illustrating that the reference `c` is an alias to the
reference `cell0` (they are the same heap map key).
