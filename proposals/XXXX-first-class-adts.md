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
value of ledger ADT type, there is implicitly a dereference via a lookup in the
heap corresponding to the type.

## The Source Language

Because Compact does not currently have first-class ADTs, calls to `read` on
ledger `Cell` types can be implicit, and assignment expressions can be used as
shorthand for calls to `write` on ledger `Cell`s.  In the presence of
first-class ADTs these could be ambiguous.  For this reason we consider a source
language where ledger `Cell` reads and writes are explicit (in the form of calls
to the `read` and `write` operations).  For clarity, we use a fully
type-annotated source language in examples, though this is not necessary.

In Compact, top-level ledger fields with a Compact (not ledger ADT) type `T` are
implicitly of ledger ADT type `Cell<T>`.  We assume that this is always explicit
in the source language.

*[TODO: require a constructor and that every field is explicitly initialized in
the source language, using the appropriate default if there was no original
initializer.  Update all the examples to include this.  Does it let (or make) us
modify the translation of the ledger slightly?]*

The source language is then extended so that ledger ADT types are Compact types
and can appear wherever Compact types can appear.  Expressions with ledger ADT
types can appear anywhere expressions can appear (and not just as the ADT
subexpression in a ledger ADT operation expression).

The target language is the same as the source language except that the
first-class ledger ADTs have been translated away.  The type system is again
stratified into Compact types and ledger ADT types.

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

The translation `type[[_]]` operates on Compact and ledger ADT types.  We write
`type*[[_]]` to indicate mapping this translation of a sequence of types.

If the type is a first-class ledger ADT type in the collected set, it is
replaced with `Addr`, which is a builtin Compact type we have introduced for the
purpose.  It is a Compact type which can be used as a `Map` key and which is
"big enough" in the sense of having enough values to represent many values of a
given type.  This is not a type which is available to the user.

Otherwise, the type is the same type with the subterms translated by
`type[[_]]`.

Top-level ledger fields use a slightly different tranlation `ltype[[_]]`.  For a
top-level ledger field whose type is in the collected set, we replace it with
`Cell<Addr>` (not just `Addr`, because that can't appear as a top-level ledger
field type in the source language).  Otherwise, we translate the subterms using
`type[[_]]` (because they are not top-level ledger ADTs).

### Ledger

We add a heap ledger field per type in the collected set.  For a type `T`, we
will write this field with name `heap_T`, e.g., for `Cell<Field>` we will write
`heap_Cell<Field>` even though this is not a valid Compact identifier that a
programmer could write.

For a non-generic ledger ADT type `T`, the type of this field is `Map<Addr, T>`.
For a generic ledger ADT type `T<T*, ...>`, the type of this field is
`Map<Addr,T<type*[[T*]],...>`.  That is, the subterms of the value type are
translated using the type translation above.

We need the ability to allocate keys for these maps.  We assume a nullary
generic ledger kernel operation `allocate`,
e.g. `kernel.allocate<Cell<Field>>()` will return a value of type `Addr`.

If there is no constructor, we introduce one.  In the constructor, before any
other code, we add allocation and initialization for all the ledger fields with
first-class ledger ADT types (i.e., types in the collected set which are `Addr`
after the translation).  For a field `f` and type `T`, where the value type of
`heap_T` is `V`, we introduce a fresh identifier `a` and add the statements:

```
const a: Addr = kernel.allocate<T>();
f.write(a);
heap_T.insert(a, default<V>);
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

- When it encounters `default<T>` where `T` is a ledger ADT type in the
  collected set, this represents the dynamic memory allocation of a first class
  value of type `T` *[KSM: except as a value inserted in a `Map` with a ledger
  ADT value type, how to describe this in a simple way?]*  This is translated as
  the expression:
  ```
  (addr) => {
     heap_T.insert(addr,default<T>);
	 return addr;
  }(kernel.allocate<T>())
  ```
  This is simply a `let` binding.  In reality the translation can be done on an
  IR that includes `let`.  As a source-to-source translation in the examples we
  will use `const` binding when `default` occurs in a suitable context.

## Examples

### Swapping arbitrary ledger cells

Here is a program in the source language which swaps the values in a pair of
ledger cells:

```
import CompactStandardLibrary;

ledger field0: Cell<Field>;
ledger field1: Cell<Field>;

// TODO: Add a constructor and verify its translation below.

circuit swap(c0: Cell<Field>, c1: Cell<Field>): [] {
  const tmp: Field = c0.read();
  c0.write(c1.read());
  c1.write(tmp);
}

export circuit test(): [Field, Field, Field] {
  const c: Cell<Field> = field0;
  field0.write(2);
  swap(c, field1);
  return [field0.read(), field1.read(), c.read()];
}
```

The collected set for this program is {`Cell<Field>`}.

Applying the translation defined above yields:

```
import CompactStandardLibrary;

ledger field0: Cell<Addr>;
ledger field1: Cell<Addr>;

ledger heap_Cell<Field>: Map<Addr, Cell<Field>>;

constructor() {
  const a0: Addr = kernel.allocate<Cell<Field>>();
  field0.write(a0);
  heap_Cell<Field>.insert(a0, default<Cell<Field>>);
  
  const a1: Addr = kernel.allocate<Cell<Field>>();
  field1.write(a1);
  heap_Cell<Field>.insert(a1, default<Cell<Field>>);
}

circuit swap(c0: Addr, c1: Addr): [] {
  const tmp: Field = heap_Cell<Field>.lookup(c0).read();
  heap_Cell<Field>.lookup(c0).write(heap_Cell<Field>.lookup(c1).read());
  heap_Cell<Field>.lookup(c1).write(tmp);
}

export circuit test(): [Field, Field, Field] {
  const c: Addr = field0.read();
  heap_Cell<Field>.lookup(field0.read()).write(2);
  swap(c, field1.read());
  return [heap_Cell<Field>.lookup(field0.read()).read(),
          heap_Cell<Field>.lookup(field1.read()).read(),
          heap_Cell<Field>.lookup(c).read()];
```

If `field0` contains 0 and `field1` contains 1 and we invoke `test`, the result
will be `[1,2,1]`, illustrating that the reference `c` is an alias to the
reference `field0` (they are the same heap map key).

### Top-level first-class ledger ADTs

An example that uses first-class ledger ADTs in the ledger itself (at the top
level) is a variation of the one above.  It has ledger fields holding Compact
values of `Field` type, and ledger fields holding Compact values of
`Cell<Field>` type:

```
import CompactStandardLibrary;

ledger field0: Cell<Field>;
ledger field1: Cell<Field>;
ledger cell0: Cell<Cell<Field>>;
ledger cell1: Cell<Cell<Field>>;

constructor() {
  field0.write(default<Field>);
  field1.write(default<Field>);
  cell0.write(default<Cell<Field>>);
  cell1.write(default<Cell<Field>>);
}

Export circuit fieldToCell(): [] {
  cell0.read().write(field0.read());
}

export circuit cellToField(): [] {
  field0.write(cell0.read().read());
}

export circuit fieldToField(): [] {
  field0.write(field1.read());
}

export circuit cellContentsToCellContents(): [] {
  cell0.read().write(cell1.read().read());
}

export circuit cellToCell(): [] {
  cell0.write(cell1.read());
}
```

This program illustrates first class ledger ADTs that appear in the ledger
itself, not necessarily as Compact values flowing through the contract.  The
collected set is `Cell<Field>` because it appears as the type argument in
`cell0: Cell<Cell<Field>>.  The translation results in:

```
import CompactStandardLibrary;

ledger field0: Cell<Addr;
ledger field1: Cell<Addr>;
ledger cell0: Cell<Addr>;
ledger cell1: Cell<Addr>;

ledger heap_Cell<Field>: Map<Addr, Cell<Field>>;

constructor() {
  const a0: Addr = kernel.allocate<Cell<Field>>();
  field0.write(a0);
  heap_Cell<Field>.insert(a0, default<Cell<Field>>);

  const a1: Addr = kernel.allocate<Cell<Field>>();
  field1.write(a1);
  heap_Cell<Field>.insert(a1, default<Cell<Field>>);

  const a2: Addr = kernel.allocate<Cell<Field>>();
  heap_Cell<Field>.insert(a2, default<Cell<Field>>);
  cell0.write(addr);

  const a3: Addr = kernel.allocate<Cell<Field>>();
  heap_Cell<Field>.insert(a3, default<Cell<Field>>);
  cell1.write(addr);
}

export circuit fieldToCell(): [] {
  heap_Cell<Field>.lookup(cell0.read()).write(
      heap_Cell<Field>.lookup(field0.read()).read());
}

export circuit cellToField(): [] {
  heap_Cell<Field>.lookup(field0.read()).write(
      heap_Cell<Field>.lookup(cell0.read()).read());
}

export circuit fieldToField(): [] {
  heap_Cell<Field>.lookup(field0.read()).write(
      heap_Cell<Field>.lookup(field1.read()).read());
}

export circuit cellContentsToCellContents(): [] {
  heap_Cell<Field>.lookup(cell0.read()).write(
      heap_Cell<Field>.lookup(cell1.read()).read());
}

export circuit cellToCell(): [] {
  cell0.write(cell1.read());
}
```

This example illustrates some subtle properties.

First, the types of `field0` and `cell0` are different before the translation
but they are the same after the translation.  They have the same type but for
different reasons.  The source type of `field0` is `Cell<Field>` which is in the
collected set.  This type is translated to `Addr` everywhere, except the
top-level of the ledger where it becomes `Cell<Addr>`.  The source type of
`cell0` is `Cell<Cell<Field>>`.  This type is not in the collected set
(`Cell<Cell<Field>>` is not a first-class ADT in this program), but the type
argument `Cell<Field>` is in the collected set and so it's replaced with `Addr`,
yielding `Cell<Addr>`.  In the type of `field0`, the outermost `Cell` is to keep
the ledger types well-formed (they must be ledger ADT types, not Compact types
like `Addr`).  This cell is *NOT* mutable to the programmer (because the
translation doesn't expose any way to change its contents).  In the type of
`cell0`, the `Cell` type is the *outermost* one in the original
`Cell<Cell<Field>>`.  This cell *IS* mutable because it occurs in the original
source program.

Because `field0`, `field1`, `cell0`, and `cell1` all have the same type, the
translation of the bodies of the first four circuits (moving the cell contents
around) are identical as we would expect.  For references to `field0` and
`field1`, there is an extra `read()` inserted by the translation, and for
references to `cell0` and `cell1` it was already explicit in the source.

The body of the last circuit demonstrates a capability that isn't available for
`field0`: `cell0` is a mutable cell in the ledger and the programmer can assign
it.  In this case, the code causes `cell0` to become an alias for `cell1` (they
are the same address in the heap).

### Passing lists of cells, dynamic allocation

Here is a program that has a list of cells which can be passed to a circuit.

```
import CompactStandardLibrary;

ledger list: List<Cell<Field>>;

// TODO: Add a proper constructor and ensure that the translation of it is correct.

circuit swapTwo(ls: List<Cell<Field>>): [] {
  const fst: Cell<Field> = ls.head().value;
  ls.pop_front();
  const snd: Cell<Field> = ls.head().value;
  ls.pop_front();
  ls.push_front(fst);
  ls.push_front(snd);
}

export circuit test(): [] {
  const x0: Cell<Field> = default<Cell<Field>>;
  x0.write(0);
  list.push_front(x0);
  const x1: Cell<Field> = default<Cell<Field>>;
  x1.write(1);
  list.push_front(x1);
  swapTwo(list);
}
```

The collected set contains `List<Cell<Field>>` because it is used as the
parameter type in `swapTwo`, and it contains `Cell<Field>` because it is a
subterm in `List<Cell<Field>>` (where only Compact types are currently allowed)
and also because it is used on `const` type annotations.

The translation will therefore have a pair of heaps:

```
import CompactStandardLibrary;

ledger list: Addr;

ledger heap_List<Cell<Field>>: Map<Addr, List<Addr>>;
ledger heap_Cell<Field>: Map<Addr, Cell<Field>>;

constructor() {
  const a0: Addr = kernel.allocate<List<Cell<Field>>();
  list.write(a0);
  heap_List<Cell<Field>>.insert(default<List<Addr>>);
}

circuit swapTwo(ls: Addr): [] {
  const fst: Addr = heap_List<Cell<Field>>.lookup(ls).head().value;
  heap_List<Cell<Field>>.lookup(ls).pop_front();
  const snd: Addr = heap_List<Cell<Field>>.lookup(ls).head().value;
  heap_List<Cell<Field>>.lookup(ls).pop_front();
  heap_List<Cell<Field>>.lookup(ls).push_front(fst);
  heap_List<Cell<Field>>.lookup(ls).push_front(snd);
}

export circuit test(): [] {
  const x0: Addr = kernel.allocate<Cell<Field>>();
  heap_Cell<Field>.insert(x0, default<Cell<Field>>);
  heap_Cell<Field>.lookup(x0).write(0);
  heap_List<Cell<Field>>.lookup(list.read()).push_front(x0);
  const x1: Addr = kernel.allocate<Cell<Field>>();
  heap_Cell<Field>.insert(x1, default<Cell<Field>>);
  heap_Cell<Field>.lookup(x1).write(1);
  heap_List<Cell<Field>>.lookup(list.read()).push_front(x1);
  swapTwo(list.read());
}
```

This example illustrates the dynamic allocation of a pair of ledger cells, which
survive the transaction by being placed in a list in the ledger.
