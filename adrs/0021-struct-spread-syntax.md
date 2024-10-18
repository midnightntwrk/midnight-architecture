# Introduce Compact `struct` spread syntax, remove `new`

## Status

Proposed

---
| -         | -                                                                        |
|-----------|--------------------------------------------------------------------------|
| date      | 2024-08-13                                                               |
| deciders  | Kevin Millikin                                                           |
| consulted | Languages team                                                           |
| informed  | -                                                                        |
---

## Context and Problem Statement

Compact structure (`struct`) values are immutable.  Creating new `struct` values
from existing ones can be tedious and error-prone for developers.

Part of [Proposal 0015](../proposals/0015-spread-syntax.md) is the introduction
of new syntax for functional update of `struct` values, using the "spread"
(ellipsis, `...`) operator from TypeScript and JavaScript.  This gives a
convenient way to create new `struct` values from existing ones.

This new syntax subsumes the current way that `struct` values are created, via
the `new` keyword.  Therefore, we can remove the `new` keyword.  This is a
breaking change for developers.  They will have to update their code when
compiling with a new version of the `compactc` compiler when we remove the
keyword.  However, it is a change that we would like to make because it
simplifies the language both conceptually for developers and for our own
implementations.

Because this is a breaking change, we prefer to do it as soon as we can to
minimize the impact on (future) Compact developers.

## Overview of the Changes

The quick summary of the changes is:

* Implement the spread syntax from [Proposal 0015](../proposals/0015-spread-syntax.md)
  for `struct`s, but not yet for vectors
* Remove the current `new` syntax for struct construction

The breaking change we are prioritizing is the removal of `new`.  We cannot do
that without giving developers something to replace it.

We do not yet need to support spread in vector creation expressions.  Spread in
vector creation is a non-breaking change, and it requires another feature
(vector slicing, in development) to be fully useful for functional update of
vectors.

### Considered Options

1. We could introduce spread for `struct`s and keep `new` as well

1. We could stage the introduction of the feature and the removal of the keyword,
  so that the new feature was first introduced, the keyword was deprecated, and
  then the keyword was removed
  
1. The decided option: to introduce spread for `struct`s and remove the `new`
  keyword in the same release
  
The first option makes Compact a more complicated language.

It is conceptually complicated for developers, because there are more language
features they have to know about.  Even if the old way becomes less common, it
is still possible that they will encounter it in code they are reading.  We want
Compact to be a simple and easy to learn language, so we don't really want two
different ways to do this one thing (create `struct` values).

It is also more complicated for us to develop.  Our tools have to implement
support for both language features and we have to test both of them.

The second option is one that we would use if Compact was further along in its
lifecycle, like post-MainNet or Compact version 1.0.  While we are currently in
TestNet and Compact is at version 0.x, we can use a less heavyweight process.
For developers, option 2 is more like two changes they have to be aware of:
first they can use the new syntax, learn it, and start thinking about removing
the old one; and then later they *must* remove the old syntax.

### Decision Outcome

For those reasons, we've decided to use the third option.

Note that this would be an ideal change for us to try to automate via a
`compact fix` tool.  The change is conceptually simple: replace
`new Foo(e, ...)` and `new Bar<X, Y>(e, ...)` with `Foo {x: e, ...}` and
`Bar<X, Y>{x: e, ...}`.  The complicated part for developers doing this manually
is listing the `struct` field names `x` in order.  If we automate this, it will
likely disturb the code's indentation and we do not yet have a Compact formatter
to fix that.

This change required updates to our compiler tests, example DApps, and our
documentation.

### Validation

* Update the compiler tests and example DApps to use the new syntax, and ensure
  that they work as before
