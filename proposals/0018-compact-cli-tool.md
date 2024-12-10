# Proposal 0018: `compact` CLI Tool for Compact

## Problem Statement

There will be potentially many command-line tools that Contract and DApp
developers will use.  We already have the `compactc` compiler and we plan to
launch `compactup`, the Compact updater tool.  In addition we plan a "fixup"
tool to apply automated fixed to contracts, such as updating to new syntax when
we make breaking changes; and this will rely on a "format" tool that formats
Compact source code.

Developers should not have to know the specific details of how we've implemented
these tools.  For instance, some of theme might be Rust binaries, some of the
might be Scheme binaries, and some of them might be shell scripts.  Some of them
(such as "format" and "fixup") might actually be the same tool invoked with
different options.

In addition, we should provide a uniform UX for invoking these tools: similar
options should be specified to the tools in similar ways.

## Overview of the Proposal

We propose a single CLI (command-line interface) tool for working with Compact
contracts (and possibly Midnight DApps).  It will be named `compact`, and it
will have subcommands for the various things that it is capable of doing.

An example of such a tool that many developers will be familiar with is the
`git` command-line program.  `git` has a **lot** of subcommands, but to
developers they are all just seen as "part of Git".  Developers can see a list
of all commands via `git help -a`, and they can get help on an individual
command via, for example, `git help bisect` for help on the `git bisect`
subcommand.

In the context of programming languages, and example of a CLI tool is the
[`dart` tool](https://dart.dev/tools/dart-tool) for the Dart programming
language.  For app development, and example is the [`flutter`
tool](https://docs.flutter.dev/reference/flutter-cli) for the Flutter mobile app
development framework.  These are presented to give an idea of some of the
things such tools can be used for.

### Keeping the Tool Updated

One nice feature is if the CLI tool automatically updates itself when invoked.
To avoid latency (of a version check to a server somewhere), it's likely a good
idea to perform this check only periodically when a subcommand is invoked.

Note that this is an update of the `compact` tool itself, but not necessarily an
update of the tools implementing the subcommands.  For instance, we likely want
updating (or reverting) the compiler version to be an explicit action from the
developer in some way.

### Subcommands

What follows is a list of possible subcommands for the `compact` tool.  Some of
them are already provided by other tools, and will be simply moved under the new
CLI tool.  In these cases, we will prefer removing (or rather, "hiding" by
renaming) the current tool, either at the same time we launch `compact` or as a
deprecation and an announced future removal.  For example, if `compact compile`
invokes the compiler, it is potentially confusing that `compactc` also invokes
the compiler (and not necessarily with the same options or in the same
configuration).

#### Planned Subcommands

We have a small number of subcommands for tools that already exist or that we
are currently building.

**`compact compile`** This will invoke the Compact compiler, currently shipped
as `compactc`.  It will compile your contract code to TypeScript interfaces,
JavaScript implementations, and ZKIR circuit representations (just as `compactc`
currently does).  `compactc` is implemented in Scheme and invoked by a Bash
shell script wrapper.

**`compact update`** This will invoke the `compactup` tool developed by the CE
squad at IO.  This tool will download binary artifacts needed according to an
explicit version (which could be "latest").  It solves a very common problem
that developers have where they have mismatching versions of artifacts.  We
specifically see this with example DApps and compiler versions.  This tool is
not yet launched.  Ideally we launch it at the same time as `compact` (so that
`compact` has more than one subcommand at launch).

**`compact fix`** We have been making some breaking changes to the language,
which require developers to update their contract code when they switch to a new
compiler version.  Many of these can be automated.

For example, a future release of the compiler will have a big, but tedious
change.  We will change the way we capitalize Compact standard library and
ledger ADT names.  Currently they use a mix of "kebab case" (like
`hash_to_curve`) for functions and "camel case" (like `MerkleTreeDigest`) for
types, but we will change this to use "camel case" (like `hashToCurve`)
everywhere.  This change is for uniformity and to match the common TypeScript
and JavaScript style.

This change is tedious and error prone.  A developer has to manually look for
such names and change them all.  They might misspell a name, which they only
discover when they compile their contract.  Even more complicated, they have to
be careful that they don't incorrectly rename the wrong things (like their own
implementation of `hash_to_curve` that shadows the standart library's one).

To apply these fixes automatically, we are building a tool that will be invoked
by `compact fix`.  Initially it will apply updates to the latest version of
Compact, unless there is a compiler version or language version in the contract.
In that case, it will "update" to that version.  (We haven't completely decided
what that means or how it will work.)

**`compact format`** As part of `compact fix` we will use an automatic formatter
for Compact contracts.  Changing the capitalization of identifiers can break
alignment in the code, so we will reformat it.  We can provide a "separate"
subcommand for formatting code without applying any fixups.

This is a case where our implementation might be using the same binary with
different options, but developers will logically think of it as a separate
subcommand.

**`compact help`** We should have a `help` subcommand that lists common options
to all subcommands, list the available subcommands, and that can provide
specific help on subcommands via `compact help compile`, `compact help update`,
etc.

#### Possible Future Subcommands

These are some ideas of future subcommands, not intended as a commitment.  They
are listed alphabetically here, but obviously some of them will be easier to
implement or deliver more value to developers.

**`compact build`** To build a DApp, including the contract (which might need to
be compiled) and the TypeScript or JavaScript DApp implementation.  This might
require developers to use a "standard" TS/JS toolchain, or have options to
select one.

**`compact create`** We have had questions from developers about what is the
bare minimum structure they need for a DApp.  We could provide a subcommand to
create a skeleton or template DApp.

**`compact deploy`** In our example DApps, we normally make deploying the
contract something that happes through the DApps UI or some other UI.  It might
be useful for developers to have a CLI subcommand that deploys their contract
somehow.  It could have options (or separate subcommands) to "check on" the
status of a deployed contract (see its address, see its state, etc.).

**`compact doc`** This will generate HTML or other formatted documentation from
comments in the source code.

**`compact lint`** A "linter" is a tool that warns about potential problems in
source code.  These are not necessarily real problems, so making them a compiler
error will result in false positives that a developer has to work around.
Still, some organizations require code to be free of "lints".  We could provide
a tool to identify potential problems that fall short of a compiler error.

A less jargony name might be `compact analyze`, but it should be clear to
developers what the tool is doing.  We could provide an option to `compact fix`
to fix these problems, or have automated fixes an option to `compact lint`.

**`compact serve`** To run a DApp with a local web server, for testing.  This
could have options to debug the DApp.

**`compact test`** We might provide a testing framework for contract circuits,
and then the subcommand `compact test` could run all or a subset of a contract's
tests.
