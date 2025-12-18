# Midnight Ledger Support in the Compact Toolchain

**Overview:**
Compact is the smart contract language for the Midnight Network.
Midnight will eventually consist of multiple environments.
There will be the Midnight Mainnet itself and multiple "testnets".
The compiler-generated code depends on the Midnight Network through the ledger.
We propose a way to develop the Compact toolchain (containing the Compact compiler)
so it can target multiple environments while
(1) offering a good user experience,
(2) giving timely access to new language features for Mainnet users, and
(3) minimizing the maintenance burden on the Compact language developers.

## Context

To set the stage we describe Compact's current (single ledger version) release process,
explain how the Midnight Network environments will be upgraded, and
describe how the Compact toolchain depends on the ledger version.

Compact has two very important characteristics that differ from the rest of the Midnight Network.

First, **Compact is not "deployed" in the same way**.
For the software on the Midnight Network, we can choose to upgrade it and deploy it to the network.
For the Compact tools, we do not choose to deploy it.
Developers themselves choose a version that they will use.

For the Midnight Network, it makes sense to have a matrix telling exactly what configuration of software is deployed.
For the Compact tooling, this does not make sense in the same way.
There is a range of versions that might be used (not all of them will be supported).
Some users are very conservative about updating tooling.
We **can't** force them to do it (well, we can try, but they won't be happy at all).
We **must** provide a good user experience for all our users, even ones staying on older versions.
Since our users choose to upgrade, we **must** make it easy and obvious to them when they need to do so.

Second, **Compact has language features that are independent of the network environment**.
It doesn't really make sense to think of the versioned network components in this way.
Those components **are** the network.
However, Compact language features are (perhaps most) often independent of specific network environment.
As an example, we developed "type aliases" in Compact.
This is a pure language feature that does not depend on the environment it is used on.
Conceptually, this feature should work on Mainnet itself and on any available testnet, because it does not change the interface of contracts to the network.

Because most language features will be like this, we absolutely do not want to tie them to some (completely unrelated!) network promotion process.

### Compact development and release

We have so far used a regular periodic release process for Compact.
Features are developed and merge to Compact's `main` (development) branch.
They are merged in a form where they are ready to be shipped.
Periodically (roughly every two sprints, or four weeks),
we commit an updated version number to `main` and merge that commit to our (single) release branch.

We can build internal release candidates from either the release branch (usually) or `main` (sometimes, early in the release process).
We stabilize and make fixes to the release by committing them to the release branch and merging them to main
(or we could commit them to main and cherry pick them to the release branch).
When we're ready, the release branch is tagged with the version number and release builds are made.

The Compact developer tools (devtools, the `compact` command-line program) can be used to upgrade the toolchain and switch versions.
New toolchain releases are in a public repository, and the devtools can get a list of them and upgrade by (1) downloading the appropriate artifact based on OS and architecture, (2) unzipping it to a directory managed by the devtools, and (3) arranging to invoke it appropriately.
The devtools keeps old versions (unless told to delete them) so "upgrading" back to a previous version is simple.

Important characteristics of this release strategy for the development team are:
(1) we maintain a single development branch,
(2) we have a single release branch, and
(3) only the most recent release is supported in the sense of potentially getting bugfix releases.

The most important characteristic for users is that they get a constant flow of new language features.

### Midnight environments and promotion

The Midnight Network will have a single Mainnet and a number of "testnets".
We will focus on a specific pair of public testnets: Preview and Preprod.

The **Midnight Mainnet** (Mainnet for short) is the Midnight Network blockchain itself.
It will have periodic upgrades and sometimes hard forks.

The **Prepoduction Testnet** (Preprod for short) is a public testnet that will be upgraded to 
the expected next version of Mainnet when a Mainnet upgrade is announced.
Developers can use Preprod to assess the impact of an upgrade on their contracts.
In between Mainnet upgrades, preprod is not particularly interesting for developers.
At these times, when there is no specifically expected Mainnet upgrade,
we expect that Preprod will have software identical to Mainnet's.

The **Preview Testnet** (Preview for short) is a public testnet that will get the latest released features.
When new features come to the network, they will arrive in Preview before Mainnet.
Developers can use Preview to test out those features, and to have early access to develop and test
contracts using the features.

There is a process of promotion between networks.
When Mainnet is updated, it is by promoting the version on Preprod.
And when Preprod is updated, it is by deploying to it some (but not necessarily the latest?)
version of the network that was once on Preview.

### The Compact toolchain's dependency on the Midnight Network

The working of the Compact toolchain itself does not depend on the Midnight Network,
but the contract code generated by the compiler **does**.
This dependency is via the Midnight ledger.

The compiler-generated JavaScript (JS) code uses a JS library called the Compact runtime.
This library has an embedded version of the ledger called the on-chain runtime.
The on-chain runtime is compiled from the ledger's Rust code into WebAssembly (Wasm).
When the ledger version changes and requires an updated on-chain runtime, we normally have to update the Compact runtime.
At a minimum, the Compact runtime has to import the new version of the on-chain runtime.
In some cases, the Compact runtime and possibly the generated JS might have to be updated to account for ledger changes.

The compiler also generates ZKIR (**Z**ero **K**nowledge **I**ntermediate **R**epresentation) circuits for contracts.
These are used as input to a binary called `zkir` that ships with the Compact toolchain.
`zkir` is compiled from the ledger's Rust code into a separate binary that is invoked by the compiler.
The `zkir` binary takes the compiler-produced ZKIR as input and generates prover and verifier keys to be used on-chain.

When the ledger version changes, a new version of the `zkir` binary will be included in a toolchain release.

Compact comes with a standard library.
The standard library can change with ledger changes.
If the ledger adds new features, they are normally exposed to the langauge through the standard library.
Even without new features, the implementation of the standard library can change.
As an example, ledger version 6.2 had a different representation of coin commitments on chain.
These were constructed for Compact by code in the standard library implementation, which needed to be updated.
Part of the standard library are the so-called "ledger ADTs" (Abstract Data Types).
These ADTs or their implementations can also change when the ledger changes.

Note that the compiler does not depend on the ledger's patch version.
New (non-breaking) ledger features will always come with a minor version increment,
and breaking changes will always come with a major version increment.

### Compact Language Features

Many Compact language (as opposed to library) features are completely independent of the network backend.
They do not rely on the interface to the ledger, and they do not change the interface of compiled contracts to the network.
As two simple examples: we implemented "type aliases" where a user could give a short name to Compact type,
and we implemented "selective import and renaming" where a user could import only specific names from a Compact module and
could individually rename imported names.
Neither of these features rely on the interface to the Midnight Network.
Conceivably, we could (and should!) deliver these features immediately to Mainnet users in the next release.

## Rejected approach: single ledger version, single release channel

This is our current approach.
It works well for us now and we could continue to use it.
Here is how it would work in the face of multiple network environments.

The code on the development branch (`main`) still targets a single ledger version.
Because we don't want multiple development branches, this ledger version is necessarily the latest on deployed to Preview.
New features are developed on `main` and there are regular periodic releases, which target Preview.
These new releases can only be used on a more stable network (Preprod or Mainnet) if they happen to have the same ledger (major and minor) version.

Preprod and Mainnet users are told to remain on an earlier released version of the compiler.
The Compact devtools can help make this easy and obvious for users.
Conceivably, there are three different versions of the toolchain in use.

### Mutiple release branches

A difference from the current approach is that the versions of the toolchain used for Preview, Preprod, and Mainnet are all supported.
We might need to release bug fixes for any of these supported releases.
Therefore, we will have to maintain multiple (at least three) different release branches in some way.
Unless we can guarantee that promotion to Preprod is **always** the current version on Preview,
we will have to also maintain release branches somehow for old versions of Preview that might be candidates for Preprod.

For example: if we consider numbering Preview deployments and we are on Preview 19 when a decision is made to deploy Preview 17 to Preprod.
Then we will need a release branch for Preprod that corresponds to the latest version of the Compact tools that worked on Preview 17.
We either maintained this branch until it was definitely not needed, or we reconstituted it from an earlier tag and backported bug fixes to it.

### Promotion events

A promotion event in this approach is pretty simple.
For instance, if we promote some version of Preview to Preprod, we tell Preprod users to use an updated, already released, version of the toolchain.
This it the latest supported release for the promoted version of Preview.
Only once that promotion happens can we stop supporting earlier Preview releases because we now don't believe that they will ever be promoted to Preprod.

Promotion of Preprod to Mainnet is similarly simple: we tell Mainnet users to use a newer already-released version of the toolchain.
The Compact devtools can make this simple and obvious to users.

### Consequences

We have **rejected** this approach for two reasons.

First, it requires us to maintain multiple release branches, which we'd rather not have to do.

Second, and much more importantly, it means that Mainnet users can't get new language features like "type aliases" or "selective import and renaming"
until those features undergo network promotion from Preview all the way to Mainnet.
This network promotion is completely unrelated to those language features, and restricting them from Mainnet is completely artificial.

If Mainnet upgrades happen, say, every four months then Mainnet users will perceive that the Compact language is stagnant for four months at a time.
If they are waiting for a language feature in Preview, then they will be perversely both hoping for a Mainnet upgrade so they can get the feature,
and dreading an upgrade because it might create undesired upgrade work for them.

If we have a really stable year where there are no Mainnet upgrades, then the language will not get a chance to improve for that year.

## Rejected approach: multiple release channels

We might consider an approach where we have "alpha" (corresponding to Preview), "beta" (Preprod) and "stable" (Mainnet) release channels for the Compact tools.
Conceptually, this means we maintain at least three separate development branches in addition to at least three separate release branches.

New language features become like bug fixes: they need to be cherry-picked or backported to all the active development branches.

This approach seems untenable (it's not even obvious how we would assign coherent version numbers) and overly complicated.

It's **rejected** outright because there is a simpler and much better way.

## Proposal: multiple ledger backends

We believe that we can segregate the part of the Compact toolchain that depends on the ledger into a "ledger backend".
As described above, this consists of the JavaScript code generator (basically, only the code in `compiler/typescript-passes.ss`),
the ZKIR code generator (the code in `compiler/zkir-passes.ss`),
the standard library (`compiler/standard-library.compact`),
the ledger ADT implementation (`compiler/midnight-ledger.ss`),
and the so-called "natives" provided by the ledger (`compiler/midnight-natives.ss`).

We will move all of this code into a subdirectory like `compiler/ledger-6.2`.

The compiler will be changed to allow multiple different versions of this code to be built in at compile time (that is, when we compile the compiler).
It will be able to select between them with a flag, like `--ledger=6.2`.
We will also find a way to make the `zkir` binary support multiple ledger versions
(at worst we can ship multiple binaries with a release and dispatch to the correct one).

The Compact devtools can maintain a mapping between the **relative** names of the environments,
such as `--environment=preview` is currently the same as `--ledger=6.2`.

We only have to maintain a limited number of these subdirectories.
Once a version of the ledger that was on Preview is no longer a candidate for promotion to Preprod
(that is, when a newer version is deployed to Preprod),
we can delete that version.
And once a version of the ledger that is on Mainnet is replaced with a newer one, we can delete that version.

Therefore, the compiler supports only a specific enumerable list of `--ledger` version numbers in a given release.

We still maintain a single release branch.
Bugfixes are made as normal, and they are fixed in all the affected backends.
New language features are developed the same as today, and they are released simultaneously for all environments.

## Scenarios

We will continue to make frequent periodic releases as normal, independent of the environment promotion cadence.
Developers will get new language features in new releases, for all environments.

We will also be required to make new releases in conjunction with new ledger deployments to Preview.

It's instructive to consider what happens when the network is upgraded.
For illustration, suppose that Mainnet and Preprod are on ledger version 7.0.x
(remember, Compact does not care about the ledger's patch version)
and Preview is on ledger version 8.0.x.

Suppose that the current released version of the Compact toolchain is 1.2.0.
This is supported in the compiler by two separate ledger backends:
`compiler/ledger-7.0` and `compiler/ledger-8.0`.
It is selected by flags `--ledger=7.0` and `--ledger=8.0`,
and the Compact devtools allows `--environment=preview` (to select the ledger 8.0 backend),
`--environment=preprod`, and `--environment=mainnet` (to select the ledger 7.0 backend).

### An upgrade to Preview

Suppose that there is a ledger version 8.1.0 to be deployed to Preview.

Before that can happen, the langauge team will duplicate the `compiler/ledger-8.0` subdirectory
into `compiler/ledger-8.1` and then update that to support ledger 8.1.0.

We would not necessarily delete the `compiler/ledger-8.0` backend,
because it is still potentially a candidate for promotion to Preprod.

Then, in conjunction with the ledger 8.1.0 deployment to preview, a new release of the Compact toolchain must be made.

This would be Compact toolchain version 1.3.0.
It would support `--ledger=7.0` and `--ledger=8.1` (we might choose to allow `--ledger=8.0` or we might hide that).
The Compact devtools don't necessarily need to be updated, they just need to be able to find a new mapping where Preview is ledger version 8.1.

This necessary release does not necessarily update the language version.
Preprod and Mainnet users could choose to remain on Compact toolchain 1.2.0, but it is no longer supported.

### Promotion of Preview to Preprod

Suppose that there is a decision to update Midnight Mainnet to the latest ledger 8 version, which is 8.1.0 on Preview.
In preparation, ledger 8.1.0 is going to be promoted to Preprod.

There is no ledger integration work required for the language team.
There is no update required to the Compact toolchain or the Compact devtools.
The devtools only has to find a new mapping from Preprod to ledger 8.1.

Now, when users compile with `compact --environment=preprod compile` it will invoke the compiler as
`compactc --ledger=8.1` instead of `compactc --ledger=7.0`.

Mainnet users can still stay on Compact toolchain 1.2.0, or upgrade as they choose.
Preprod users would need at least Compact toolchain 1.3.0 (this is the earliest version supporting ledger 8.1).
The Compact devtools can make this simple and obvious, and update when necessary.

Once the deployment is made to Preprod, the language team can presume that it's OK to delete `compiler/ledger-8.0`
because it's no longer deployed on Preview and it's not a candidate to ever be deployed to Preprod (or Mainnet).

### Another upgrade to Preview

Suppose that before ledger 8.1 is deployed to Mainnet, there is a ledger 8.2 developed and deployed to Preview.
(We would not necessarily freeze Preview updates.)

This is exactly the same as the Preview upgrade described before.
The languages team would create a new backend subdirectory and develop support.
A new release (Compact toolchain 1.4.0) is necessary to support the new backend.
Preview users must be on Compact tolchain 1.4,
Preprod users can use 1.4 or any version after 1.3,
and Mainnet users can use 1.4 or any version after 1.2.
Again, the Compact devtools can manage these associations for developers.

### A Compact toolchain bug fix

Suppose a bug is found on Compact toolchain 1.4.0 affecting the ledger 8.1 and 8.2 backends,
and we decide to release a bug fix.
The fix is developed and tested in both backends, it is cherry picked to the release branch, and a new 1.4.1 release is made.

Preview and Preprod users are told that they should ugrade.

### Promotion of Preprod to Mainnet

This promotion is the same as from Preview to Preprod.
There is no new ledger integration, and there is no new release necessary for the Compact toolchain.
The association of `--environment=mainnet` has to change from `--ledger=7.0` to `--ledger=8.1`.

A difference here is that we can now remove the `compiler/ledger-7.0` implementation because we don't expect that it will be redeployed to Mainnet.

### A bug is discovered and fixed in the ledger

There is no work for the languages team.
The ledger-specific backends don't depend on the ledger's patch version level.

### A new regular release of the toolchain

A new periodic release of the toolchain is made with new language features.
This would get toolchain version 1.5.0, and there would be a bump of the language version (to, say Compact 1.1).

This is prepared as usual, by merging a specific commit from the development branch (`main`) into the release branch.
When users update, for any environment, they would get access to the Compact 1.1. features.
