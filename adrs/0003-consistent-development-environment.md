# 3. Consistent Development Environment

## Status

accepted

---

| -         | -                                            |
|-----------|----------------------------------------------|
| date      | 2022-07-15                                   |
| deciders  | Jon Rossie, Jakub Zalewski and Andrzej Kopeć |
| consulted | Midnight team                                |

---

## Context and Problem Statement

At Midnight (and IOG in general) there are no restrictions (and guidelines) for developer
environments. Everyone is left to their own devices, which is great in terms of
flexibility, but results in variety of different systems.

Engineers use different operating systems, including but not limited to:

- Windows (WSL + Ubuntu)
- Linux (Ubuntu, NixOS)
- macOS

Furthermore, there are at least three architectures that are being in use:

- x86
- arm64 with x86 emulation (Rosetta 2 on macOS)
- arm64

Additionally, there are multiple ways engineers can set up their environment.

It all combined, often leads to many questions, hard-to-reproduce issues, differences in
behavior between code built on CI and by different team members or even avoidable CI
builds because of some checks/steps/tools missing in the local environment. Which, in the
end, is a distraction from things that matter.

This decision also generally impacts how CI images are created and thus the packaging
of the final product.

## Decision Drivers

* local environment consistent with the one CI uses
* local environment easy to set up for engineers on the team, with as little manual steps
  as possible
* local environment set up ideally does not require platform-specific knowledge and is
  consistent between different projects, so people new to platform X can set up
  environment for project built on top of it

## Considered Options

* Using Nix devshell
* Using Nix devshell + shared per-stack guidelines for people not using nix
* shared per-stack guidelines for people not using nix with an optional Nix devshell
* Earthly + shared per-stack guidelines for people not using nix with an optional Nix devshell
* Use Conda

(Note that in all cases we expect our developers to understand Docker as this is the primary packaging technology we use.)

## Decision Outcome

Chosen option: "Earthly + shared per-stack guidelines for people not using nix with an optional Nix devshell" because:
- Earthly is FAST and Consistent on CI and on a local machine.
- Earthly's underlying tech is Docker which most developers have widespread knowledge of (unlike nix)
  Docker is probably one of the most widely used technologies in the world.
- Earthly is also used by the Sidechains team which will lead to potential reuse that we could
  not achieve as easily if we were using solely Nix.
- Nix as a build system has a very steep learning curve, and can be difficult to modify.
- Like Nix Earthly behaves consistently across supported platforms (because docker)
- Like Nix Earthly does not interfere with system-level installed packages by design.
- Earthly by-design allows to set up all important tools, which are necessary in environment
- Earthly by-design supports incremental builds and extensive (remote) caching, which allows
  for quick experimentation and switching between projects without imposing big delays on
  engineers. (This was in practice demostrably not true of Nix - changing branches was SLOW.)
- Using standard images based on debian rather than Nix created images is less surprising for our
  users. (Security scanning can have difficulties understanding nix images.)

### Positive Consequences

* Single, uniform, easy-to-run, reliable style of environment definition across all
  projects. (Any CI target can be run locally easily).
* Increased familiarity with Docker across engineers on the project.
* Little work done in github workflows (that was hard to debug).
* More and faster cache hits.
* Across developers, Earthly is rather unknown tool (but given it's a superset of Docker
  people should pick it up quickly. )
* Earthly documentation is pretty comprehensive and in many cases just defers to Docker documentation.
* Windows developers not using WSL2 might get further.
* Given the reduction on reliance on Nix, ideally there will be no overlap between flake.lock and other
  lock files (E.g. Cargo.lock). It's not ideal that we currently have to update cargo and nix when
  pulling in a new version.
* Last but not least: This fits with Midnight's values. I.e. we choose popular technologies that
  everyone is very familiar with such as Typescript to make dapps. Choosing a technology that
  under the hood everyone intuitively understands lowers the bar for external pull requests.

### Negative Consequences

* Time will be spent on battling issues coming either from different versions in use or specific local setup (but this has to be conterballanced by the time saved not waiting for nix.)

* Earthly does NOT set up a local dev environment.
  For this reason standard per-stack conventions should be used or a simple Nix shell for installing
  required components for basic compile and run/debug. (use nix less, just for simple stuff)

* Time will be spent on issues where Earthly running on CI or running locally in a container doesn't match
  the user's setup (if they don't use the nix shell). But at least it will be painfully obvious that it's
  their computer's setup that's at fault.
  (If there is a discrepancy between Earthly running on the local machine and the user's setup
  one can put `RUN false` and invoke with a `-i` flag and you will be dropped into a shell at that point
  and diagnose what the difference is.)

## Validation

By end of September 2024 all existing and active Midnight repositories should have their
CI defined in an Earthfile. A Nix devshell should be made available for those that want to use it,
but where possible it should defer to stack specific conventions for which tool versions to install.
(I.e. the nix devshells should be as minimal as possible to be fast to enter and more likely to be cached.
In particular devshells that depend on devshells that depend on devshells should be avoided where possible
and heavy computation of things like public parameters should be cached in a shared image rather than being constantly recomputed. - Earthly makes it very easy to pull files out of images and save them locally)

## Pros and Cons of the Options

### Using Nix devshell

This option was tried for several years and had certain shortfalls:
- People complain of sometimes 30 mins+ to wait for nix to build the environment.
- When people got used to Nix they still found it hard. Nix is hard. You just won't believe how vastly, hugely, mind-bogglingly hard it is. I mean, you may think debugging Conda packages is hard, but that's just peanuts to Nix.
  E.g. how to switch which version of rustc we're using?
  This delayed releases when we hit nix issues (sometimes for days, sometimes a lot longer).
  While using nix is relatively easy (if slow), changing nix isn't easy. This is mostly down to the
  language's lazy evaluation which means IDEs etc. really can't give you much help.
  (Compare how much help `nix` gives you to `rustc`!)
- nix created images while theoretically 'more secure' as they had just what they needed in them,
  but the security scanning doesn't seem to handle them well.

### Using Conda

Anaconda is the only crossplatform packaging framework that can work on Windows as well as Mac and Unix.
Having used it for a year at another establishment I can confirm it's unsuitable because:
- It's very very slow.
- Making conda packages is non-trivial (considerably less fun than making nix packages).
- Nix is hands down a better packaging framework in every way except it doesn't support Windows.

### Using Nix devshell + shared per-stack guidelines for people not using nix

That option sounds very tempting, mostly because nix usage across developers can be
limited and nix has a reputation of a tool that has a very steep learning curve,
though in reality it would mean, that:
- there are slightly different tool versions in use locally and in Cicero
- more time needed for setting up development environment
- a lot of time spend on battling issues coming either from different versions in use or
  specific local setup

## More Information

This decision is a direct result of discussion that was held on [ticket](
https://input-output.atlassian.net/browse/PM-3860), partially on [Slack](
https://input-output-rnd.slack.com/archives/GEH5A0YLR/p1656425716597359)

[Guide](https://input-output.atlassian.net/wiki/spaces/MN/pages/3763798043/Troubleshooting+nix+build) with use cases about troubleshooting nix builds.
