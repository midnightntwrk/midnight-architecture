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

## Decision Drivers

* local environment consistent with the one Cicero uses
* local environment easy to set up for engineers on the team, with as little manual steps
  as possible
* local environment set up ideally does not require platform-specific knowledge and is
  consistent between different projects, so people new to platform X can set up
  environment for project built on top of it

## Considered Options

* Using Nix devshell
* Using Nix devshell + shared per-stack guidelines for people not using nix

## Decision Outcome

Chosen option: "Using Nix devshell", because:
- it allows for definition of both local dev environment and Cicero action 
  environment in a single place
- Cicero is built with Nix, while it should be considered as an implementation detail, it
  is an important fact in this context
- While nix as a build system has a very steep learning curve, it is relatively easy to
  use for environment provisioning
- On the contrary to other provisioning systems Nix behaves consistently across supported
  platforms
- On the contrary to other provisioning systems, which can be used locally, Nix does not
  interfere with system-level installed packages by design
- There exists a good direnv integration for nix
- Nix by-design allows to set up all important tools, which are necessary in environment
- Nix by-design supports incremental builds and extensive (remote) caching, which allows
  for quick experimentation and switching between projects without imposing big delays on
  engineers
- Nix flakes allow using private repositories, which can help with nix code re-use across
  stacks and projects

### Positive Consequences

* single, uniform, easy-to-run, reliable style of environment definition across all
  projects
* high consistency with Cicero without any overhead
* increased familiarity with Nix across engineers on the project, which may improve
  communication and cooperation with DevX and SREs
* better understanding of Cicero across engineers being Cicero users

### Negative Consequences

* Across developers, Nix is rather unknown tool (Haskell developers are an exception)
* Nix documentation is generally lacking (though it is changing)
* Nix mental model may feel foreign sometimes, which affects how easy it is to pick for a
  newcomer

## Validation

By end of September 2022 all existing and active Midnight repositories should have their
environments defined only as Nix devshells that share environment definition with Cicero
and using other, stack-specific tools should happen only if character of the repository
justifies the case.

Since the ultimate goal is compatibility with Cicero, unless OS-specifics are involved,
there should not be Cicero actions or local flows failing because of versions/environment
mismatch.

## Pros and Cons of the Options

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
