# Midnight Architecture

> **⚠️ This repository is archived.** It is kept as a historical record of early Midnight
> architecture documents and is no longer maintained. Content here may be out of date.
>
> Changes to the Midnight protocol now go through the open-source improvement-proposal
> process: <https://github.com/midnightntwrk/midnight-improvement-proposals>.

This is a repository of the Midnight software architecture documents. While each component
repository may have its own local documentation, this repo includes the specification of
each component in standard terms and documents the flows, features, and deployments
supported by the system.

What are *flows*, *features*, *components* and so forth? The essential terminology of our
architectural elements are defined in [definitions](definitions.md).

## TOC

* [Definitions of Architectural Elements](./definitions.md)
* [Decision Record](./adrs)
* [Proposals](./proposals/)
* [Midnight Architecture Overview](./overview)
* [Deployments](./deployments)
* [User Flows](./user-flows/README.md)
    - [dAPP-User Flows](./user-flows/dapp-user/README.md)
        - [Flow: dApp User Generating a Transaction](./user-flows/dapp-user/dApp%20User%20Generating%20a%20Transaction.md)
* [Components](./components/README.md)
    - [Wallet Engine](./components/WalletEngine/README.md)
    - [Client SDK](./components/ClientSDK)
    - [Indexer](./components/PubSubIndexer)
    - [Wallet Browser Extension](./components/WalletBrowserExtension/README.md)
    - [Wallet Backend](./components/WalletBackend/README.md)
    - [Transaction Kernel](./components/kernel/README.md)
    - Lares Runtime
        - [Private State Management](./components/lares/private-state-management/README.md)
* [Specifications](./specification)
  - [Metadata](./specification/Metadata.md)
* [API’s and Common Types](./apis-and-common-types/README.org)
  - [Transaction Submission](./apis-and-common-types/transaction-submission/Readme.md)
  - [Event Log](./apis-and-common-types/event-log/Readme.md)
  - [Metadata](./apis-and-common-types/metadata)
* Example dApps
    - [Lares Private e-Voting Example](./example-dapps/evoting/README.org)
    - [Private DAO Example](./example-dapps/dao/)
* [Languages Architecture](./languages/README.org)
    - [Abcird](./languages/abcird.org)
    - [Reach](/languages/reach.org)
* [Flowlets](./flowlets/README.md)
  * [Native Tokens](./flowlets/native-tokens/README.md)
* [Architectural Issue Tracking](./risks-and-issues.md)


## How to propose changes

This repository is archived and no longer accepts updates. The former Jira / Tech Assembly
process is retired. To propose a change to the Midnight protocol, open a Midnight
Improvement Proposal (MIP) at
<https://github.com/midnightntwrk/midnight-improvement-proposals>.

The historical process is described in the ADRs:
  - [0, about using ADRs in the first place](./adrs/0000-use-adrs-and-adrgen.md)
  - [1, about PR template](./adrs/0001-extended-pr-template.md)

## Tools

Documents use text-based diagrams to enable version control of key illustrations. The
tools used include:

- [plantUML](https://plantuml.com/)
- [graphviz](https://www.graphviz.org/) (used by plantUML)

**Please use local installations of these tools rather than pasting IOHK confidential data
into web-hosted versions.**

Additionally, to help with maintaining Decision Record documents -
an [adrgen](https://github.com/asiermarques/adrgen)
is used.

You can access all the tools needed with nix and (optional) direnv. Having a working nix
installation, and enabled flakes and nix command features (e.g. by adding
line `experimental-features = nix-command flakes` to `~/.config/nix/nix.conf` file), you
can run `nix develop` or `direnv allow` to enter a shell environment, where they all are
available on `$PATH`.
