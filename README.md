# Midnight Architecture

This is a repository of the Midnight software architecture documents. While each component
repository may have its own local documentation, this repo includes the specification of
each component in standard terms and documents the flows, features, and deployments
supported by the system.

What are *flows*, *features*, *components* and so forth? The essential terminology of our
architectural elements are defined in [definitions](definitions.md).

## TOC

* [Definitions of Architectural Elements](./definitions.md)
* [Decision Record](./adrs)
* [Midnight Architecture Overview](./overview)
* [User Flows](./user-flows/README.md)
    - [dAPP-User Flows](./user-flows/dapp-user/README.md)
        - [Flow: dApp User Generating a Transaction](./user-flows/dapp-user/dApp%20User%20Generating%20a%20Transaction.md)
* [Components](./components/README.md)
    - [Wallet Engine](./components/WalletEngine/README.md)
    - [Client SDK](./components/ClientSDK)
    - [Wallet Browser Extension](./components/WalletBrowserExtension/README.md)
    - [Wallet Backend](./components/WalletBackend/README.md)
    - [Transaction Kernel](./components/kernel/README.md)
    - Lares Runtime
        - [Private State Management](./components/lares/private-state-management/README.md)
* [API’s and Common Types](./apis-and-common-types/README.org)
* Example dApps
    - [Lares Private e-Voting Example](./example-dapps/evoting/README.org)
* [Languages Architecture](./languages/README.org)
    - [Abcird](./languages/abcird.org)
    - [Reach](/languages/reach.org)
* [Flowlets](./flowlets/README.md)
* [Architectural Issue Tracking](./risks-and-issues.md)

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


