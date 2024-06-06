# Proposal 0013: Shared configuration management

This is a template for writing new Midnight Architecture Proposals.  We want
this template to be lightweight, so that it does not impede the process of
capturing the proposals, and we to evolve this template over the time, as we
figure out the process of proposing changes to our architecture.

## Problem Statement

There are couple of pieces of configuration, which are scattered and almost identical across many repositories. Most notable are:

- network connection configuration - nodes to submit transaction, indexer location, related network id
- docker compose files used in local development and testing (usually with test containers)

Every update to deployments or configuration of services needed, or even upgrading those services and finding compatible sets of them is very tedious, time-consuming and repetetive work, with significant lead times observed too, including released examples not able to connect to officially supported networks.

## Possible options

There are multiple ways of managing this, and they differ depending on the configuration to manage as well as amount of automation needed in order to work well.

General possibilities seem to be, each one having possible variants:

- building a centralized artifact
- re-using existing charts
- implementing service discovery

### Option -  Building a centralized artifact

It definitely is the easiest option, and the one, which would work well both for network configuration and docker compose files. Though, there are 2 cases, which require mitigation:

1. Managing Lace wallet configuration, with embedding the default network configuration, as well as enabling easy switch to one of private networks like QA-nets
2. Publishing example applications either in a pre-configured way or making it very easy for them to be configured within tutorial boundaries, and then reconfigured for testing purposes

It could look like a reposiutory, which defines necessary files, and has CI defined to generate e.g. internal NPM package(s) (as in - published only to github registry, not passed further to npm) as well as public NPM packages (as in - published to NPM) with different contents (extended with private environments or limited to public ones only). The network configuration could be a separate file per network following a well-defined schema (or a definition in e.g. TypeScript); docker compose configuration could make usage of includes and profiles so that updates of specific components are easier scoped and the possibility of creating different configurations is maintained (testcointainer support both profiles and ability to run only specified services).

It would be possible to e.g. provide CLI tool, which extracts those files for the official environments, and embeds them in Lace or example applications. This would be additional friction though in their build process, but at the same time - it would simplify the management significantly.

A natural consequence of this approach would be forced versioning and a need to perform explicit upgrade step in case of backward-incompatible changes.

Initially, this approach could be implemented manually for both network configuration and the docker compose definitions. At later stage, it seems reasonable to try to source data from other places:

- network configuration from midnight-gitops repository, either directly from the code (if possible) or by inspecting environment
- update docker compose files with usage of Renovate (<https://docs.renovatebot.com/docker/#docker>)
- source pieces of docker compose files from midnight-charts repository, to the extent possible, so that regular updates of charts trigger updates of docker compose files

### Option - Re-using existing charts

If helm charts are adjusted to work testing scenarios well too, one could try to adapt container orchestration for tests to be done using a development kubernetes cluster.

Regardless of the place to run such a cluster (on cloud, dedicated cluster for a test suite or local, like the one built into docker desktop), such option seems to create more issues to be solved with automation, than solutions. Not mentioning need to adapt many tests to not use testcontainers anymore (Because <https://testcontainers.com/modules/k3s/> is only available for JVM, Go and .NET at the moment of writing).

### Option - Rely on convention

Given environment name, all public-facing URLs are fully standarized, reducing configuration needed to a function deriving URLs of specific services.

### Option - Implementing service discovery

Given environment name, there would be a convention and standarised API available to discover deployed services in the environment. For the network configuration, it could simplify some areas a lot just by relying on the fact, that regardless of exact connections and URL, it would be possible to discover services based on API/capabilities/type of service needed. Such approach should also allow quicker reaction to deployment changes. Possible issue though would be that publicly available code should not use the service discovery, and thus - likely require a build step capturing the configuration from the environment (as mentioned as a next stage for [option with centralized artifact](#option----building-a-centralized-artifact)).

A significant advantage of this option is that it will be possible to deploy ad-hoc networks with varying configurations, and still be able to perform the same set of tests as long as client code is compatible with the network.

## Proposed changes

Start with centralized artifacts approach: one for docker compose files, and the other one for network configuration. One meeting following criteria:

- manual updates
- automated publishing
- versioned
- available as npm package (because significant majority, if not all clients are TS code today)
- possibility to easily extract configuration of public networks (like devnet or testnet) into files (preferably through a CLI in the npm package), so that projects like example dapps or Lace wallet builds can easily be built with the needed configuration without leaking information about non-public environments (like QA-nets)

Once package is created and clients migrated - revisit approach after couple of sprints, to see whether this approach is enough, or maybe some refinements are needed.

## Desired Result

1. Noticeably less work put into maintenance and upgrades of configuration of network connection and testing environments.
2. Reduced delay from updating deployment/services to apps ready to use those updates.

## Questions, concerns

### Should this proposal cover genesis block definition, shared cryptographic parameters, etc.?

This kind of data seem to fit nicely under the network configuration, and thus - eventually the artifact and successor approaches should provide access to them.
