# Metadata Server API

Metadata servers are likely to serve metadata of many types and purposes. Thus, while at the time of writing, only token metadata is being specified, server API needs to be extensible enough to allow serving other kinds of metadata in the future, without necessarily being limited by this specification.

For that reason there are a couple of decisions being made around the API, defined in the [`API.graphql`](./API.graphql) file:
1. It is a GraphQL API
2. The GraphQL schema defines common metadata, meant to be common for all kinds of metadata introduced, as well as specific token metadata
3. There are 2 separate queries defined: one for arbitrary metadata (e.g. if client only has subject, but does not know, what type it is) and second one for token metadata specifically
4. The API specified is limited to certain elements

## GraphQL API

Within Midnight architecture, GraphQL is the technology employed to let clients like wallets, DApps or explorers, interact with Indexer. Not only it is extensible and flexible, but also it allows to extend Indexer API with connections between existing queries (like contracts) to metadata.

GraphQL also allows for introspection or generating the schema, as well as defining the schema upfront, which makes it a good fit (in terms of developer experience) for an API specification, which is meant to be often extended in the future. 

## Common metadata extraction

It is certain, that more kinds of objects will require their metadata be stored and served. For that reason the API aims to define the bare minimum of shared schema, which allows to future-proof the API a bit.

## Separate query for token metadata

Within framework of GraphQL types, this seems to be the best option to guarantee client, that token metadata will be served

## Only certain use-cases supported

GraphQL is a flexible technology and easily accommodates additions to the API. For that reason the API specified focuses on essentials, allowing to expand it as needed
