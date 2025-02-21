# DApp Connector API

DApps need an API to interact with wallets, so that users can confirm their transactions and use tokens in DApp interactions. What makes this line of interaction particularly important is an asymmetry in trust and data needed to actually implement useful interactions: wallet software is usually carefully selected and receives a lot of trust from its user, while DApps may be of varying quality, their goals will vary, as well as approach to overall security and privacy (including outright malicious intents). At the same time - many honest DApps, to provide good user experience or simply basic functionality for the kind of DApp, will require access to data, that users should not share lightly in many cases, like balances of (shielded) tokens or transactions found relevant for the wallet.

What raises additional concern to this API is potential presence of multiple browser extensions wanting to install their instances of the API in the DApp website, some of which might be malicious. 

## API Design

> [!note]
> Code snippets below are defined in TypeScript, this enables easy consistency check between the specification here, and definition in the DApp Connector API package: https://github.com/input-output-hk/midnight-dapp-connector-api / https://www.npmjs.com/package/@midnight-ntwrk/dapp-connector-api

> [!note] 
> In certain ways, the design of this API borrows from the [Cardano DApp Connector API defined in CIP-30](https://cips.cardano.org/cip/CIP-0030). This is a deliberate decision, to make the API look familiar to Cardano DApp developers.

### Initial API

The initial API of a wallet is an object containing information about the wallet, as well as a method allowing to connect to it or check if a connection is established.

```ts
import { type NetworkId } from '@midnight-ntwrk/midnight-js-network-id';

type InitialAPI = {
  /**
   * Wallet name, expected to be displayed to the user
   */  
  name: string;
  /**
   * Wallet icon, as an URL, either reference to a hosted resource, or a base64 encoded data URL
   */
  icon: string;
  /**
   * Version of the API implemented and installed, string containing a version of the API package @midnight-ntwrk/dapp-connector-api that was used in implementation
   */
  apiVersion: string;
  /**
   * Status of an existing connection to wallet
   */
  connectionStatus(): Promise<ConnectionStatus>;
  /**
   * Connect to wallet, hinting desired network id
   */
  connect: (networkId: string | NetworkId) => Promise<ConnectedAPI>;
};

type ConnectionStatus =
  | {
      /**
       * Connection is established to following network id
       */
      status: "connected";
      networkId: string | NetworkId;
    }
  | {
      /**
       * Connection is not established (e.g. if `connect` was not called yet or the connection was lost)
       */
      status: "disconnected";
    }
  | {
      /**
       * Connection was entirely rejected by the wallet or user
       */
      status: "rejected";
    };
```

Then, to allow DApp to access the API, Wallet installs its initial API under global `window.midnight` object:

```ts
declare global {
  interface Window {
    midnight?: {
      [key: string]: InitialAPI;
    };
  }
}
```

Here, some responsibilities lie on both DApp and Wallet:
1. The DApp should not rely on the contents of the key in the `midnight` object, as it can be arbitrary string and defined arbitrarily by the implementor. The wallet can use their name as the identifier, but a randomized string, like UUID is equally valid option.
2. In case multiple wallets install their API - the DApp should present the user with way to choose the wallet to use for the interaction
3. From DApp perspective, both name and icon are potentially malicious input, and thus - they should be sanitized before being presented to the user. In particular - the icon should always be rendered inside an `img` tag to prevent XSS from JavaScript embedded in SVG.
4. DApp should always check the `apiVersion` against supported range of versions (following semver semantics)
5. Wallet must report exact version of the `@midnight-ntwrk/dapp-connector-api` package it implemented
6. If the Wallet implements multiple incompatible versions of the API simultanously (which is a possible case during transition period related to a hard-fork), Wallet must provide multiple entries in the `midnight` object.
7. When connecting:
   - DApp must provide network id it wants to connect to
   - Wallet must reject connection request if it can't connect to the network with id provided by the DApp
   - It is up to wallet to define their approach to different networks, they can support connecting to multiple networks simultanously, they can connect to only single network at a time and ask user to make the switch and then reload the DApp, etc.
   - Wallet should ask user for the scope of permissions provided to the DApp and indicate what network the DApp wants to connect to. It is up to the wallet implementation to decide how exactly and when exactly user is asked for confirmation

### Connected API

Once connected, wallet provides connected API - one which allow for specific interaction with the wallet.

The connected API consists of couple of parts, each always present, but its methods may throw an error indicating lack of permission:
```ts
type ShieldedBalance = {
  getShieldedBalances(): Promise<Record<TokenType, bigint>>;
};

type UnshishieldedBalance = {
  getUnshieldedBalances(): Promise<Record<TokenType, bigint>>;
};

type TxHistory = {
  getTxHistory(pageNumber: number, pageSize: number): Promise<HistoryEntry[]>;
};

type ShieldedAddress = {
  getShieldedAddresses(): Promise<{
    shieldedAddress: string;
    shieldedCoinPublicKey: string;
    shieldedEncryptionPublicKey: string;
  }>;
};

type DustAddress = {
    getDustAddress(): Promise<{
        dustAddress: string;
    }>;
}

type UnshieldedAddress = {
  getUnshieldedAddress(): Promise<{
    unshieldedAddress: string;
  }>;
};

type InitActions = {
  /**
   * Take transaction, add necessary inputs and outputs to remove imbalances from it, returning a transaction ready for submission
   */
  balanceTransaction(tx: string): Promise<{tx: string}>;
  /**
   * Initialize a transfer transaction with desired outputs
   */
  makeTransfer(desiredOutputs: DesiredOutput[]): Promise<{tx: string}>;
  /**
   * Initialize a transaction with unbalanced intent containing desired inputs and outputs.
   * Primary use-case for this method is to create a transaction, which inits a swap
   */
  makeIntent(intentId: number | "random", desiredInputs: DesiredInput[], desiredOutputs: DesiredOutput[]): Promise<{tx: string}>;
  /**
   * Sign provided data using key specified in the options
   */
  signData(data: string, options?: SignDataOptions): Promise<{ data: string; signature: string }>;
};

type Configuration = {
  /**  Indexer URI */
  indexerUri: string;
  /**  Indexer WebSocket URI */
  indexerWsUri: string;
  /**  Prover Server URI */
  proverServerUri: string;
  /**  Substrate URI */
  substrateNodeUri: string;

  /** Network id connected to - present here mostly for completness and to allow dapp validate it is connected to the network it wishes to */
  networkId: string | NetworkId;
};

type AccessConfiguration = {
  getConfiguration(): Promise<Configuration>;
}

type SubmitTransaction = {
    submitTransaction(tx: string): Promise<void>;
}

type ConnectedAPI = 
  & ShieldedBalance 
  & UnshieldedBalance 
  & TxHistory 
  & ShieldedAddress 
  & DustAddress 
  & UnshieldedAddress 
  & InitActions 
  & AccessConfiguration 
  & SubmitTransactions

type ExecutionStatus = Record<number, "Success" | "Failure">;

type TxStatus =
  | {
      /**
       * Transaction included in chain and finalized
       */
      status: "finalized";
      executionStatus: ExecutionStatus;
    }
  | {
      /**
       * Transaction included in chain and not finalized yet
       */
      status: "confirmed";
      executionStatus: ExecutionStatus;
    }
  | {
      /**
       * Transaction sent to network but is not known to be either confirmed or discarded yet
       */
      status: "pending";
    }
  | {
      /**
       * Transaction failed to be included in chain, e.g. because of TTL or some validity checks
       */
      status: "discarded";
    };

type HistoryEntry = { 
    /**
     * Hex-encoded hash of transaction
     */
    txHash: string; 
    txStatus: TxStatus 
};

type DesiredOutput = {
  kind: "shielded" | "unshielded";
  type: TokenType;
  value: bigint;
};

type DesiredInput = DesiredOutput;

type TokenType = string;

type SignDataKeyType = "unshielded";
type SignDataOptions = {
  keyType: SignDataKeyType;
};
```

The protocol that comes with this API is as follows:
1. The DApp should not assume presence of methods means granted permission, wallets might implement policy like "Ask on first use", as well as "Ask user upfront"
2. To let DApp clearly distinguish it is the case, wallet must return `PermissionRejected` error for a particular method
3. The way the API is compartmentalized is a possibility of how wallets can manage permissions, though wallets are free to implement more coarse-grained as well as more fine-grained permissions to limit access to certain actions or data.
4. When asked returning transaction (in methods `balanceTransaction`, `makeTransfer` or `makeIntent`), wallet must always return a transaction ready to be submitted to the network, that is one that is sealed, contains signatures, and contains proofs.
5. The DApp, when asking wallet to submit a transaction, needs to provide a transaction ready to be submitted to the network, that is one that is sealed, contains signatures, and contains proofs.
6. The DApp, when asking wallet to balance a transaction, needs to provide a transaction, which is not sealed and does not contain signatures, but already contains proof, otherwise wallet won't be able to deserialize it and complement with necessary tokens.
7. The DApp, when asking wallet to balance a transaction, needs to provide a transaction compatible with network id indicated in the configuration object.
8. The DApp should connect to indexer and proving server indicated by configuration, therefore wallet should not limit access to the `getConfiguration` method unless absolutely necessary.
9. The DApp can double check if `networkId` present in configuration matches the requested one
10. In the configuration object, the wallet must point to service deployments, which are compatible with network id present, and preferably are the same that the wallet itself uses for particular network.
11. Wallet must provide data like token types and addresses in format compatible with network id present in the configuration object.
12. Wallet can reconcile data like balances from multiple accounts, in such case wallet must ensure data consistency, mostly related to reported balances, so that they can actually be used in a transaction, if only it fits single transaction and user does permits so.
13. Wallet needs to ensure that balances reported in `getShieldedBalances` and `getUnshieldedBalances` methods are available balances, which means balances wallet is willing to allow spending in transactions. This allows DApps to rely on the balance checks (to certain extent at least since race conditions are a possibility) in their logic.


### Errors

Errors are modelled with a dedicated enumeration of codes:

```ts
const ErrorCodes = {
  /** The dapp connector wasn't able to process the request */
  InternalError: 'InternalError',
  /** The user rejected the request */
  Rejected: 'Rejected',
  /** Can be thrown in various circumstances, e.g. one being a malformed transaction */
  InvalidRequest: 'InvalidRequest',
  /** Permission to perform action was rejected. */
  PermissionRejected: 'PermissionRejected'
} as const;

type ErrorCode = (typeof ErrorCodes)[keyof typeof ErrorCodes];

type APIError = Error & {
  /** indication it is a DApp Connector Error */  
  type: 'DAppConnectorAPIError';
  /** The code of the error that's thrown */
  code: ErrorCode;
  /** The reason the error is thrown */
  reason: string;
}
```

Codes `InternalError` and `InvalidRequest` are rather simple in interpretation, along the lines of guidelines behind usage of 4xx and 5xx error codes in HTTP.
There is a notable difference in semantics between `Rejected` and `PermissionRejected` codes: `Rejected` indicates one-time rejection (e.g. user rejecting a transaction after seeing the real cost of it), while `PermissionRejected` indicates general preference to not permit particular action. Because of this - the connected DApp can expect, that once `PermissionRejected` is observed for a particular part of the API, it will keep being returned for the session (that is - until the browser window/tab with the DApp page is closed).

`APIError` type is not modelled as a class here, because it would be impossible to share single class definition between the DApp and the Wallet and in result - `instanceof` checks would not work as expected. Wallets can implement the type as a class extending native `Error`.

## Future direction

Although not part of the specification at this moment, there are some additions to the API expected in the future. They are not perceived as crucial and are expected to be mostly supplementary improvements.

### EIP-6963-like provider installation and discovery

Current specification based on shared global object offers simplicity and familiarity. Though it might cause synchronization issues when multiple wallets try to install their APIs. One possible solution, at a cost of increased complexity on the DApp side (likely asking for a dedicated client library) is for wallets to install their APIs using events, like in [EIP-6963](https://eips.ethereum.org/EIPS/eip-6963).

### Custom extensions

In many cases wallets might want to expose additional APIs, which are not part of the standard yet - for example to perform real-world testing and to gather feedback. For such cases extensions API similar to the one specified in [CIP-0030](https://cips.cardano.org/cip/CIP-0030) could be defined.

### Structured data signing

DApp connector's ability to sign arbitrary data is crucial to enable plenty of use-cases. It faces a significant user experience issue - many times the data being signed will not be human-readable, preventing user from assesing what exactly is being signed. To change that, Ethereum has adopted [EIP-712](https://eips.ethereum.org/EIPS/eip-712), Midnight's DApp connector could be extended to similar functionality.