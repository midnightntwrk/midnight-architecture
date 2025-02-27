# Key derivation and address format reference

This small project is a reference implementation of key derivation for Midnight Wallet and address formatting. As such - it is used to generate test vectors.

> [!WARNING] 
> It optimizes for readability and simplicity at a cost of security!
> Scalar operations are not constant time and there is no attempt at cleaning memory from unnecessary copies of the secret key or data used to generate it.

## Test vectors format

### `addresses.json`

```ts
type HexString = string; // Hex-encoded data in string
type Bech32m = string; // Address encoded in Bech32m

type NetworkId = string | null | "test" | "dev" | "undeployed"; // Either a well-known or arbitrary network id

type AddressEntry = {
  /**
   * Exact data (hex-encoded), which is encoded in the address. It is thought to enable easy roundtrip check along the lines of:
   * assert(bech32.decode(bech32.encode(hex, context), context) == hex);
   */ 
  hex: HexString;
  /**
   * Bech32m-encoded address of given type and with network id present in the entry
   */
  bech32m: Bech32m;
}

type Entry = {
  /**
   * Source data used to derive keys and addresses.
   */
  seed: HexString;
  /**
   * Network id used to encode addresses
   */
  networkId: NetworkId;

  unshieldedAddress: AddressEntry;
  shieldedAddress: AddressEntry;
  shieldedESK: AddressEntry;
  shieldedCPK: AddressEntry;
};
```

### `keyDerivation.json`

```ts
type HexString = string; // Hex-encoded data in string
type BigNumberString = string; // String-encoded big number


type Entry = {
  /**
   * Source material used to derive keys, in case of unshielded keys, it is the secret key itself
   */
  seed: HexString,
  unshielded: {
    /**
     * Unshielded secret key, equal to seed, null if not valid secret key
     */
    secretKey: HexString | null,
    /**
     * Unshielded public/verification key, null if secret key invalid
     */
    publicKey: HexString | null,
  },
  encryption: {
    /**
     * Hex-encoded bytes of the secret key
     */
    secretKeyRepr: HexString,
    /**
     * Numeric representation of the key
     */
    secretKeyDecimal: BigNumberString,
    /**
     * Binary data being output of the hashing step, before interpreting as number and taking modulo
     */
    secretKeyIntermediateBytes: esk.intermediateBytes.toString("hex"),
  },
  dust: {
    /**
     * Hex-encoded bytes of the secret key
     */
    secretKeyRepr: HexString,
    /**
     * Numeric representation of the key
     */
    secretKeyDecimal: BigNumberString,
    /**
     * Binary data being output of the hashing step, before interpreting as number and taking modulo
     */
    secretKeyIntermediateBytes: esk.intermediateBytes.toString("hex"),
  },
  coin: {
    /**
     * Hex-encoded bytes of the secret key
     */
    secretKey: HexString,
    /**
     * Hex-encoded bytes of the public key
     */
    publicKey: HexString,
  },
};

```