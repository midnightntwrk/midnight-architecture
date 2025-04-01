import * as ledger from "@midnight-ntwrk/ledger";
import { bech32m } from "@scure/base";

export const Bech32m: unique symbol = Symbol("Bech32m");

export type FormatContext = {
  networkId: string | null;
};

export class MidnightBech32m {
  public static readonly prefix = "mn";

  static validateSegment(segmentName: string, segment: string): void {
    const result = /^[A-Za-z1-9\-]+$/.test(segment);
    if (!result) {
      throw new Error(
        `Segment ${segmentName}: ${segment} contains disallowed characters. Allowed characters are only numbers, latin letters and a hyphen`,
      );
    }
  }

  static parse(bech32string: string): MidnightBech32m {
    const bech32parsed = bech32m.decodeToBytes(bech32string);
    const [prefix, type, network = null] = bech32parsed.prefix.split("_");
    if (prefix != MidnightBech32m.prefix) {
      throw new Error(`Expected prefix ${MidnightBech32m.prefix}`);
    }
    if (type == undefined) {
      throw new Error(`Did not find address type information`);
    }
    MidnightBech32m.validateSegment("type", type);
    if (network != null) {
      MidnightBech32m.validateSegment("network", network);
    }

    return new MidnightBech32m(type, network, Buffer.from(bech32parsed.bytes));
  }

  public readonly type: string;
  public readonly network: string | null;
  public readonly data: Buffer;

  constructor(type: string, network: string | null, data: Buffer) {
    MidnightBech32m.validateSegment("type", type);
    if (network != null) {
      MidnightBech32m.validateSegment("network", network);
    }

    this.type = type;
    this.network = network;
    this.data = data;
  }

  toString(): string {
    const networkSegment = this.network == null ? "" : `_${this.network}`;
    return bech32m.encode(
      `${MidnightBech32m.prefix}_${this.type}${networkSegment}`,
      bech32m.toWords(this.data),
      false,
    );
  }
}

export class Bech32mCodec<T> {
  public readonly type: string;
  public readonly dataToBytes: (data: T) => Buffer;
  public readonly dataFromBytes: (bytes: Buffer) => T;

  constructor(type: string, dataToBytes: (data: T) => Buffer, dataFromBytes: (bytes: Buffer) => T) {
    this.type = type;
    this.dataToBytes = dataToBytes;
    this.dataFromBytes = dataFromBytes;
  }

  encode(context: FormatContext, data: T): MidnightBech32m {
    return new MidnightBech32m(this.type, context.networkId, this.dataToBytes(data));
  }

  decode(context: FormatContext, repr: MidnightBech32m): T {
    if (repr.type != this.type) {
      throw new Error(`Expected type ${this.type}, got ${repr.type}`);
    }
    if (context.networkId != repr.network) {
      throw new Error(
        `Expected ${context.networkId ?? "mainnet"} address, got ${repr.network ?? "mainnet"} one`,
      );
    }
    return this.dataFromBytes(repr.data);
  }
}

export class ShieldedAddress {
  static codec = new Bech32mCodec<ShieldedAddress>(
    "shield-addr",
    (addr) => Buffer.concat([addr.coinPublicKey.data, addr.encryptionPublicKey]),
    (bytes) => {
      const coinPublicKey = new ShieldedCoinPublicKey(
        bytes.subarray(0, ShieldedCoinPublicKey.length),
      );
      const encryptionPublicKey = bytes.subarray(ShieldedCoinPublicKey.length);
      return new ShieldedAddress(coinPublicKey, encryptionPublicKey);
    },
  );

  [Bech32m] = ShieldedAddress.codec;

  public readonly coinPublicKey: ShieldedCoinPublicKey;
  public readonly encryptionPublicKey: Buffer;

  constructor(coinPublicKey: ShieldedCoinPublicKey, encryptionPublicKey: Buffer) {
    this.encryptionPublicKey = encryptionPublicKey;
    this.coinPublicKey = coinPublicKey;
  }
}

export class ShieldedEncryptionSecretKey {
  static codec = new Bech32mCodec<ShieldedEncryptionSecretKey>(
    "shield-esk",
    (esk) => esk.serialize(),
    (repr) =>
      new ShieldedEncryptionSecretKey(
        ledger.EncryptionSecretKey.deserialize(
          Buffer.concat([Buffer.of(0), repr]),
          ledger.NetworkId.Undeployed,
        ),
      ),
  );

  [Bech32m] = ShieldedEncryptionSecretKey.codec;

  private wrapped: ledger.EncryptionSecretKey;

  // There are some bits in serialization of field elements and elliptic curve points, that are hard to replicate
  // Thus using zswap implementation directly for serialization purposes
  constructor(toWrap: ledger.EncryptionSecretKey) {
    this.wrapped = toWrap;
  }

  serialize(): Buffer {
    return Buffer.from(
      this.wrapped
        .yesIKnowTheSecurityImplicationsOfThis_serialize(ledger.NetworkId.Undeployed)
        .subarray(1),
    );
  }
}

export class ShieldedCoinPublicKey {
  static readonly length = 32;

  static codec: Bech32mCodec<ShieldedCoinPublicKey> = new Bech32mCodec(
    "shield-cpk",
    (cpk) => cpk.data,
    (repr) => new ShieldedCoinPublicKey(repr),
  );

  [Bech32m] = ShieldedCoinPublicKey.codec;

  public readonly data: Buffer;

  constructor(data: Buffer) {
    if (data.length != ShieldedCoinPublicKey.length) {
      throw new Error("Coin public key needs to be 32 bytes long");
    }

    this.data = data;
  }
}
