### The Witness Problem

#### Problem Statement

Today witnesses are implemented in TypeScript and provided by the dApp at runtime. For example:

```compact
witness getSecretKey(): Bytes<32>;
```

requires a corresponding TypeScript implementation:

```typescript
const witnesses = {
    getSecretKey: (privateState) => {
        return [privateState, privateState.secretKey];
    }
};
```

This conflicts with dynamic cross-contract calls. When a caller makes a dynamic call, the dApp can't know at compile time:

1. Which contracts will be called (address read from ledger state)
2. What witnesses those contracts declare
3. What private state schema those witnesses need

If the callee needs a witness the dApp hasn't provided, execution fails.

#### Solution: Embedded Witnesses

The proposal: dynamically callable contracts embed their witness implementations in the contract itself, using Impact VM to execute them.
This shifts the current popular mental model of witnesses from "witness state and witnesses belong to the dApp and public state belongs to the contract" to
"witness state belongs to the dApp and witnesses and public state belong to the contract." The primary benefit of this approach is
that we get a portable executable representation for contract witnesses.

##### Most Witnesses Are Simple

The crucial observation is that, in practice, most witness implementations are straightforward. Consider this private membership contract:

```compact
import CompactStandardLibrary;

export ledger members: MerkleTree<8, Bytes<32>>;
export ledger count: Counter;

witness secretKey(): Bytes<32>;
witness membersPathOf(pk: Bytes<32>): Maybe<MerkleTreePath<8, Bytes<32>>>;

constructor() {}

export circuit join(): [] {
    const sk = secretKey();
    const pk = publicKey(sk);
    const path = disclose(membersPathOf(pk));
    assert(!path.is_some, "Already a member");
    members.insert(disclose(pk));
}

export circuit increment(): [] {
    const sk = secretKey();
    const pk = publicKey(sk);
    const path = disclose(membersPathOf(pk));
    assert(path.is_some &&
           members.checkRoot(disclose(merkleTreePathRoot<8, Bytes<32>>(path.value))) &&
           pk == path.value.leaf, "Not a member");
    count.increment(1);
}

export pure circuit publicKey(sk: Bytes<32>): Bytes<32> {
    return disclose(persistentHash<Vector<2, Bytes<32>>>([pad(32, "counter:pk:"), sk]));
}
```

The TypeScript witness implementations are straightforward:

```typescript
export const witnesses: Witnesses<PrivateState> = {
    secretKey({ privateState }) {
        return [privateState, privateState.sk];
    },
    membersPathOf({ privateState, ledger }, pk: Uint8Array) {
        const path = ledger.members.findPathForLeaf(pk);
        if (path) {
            return [privateState, { is_some: true, value: path }];
        }
        return [privateState, { is_some: false, value: dummyPath }];
    },
};
```

These witnesses do two things: read from private state and query ledger state. Both are expressible in Impact VM.

##### Private State as Witness Declarations

We allow `witness` declarations alongside `ledger` declarations:

```compact
ledger members: MerkleTree<8, Bytes<32>>;  // Public, on-chain
witness secretKey: Bytes<32>;              // Private, per-user
```

Here `secretKey` becomes a private state variable like a `Cell`, but stored in the user's off-chain storage rather
than on the ledger.

##### Witness Constructor

Private state needs to be initialized. Currently, the dApp does this, but for dynamic calls the user may never have
interacted with the callee contract before.

We introduce a **witness constructor** that initializes private state. It runs automatically when:

1. The interpreter encounters a dynamic call to a contract, and
2. The user does not have an existing private state for that contract.

The witness constructor may read the ledger state but may not modify it.

##### Kernel Witnesses

Some things can't be expressed within the contract, like generating cryptographically secure random bytes. We introduce **kernel witnesses**. These are primitive witnesses provided by the interpreter (like WebAssembly host functions):

- `rand<#N>(length: N): Bytes<N>` — Generate cryptographically secure random bytes.

##### Revised Contract

With embedded witnesses, the private membership contract becomes:

```compact
import CompactStandardLibrary;

export ledger members: MerkleTree<8, Bytes<32>>;
export ledger count: Counter;

witness secretKey: Bytes<32>;

ledger constructor() {}

witness constructor() {
  secretKey = kernel.witness.rand(32);
  const pk = publicKey(secretKey);
  const path = disclose(members.findPathForLeaf(pk));
  assert(!path.is_some, "Already a member");
}

export circuit join(): [] {
    const pk = publicKey(secretKey);
    members.insert(disclose(pk));
}

export circuit increment(): [] {
    const pk = publicKey(secretKey);
    const path = disclose(members.findPathForLeaf(pk));
    assert(path.is_some &&
           members.checkRoot(disclose(merkleTreePathRoot<8, Bytes<32>>(path.value))) &&
           pk == path.value.leaf, "Not a member");
    count.increment(1);
}

export pure circuit publicKey(secretKey: Bytes<32>): Bytes<32> {
    return disclose(persistentHash<Vector<2, Bytes<32>>>([pad(32, "counter:pk:"), secretKey]));
}
```

Kernel witness functions are accessed via `kernel.witness.rand()`. We can debate the name `kernel.witness`.
The contract above needs no additional TypeScript.

##### Exposing js-only Operations as Witness ADT Operations

Notice the `members.findPathForLeaf(pk)` call in the revised contract. It replaces the `membersPathOf` witness that was defined in the original TypeScript version. Currently, `findPathForLeaf` is a `js-only` function—available through JavaScript but not as a Compact ADT operation. For embedded witnesses to work, we need to expose these operations directly in Compact.

We would expose all `js-only` functions that witness implementations currently need as built-in ADT operations
callable within witness contexts. These operations:

- Are callable within witness constructors and witness contexts
- Generate private transcript entries
- Cannot modify ledger state

##### Updating Witness State Out of Band

It should be possible to make arbitrary modifications to witness state. The compiler
currently outputs a JavaScript object `Ledger` with constructor `ledger` that allows users to inspect ledger state of a contract from TypeScript.
All functions on `Ledger` are `get` (read) functions. The compiler could output a JavaScript object `Witness` has `get` functions
like `Ledger` but also `set` functions. This would give users a simple interface to make witness state modifications outside the contract.

##### The Turing Completeness Objection

One concern: Impact VM isn't Turing complete because it only supports bounded, forward-only control flow.
There is no mechanism for backward jumps. This limits what circuits can express compared to TypeScript witnesses, which can use unbounded iteration.

For witness execution (rehearsal mode), we could relax this constraint — add backward jump support to Impact VM. The Compact roadmap already includes an Impact surface language for custom ADTs; much of that could transfer to witnesses with the addition of backward jump and loop syntax.

##### Foreign Witnesses

We could keep the ability to define foreign witnesses as stubs (the current behavior). This introduces an obligation for the application to define the witness implementations. Keeping support for foreign witnesses would make embedded witnesses backwards compatible with current contracts. If the application makes a dynamic call to a contract with foreign witnesses without providing an implementation for those witnesses, the ZKIR interpreter would throw an error.

##### Shared Private State

*This section is speculative.*

Currently, each user-application pair has its own private state (via IndexedDB). But what if multiple dApps need to share private state—say, a suite of apps sharing user credentials, or a wallet managing keys across contracts?

Shared private state brings concurrency challenges: race conditions, contention, atomic updates. These are exactly the problems Impact VM solves for ledger state.

If witnesses run in Impact VM, we could apply the same transactional semantics to private state. Multiple apps could share private state with proper conflict resolution and atomic commits. Whether this is worth the complexity depends on real-world demand. For now, the per-application private state works fine, but Impact-based witnesses keep this option open.

#### Alternative: Witness Registry

Another approach is a witness registry where deployers register TypeScript implementations. The interpreter fetches the implementation when a dynamic call occurs.

**Pros:** Preserves TypeScript model; supports arbitrary expressiveness.
**Cons:** Needs a registry service; security concerns with fetched JavaScript; requires trusting the operator.

#### Alternative: No Witnesses in Dynamic Callees

The simplest option: just prohibit dynamic calls to contracts with witnesses.

**Pros:** No witness architecture changes; clean static/dynamic separation.
**Cons:** Very limiting—excludes private token transfers, anonymous voting, credentials from dynamic callability.

#### Recommendation

Embedded witnesses strike the best balance. For backward compatibility, contracts can still define foreign witnesses requiring TypeScript—but those contracts are static-only. A contract is dynamically callable if all its witnesses are embedded or kernel-provided.

Note that "no witnesses in dynamic callees" is actually more restrictive than embedded witnesses. Despite the Turing incompleteness of Impact VM, at least *some* contracts with witnesses can be called dynamically.
