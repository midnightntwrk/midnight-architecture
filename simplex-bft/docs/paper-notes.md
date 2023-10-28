# Message Size Complexity

Simplex makes an explicit claim of message size complexity that is at odds with the messages described in the protocol.

> “Each message is at most size $O(λ^ε · n)$ (since a notarization contains up to $n$ signatures of $O(λ^ε)$ size each, where $0 < ε ≤ 1$)” (Chan and Pass, 2023, p. 18)

The protocol describes four kinds of messages.  Three of them are explicitly defined, while one is informally mentioned.

> “For each iteration $h ∈ N$, an honest process $p$ will multicast at most one $\mathsf{propose}$ message, at most one vote message for a non-⊥ block, at most one of $⟨\mathsf{vote}, h, ⊥_h⟩_p$ and $⟨\mathsf{finalize}, h⟩_p$, and will relay their view of a notarized blockchain of height $h$ at most once” (Chan and Pass, 2023, p. 18)

Let's consider each message type in turn, starting with the assumption that every message is signed and therefore has a minimum size of $O(λ^ε)$.

➤ $⟨\mathsf{vote}, h, b_h⟩_p$ or $⟨\mathsf{vote}, h, ⊥_h⟩_p$
The notation $b_h$ represents a block.  Not a block hash, nor a block header.  A block can have arbitrary size, since it must include all transactions seen by the proposer that are not yet included in $b_0, \ldots, b_{h-1}$.  This cannot be assumed to fall $\leq O(λ^ε · n)$.  We could address this by, say, replacing $b$ with $H(b)$, but then we are straying from the explicit protocol of the paper.

➤ $⟨\mathsf{finalize}, h⟩_p$
This message's size is $O(1)$.

➤ $⟨\mathsf{propose}, h, b_0, \ldots , b_{h−1}, b_h, S⟩_p$
So many problems here.  Each $b_i$ is a full block with all its transactions.  Every proposal is multicasting the entire ledger.  Further, by the definition “$S$ is a set of notarizations, one for each block $b_1, \ldots , b_h$” (Chan and Pass, 2023, p. 9), the size of $S$ alone is no less than $O(h · λ^ε · n)$, which is far greater than the given upper limit $O(λ^ε · n)$.  So, even if we were to replace each $b_i$ for $i < h$ with $H(b_i)$, we could not meet the space complexity target.

➤ *relay their view of a notarized blockchain*
This message plays an important role in the liveness proof, but is never properly defined.  What does the paper mean here by a *view* of a notarized blockchain?

Both the *propose* and *view* messages seem to require a process to share a *notarized blockchain* or a *view* of one. Can anyone infer from the paper what data representation for this information content that is no larger than $n$ signatures?
