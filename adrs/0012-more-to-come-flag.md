# 12. More-to-Come Flag on Ledger States in DApp API

## Status

Proposed

---

|-----------|------------------------------------------|
| date      | 2023-08-29                               |
| deciders  | Jon Rossie, Thomas Kerber, Andrzej Kopeć |
| consulted | Joseph Denman                            |

---

## Context and Problem Statement

Let's suppose you want to write a simple DApp that builds a set of all
its users.  The "contract" holds only the set of users, and it is
smart enough to be a proper set, with no duplicates.  When a new user
joins the set, that user is given the list of all the users who have
already joined.

Here's the problem: what does *already* mean in this context?  At what
point in time?  The contract's state evolves over time.
Hypothetically, the DApp would need only the contract address in order
to join the contract, and the Midnight system could scan the entire
blockchain to find it.  In reality, the DApp developer can capture the
ID of the transaction that actually deployed the contract, because no
information about the contract can exist prior to that.

Thus, the transaction ID of the deploying transaction provides a kind
of *lower bound* on the blocks where contract can appear, but what
about an upper bound?  Where is the latest information?  There is no
way for a new user of the DApp to have the "most recent" transaction
ID for the contract.  In fact, there is likely to be no way to do
better than starting with the initial deployment's transaction ID and
scanning forward through the remainder of the blockchain, unless a
more recent ID is stashed somewhere external to Midnight.

For DApps that want to report the latest information, it would be very
helpful to have a Midnight DApp API that provides the "most recent
committed" transaction for a contract.  The big caveat for any such
API, though, is that "most recent" could be out-of-date immediately
after being reported.

Instead, DApps are better understood as reactive systems, always
receiving updates about their contracts.  Rather than functional APIs
that ask "What is the current state?" and expect an immediate answer,
Midnight will have to provide APIs that subscribe to information about
contracts and react to published updates about them, whenever they
happen to appear.  This makes it difficult to write simple
command-line DApps that expect to run and terminate.  Typical
user-facing web applications should be entirely reactive, but any
indexer of the blockchain does, in fact, know whether it has reached
the current horizon of finalized blocks, and it should be able to
report this information back to DApps.  Even reactive DApps want to
know when they are definitely *not* working with the latest
information.

Aside: You might expect that one way to get around the problem of
ever-evolving contracts is to allow "getter" circuits to be built into
the contract code, extracting contract state in the regular flow of
transactions.  Thus, a programmer could submit a transaction to get
the state and know that the returned information was in-order with
respect to a sequence of transactions.  This idea turns out to be a
dead end.  The returned value of a circuit is part of its transcript,
so there is no way to submit such a transaction without already
knowing its correct return value.  Contract state really must be
observed from *outside* the transaction sequence.

## Decision Drivers

* Usability of the Midnight SDK for command-line and non-interactive DApps

## Considered Options

* **More-to-Come Flag**: Make available to the programmer some sort of
  boolean or enumeration value on the stream of ledger states produced
  by the DApp runtime/backend.  The value conveys to the DApp that
  additional states follow immediately.
* **Reactive DApps Only**: Train programmers to create DApps that always
  handle new ledger states as the flow in and never assume that that
  the last seen state represents "current" reality in any way.

## Decision Outcome

No decision yet.

## Pros and Cons of the Options

### More-to-Come Flag

* Pro: Short-running or command-line DApps can consume ledger states
  as long as the "more-to-come" flag is set, arriving at a state that
  reflects recent reality.
* Con: There is no true "current" reality, and programmers might think
  that an unset "more-to-come" flag indicates absolute truth about the
  contract, relative to some mythical shared clock.
* Con: If the queue is never quite drained, the flag could always be
  set, and a supposedly short-running DApp to run indefinitely.  This
  problem can be mitigated by setting an upper-bound in the DApp on
  the time spent processing updates or the number of updates.

### Reactive DApps Only

* Pro: Anything other than a properly reactive DApp is an
  approximation, so forcing the programmers to work in a purely
  reactive setting leads to better DApps.
* Con: Simple examples and command-line DApps must always be given
  with apologies for their failure to work as expected.
