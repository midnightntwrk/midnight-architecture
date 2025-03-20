Proposal 0018: NIGHT generates DUST
===================================

The problem, informally
-----------------------

DUST is a fuel used on Midnight to pay the transaction fees.  DUST is produced
from the ownership of NIGHT, Midnight's unshielded token.  Over time, every
NIGHT UTxO on Midnight produces DUST, assigning it to a specific *DUST address*.
Importantly, the *NIGHT address*, where the NIGHT UTxO resides, and the *DUST
address*, where DUST is allocated, need not be controlled by the same party.

NIGHT tokens can be transferred to Cardano.  NIGHT tokens on Cardano should
still be able to produce DUST if their Cardano owner desires so.  The owner of
NIGHT tokens may also want to trade DUST produced from their tokens to someone
else.

**NOTE:** Henceforth we will use the term "cNIGHT" to refer to NIGHT tokens
located on Cardano, and "mNIGHT" to refer to NIGHT tokens on Midnight.

Our goal is to create mechanisms that allow cNIGHT owners to manage DUST
generation.  By default, cNIGHT tokens do not generate DUST.  cNIGHT owner
should thus be able to enable DUST generation from their tokens.  They should
have the option to either delegate all of generated DUST to a DUST address on
Midnight - typically their own - or lease access to DUST generation to someone
else.  This leasing can be either managed manually by the cNIGHT owner or
delegated to a broker.  All of these actions must be recorded on Cardano and
then transferred to Midnight.

Motivation for recording the mappings on Cardano, rather than directly on
Midnight, is because people who first receive cNIGHT from a glacier drop will
not own any DUST, and thus would not be able to pay for a delegation on
Midnight.

Scenarios, informally
---------------------

We are assuming that a user has cNIGHT tokens in their Cardano wallet.  When it
comes to managing production of DUST from owned cNIGHT tokens, the cNIGHT owner
might engage in the following scenarios:

  1. **No DUST production**: cNIGHT owner has not expressed a wish for their
     tokens to produce any DUST, and so no DUST gets generated.

  2. **DUST produced for own use**: cNIGHT owner wants all of their tokens to
     always produce DUST for own use.

  3. **Self-managed leasing access to DUST production**: cNIGHT owner wants to
     lease access to DUST production to someone else, and they want to manage
     leasing without a 3rd party.

  4. **Broker-managed leasing access to DUST production**: cNIGHT owner wants to
     lease access to DUST production to someone else, but they do not want to
     manage making arrangements with potential buyers on their own.  Therefore,
     they wish to delegate the task of leasing access to DUST production and
     collecting payments to a 3rd party.

Personas
--------

Given the above scenarios, we assume the following personas:

  * **cNIGHT Owner**: An entity that holds cNIGHT tokens.

  * **cNIGHT DUST User**: cNIGHT Owner that generates DUST from all owned cNIGHT
    tokens to their own DUST address.

  * **cNIGHT Lessor**: cNIGHT Owner that wants to monetize DUST generated from
    their cNIGHT tokens by leasing access to DUST production.

  * **cNIGHT Lessee**: An entity that leases DUST production from a cNIGHT
    Lessor in order to receive DUST on Midnight.

  * **Broker**: an intermediary between cNIGHT Lessors and cNIGHT Lessees.

Any single person can be multiple personas.

Components
----------

Aside from above Personas, we also have the following system components:

  * **Observability layer**: observes cNIGHT balances and leasing on Cardano and
    makes this information available for Midnight.

  * **Midnight block producers**: entities permitted to construct Midnight
    system transactions based on observations made from Cardano.

  * **Midnight validators**: entities that verify the system transactions
    against the observability layer.

  * **Midnight ledger**: interprets the system transactions to implement
    requested DUST generation.

Correctness criteria of each scenario
-------------------------------------

### Scenario 1: No DUST production

cNIGHT owner does not wish for their cNIGHT tokens to be used for DUST
production.

Correctness criteria:

  * Owned cNIGHT tokens do not produce any DUST.

  * It must be the case that newly received cNIGHT tokens do not produce DUST.
    In other words, it *must not* be possible for other Cardano users to
    register DUST production on someone else's behalf.

### Scenario 2: DUST produced for own use

cNIGHT DUST User wants all of their cNIGHT tokens to always produce DUST and
have that DUST accumulated at a specified DUST address on Midnight.

Correctness criteria:

  * cNIGHT DUST User should be able to register for DUST production.
    Registration includes specifying a Cardano wallet that stores the cNIGHT
    tokens and a DUST address where the DUST should go.

  * Once a registration is made, all cNIGHT tokens stored in registered wallet
    at any given time should be automatically used for DUST production.

  * cNIGHT DUST User should be able to deregister their wallet from DUST
    production.

  * It must be impossible to perform registration or deregistration on someone
    else's behalf.  Only the wallet's owner may register it for DUST production
    and only that wallet's owner can later perform a deregistration.

  * At most one registration per Cardano wallet address should be permitted.

### Scenario 3: Self-managed leasing access to DUST production

cNIGHT Lessor wants to lease access to DUST production for some of their owned
cNIGHT tokens and wants manage the lease entirely on their own.  A single cNIGHT
Lessor may lease access to DUST production to multiple cNIGHT Lessees.  cNIGHT
Lessor commits to a lease end date but does not receive any (explicit) payments
on Cardano for the leased cNIGHT tokens.

Correctness criteria:

  * cNIGHT Lessor must be able to lease access to DUST production of an
    arbitrary amount of owned cNIGHT tokens to an arbitrary DUST address.

  * Each lease is a timed commitment.  We introduce the term "lease end date" to
    refer to the date that determines length of the lease of access to DUST
    production.  Once a cNIGHT Lessor commits to a certain lease end date, the
    lease cannot be modified or cancelled before that date passes.  However,
    cNIGHT Lessor is allowed to change ownership of cNIGHT tokens at any time,
    even if the tokens are currently leased to a cNIGHT Lessee.

  * cNIGHT Lessor is the only entity that can set the lease parameters (DUST
    address and lease end date) for their tokens.

  * It must be impossible to lease access to DUST production on someone else's
    behalf.  Only the cNIGHT Lessor may lease access to DUST production for
    owned cNIGHT tokens.

NOTE: A special case of this scenarios is when a cNIGHT Lessor sets the DUST
address to be their own.  This permits producing DUST from a predefined amount
of cNIGHT, as opposed to producing DUST from all owned cNIGHT, described in
Scenario 2.

### Scenario 4: Broker-managed leasing access to DUST production

cNIGHT Lessor wants to lease access to DUST production for some of their owned
cNIGHT tokens and delegate the lease management to a Broker.  Thus, a cNIGHT
Owner becomes a cNIGHT Lessor.  The Broker is responsible for leasing access to
DUST production obtained from multiple cNIGHT Lessors to multiple cNIGHT
Lessees.  cNIGHT Lessor wants to receive an explicit payment for the leases and
it is responsibility of the Broker to make such payments to the Lessor.

Correctness criteria:

  * cNIGHT Lessor should be able to lease access to DUST production from owned
    cNIGHT tokens.  cNIGHT Lessor should be able to set a unit price they wish
    to receive for leasing access to DUST production from a single cNIGHT token
    per unit of time.

  * cNIGHT Lessor should be able to delegate lease management to a Broker.
    Broker must not be able to embezzle entrusted cNIGHT tokens, for example by
    changing their ownership.

  * cNIGHT Lessee should be able to lease access to DUST production and indicate
    a DUST address to which the DUST should go on Midnight.  To lease the
    access, cNIGHT Lessee should pay the cNIGHT Lessor the requested price.

  * Broker is responsible for leasing access to DUST production to cNIGHT
    Lessees, ensuring that cNIGHT Lessors receive the price they requested and
    cNIGHT Lessees receive the access to DUST they paid for.  Broker may lease
    tokens obtained from one Lessor to multiple Lessees.  Conversely, cNIGHT
    Lessee might be leased tokens from multiple Lessors.

  * Delegation of lease management by a cNIGHT Lessor to a Broker is a timed
    commitment.  We use the term "broker lease end date" to refer to a date
    that says until when the Broker can manage cNIGHT Lessor's tokens.  Once a
    cNIGHT Lessor commits to a certain broker lease end date, the Broker has the
    exclusive rights to manage leasing access to DUST production from delegated
    tokens and the cNIGHT Lessor is not allowed to do anything that would
    prevent the Broker from leasing access to DUST production from delegated
    tokens.  Once the broker lease end date has passed, the cNIGHT Lessor must
    reclaim the rights to manage leasing access to DUST generation from their
    tokens.

  * cNIGHT Lessor is allowed to change ownership of cNIGHT tokens at any time,
    even if the tokens are currently managed by a Broker or leased to a cNIGHT
    Lessee.

  * Broker subleases access to DUST production from entrusted cNIGHT tokens to
    cNIGHT Lessees.  Sublease is a timed commitment.  We again use the term
    "lease end date", introduced in scenario 3, to refer to date that determines
    length of the lease.  Before the lease end date passes no one, neither the
    Broker nor the cNIGHT Lessor, can modify the lease in any way.  Lease end
    date may not extend beyond the broker lease end date.

  * Broker may voluntarily shorten the broker lease end date.

Proposed solutions
------------------

### Scenario 1: No DUST production

Requirements of this scenario are implicitly fulfilled if the cNIGHT Owner takes
no explicit actions required for producing DUST for own use or leasing access to
DUST production.  It is therefore the default behaviour for every cNIGHT Owner.

Correctness discussion:

  * Each of the proposed solutions for scenarios 2-4 requires the cNIGHT Owner
    to take explicit actions for the cNIGHT tokens to start producing DUST.
    This satisfies the correctness criteria for scenario 1, i.e. if the cNIGHT
    Owner takes no action then no DUST is generated.  Additionally, no one but
    the cNIGHT Owner can take the actions required to begin DUST production,
    which again follows from the correctness criteria for scenarios 2-4.

### Scenario 2: DUST produced for own use

To address the requirements of scenario 2, we propose a solution, whose key
element is a mapping validator (a Plutus smart contract) that logically
implements a table of mappings, where each row contains:

  * a cNIGHT DUST User identifier
  * a DUST address

From the implementation point of view, each row of the table is a UTxO with
datum attached.  To implement rows of the table described above, the datum must
include:

  * cNIGHT DUST User's Cardano wallet address represented as `PubKeyHash`
  * DUST address represented as `LedgerBytes`

The above suffices to provide Midnight's observability layer with all the
required information.  However, we must also address a key security concern:
only the owner of the wallet may register and deregister it for DUST production.
To address it, we introduce a special authentication token.  Each valid
registration must contain an authentication token that proves the registration
was made from the wallet indicated as the cNIGHT DUST User.

In order to register a wallet address for DUST production, owner of the wallet
must submit a transaction that mints the authentication token and sends it to
the mapping validator.  In order to deregister a wallet address from DUST
production, the owner of the wallet must submit a transaction that spends the
UTxO from the mapping validator and burns the authentication token.  It is
crucial that the authentication tokens don't leak from the mapping validator.

The minting policy for authentication tokens is split into two cases, one for
minting and one for burning.  The minting case checks that:

   * exactly one token is minted

   * the minted token is sent to the mapping validator with a datum attached

   * the datum sets the cNIGHT DUST User's `PubKeyHash` to one that also signs
     the minting transaction.  This is a crucial security measure that ensures
     that the token was minted by the owner of the key indicated in the datum.

In order to implement the second bullet of the minting case, the minting policy
must know the address of the mapping validator.  To achieve this we parameterize
the minting policy with this address.

The burning case checks that:

   * all authentication tokens are burned

The mapping validator, which stores UTxOs with the authentication token and a
datum, allows to spend UTxOs stored on it under the following conditions:

  * UTxO being spent contains the datum with `PubKeyHash` and a DUST address

  * The spending transaction is signed by `PubKeyHash` indicated in the datum.

  * All outputs from the transaction contain only Ada.  This ensures that no
    authentication tokens are leaked.

Correctness discussion:

  * Proposed solution ensures, that only the owner of a particular wallet can
    register and deregister its address for DUST production.

  * Direct modification of existing registration is not possible.  To modify a
    registration NIGHT owner needs to deregister and then register with a new
    DUST address.  It is technically possible to add the option to modify a
    registration in a single transaction, but this would come at the expense of
    complicating the scripts.  This extra complication is probably not worth the
    effort, because ensuring script correctness would be more difficult.

  * The proposed solution **does not** prevent multiple registrations of a
    single wallet address, and so it does not meet the correctness criteria.
    To address this issue we propose that:

    - Off-chain code is implemented such that it checks for existing
      registration, and if it finds one it refuses to submit a new one.  There
      should also be a way for the user to check the registration status.

    - While the above solution should prevent double-registration in majority of
      the cases, it does not guarantee that a double (or multiple) registration
      is not made.  Thus, the observability layer must be able to handle such
      situations, preasumably by ignoring all registrations.  Another way of
      handling such a case would be to use the latest registration and ignore
      the previous ones, though this could be problematic if two transactions
      were submitted in a single block.

    See "Other explored alternatives" section below for a discussion of another
    solution to scenario 2 that does guarantee uniqueness of registrations, but
    was discarded due to large overhead and potential problems it might cause.

### Scenarios 3 and 4: self-managed or broker-managed leasing access to DUST production

To address the requirements for scenarios 3 and 4 we propose a solution, whose
key element is a leasing validator (a Plutus smart contract) that logically
implements a table, where each row contains:

  * amount of cNIGHT tokens
  * a cNIGHT Lessor identifier
  * optional cNIGHT Lessee DUST address
  * optional broker validator address
  * lease end date
  * broker lease end date

NOTES:

  * scenario 2 and scenarios 3+4 each use different validators, resulting in two
    different validators needed to implement all of the solutions proposed in
    this document.

  * Brokers are identifier by a validator address, not by a wallet address.

From the implementation point of view, each row of the table is a UTxO.  The
amount of cNIGHT is stored as tokens in the UTxO itself, while the remaining
information are stored in a datum attached to UTxO, that contains:

  * cNIGHT Lessor identifier represented as `PubKeyHash`
  * optional cNIGHT Lessee DUST address represented as `Maybe LedgerBytes`
  * optional broker validator address represented as `Maybe Address`.
  * lease end date represented as `POSIXTime`
  * broker lease end date represented as `POSIXTime`

The leasing validator, which stores UTxOs in a format defined above, ensures
that:

  * cNIGHT Lessor is free to do anything with their UTxOs after the broker lease
    end date.  Additionally, cNIGHT Lessor may change ownership of owned tokens
    even during an ongoing lease (to a Broker or cNIGHT Lessee).  When changing
    ownership, the amount of cNIGHT tokens and other datum entries must remain
    unchanged.

  * Any actions performed by the Broker are only allowed before the broker lease
    end date.  Additionally, the Broker may not do anything to a UTxO that is
    currently leased to a cNIGHT Lessee.  This assumed for all Broker actions
    described below.

  * The Broker is allowed to modify cNIGHT Lessee DUST addresses and lease end
    dates of the UTxOs that have been assigned to them.  Broker is assigned to
    an entry by specifying their validator address in the datum.  To prove
    Broker's authority to manage a given entry, the transaction must spend at
    least one UTxO from the broker validator address.  The Broker may not modify
    the owner, broker validator address, broker lease end date, nor change the
    amount of cNIGHT tokens in the UTxO.  New lease end date must be before the
    broker lease end date.

  * Broker may split one cNIGHT UTxO into multiple UTxOs.  The amount of cNIGHT
    tokens before and after the split must be identical.  cNIGHT Lessor, broker
    validator address and broker lease end date assigned to split UTxOs
    must be the same as for the input UTxO.

  * Broker may merge multiple cNIGHT UTxOs into a single UTxO.  The amount of
    cNIGHT tokens before and after the merge must be identical.  All input UTxOs
    must be assigned to the Broker and have a common cNIGHT Lessor.  Resulting
    UTxO must maintain the same cNIGHT Lessor and broker validator address.  The
    broker lease end date must not be greater than any of the UTxOs being
    merged.  This permits merging UTxOs with different broker lease end dates by
    picking the shorter date.

  * The mapping validator **does not** verify whether the Broker has paid the
    requested amount of money to a cNIGHT Lessor.

Correctness discussion:

  * Broker assignment is optional.  If no broker validator address is provided,
    the cNIGHT Lessor is the only entity that can modify an entry, thus
    implementing Scenario 3.  cNIGHT Lessor is then allowed to make arbitrary
    modifications of their UTxOs, in particular splitting, merging, assigning
    lease end dates and cNIGHT Lessee DUST addresses.  Leasing validator ensures
    that any modifications are performed after the lease end date, with the
    exception of ownership change.

  * When assigning a Broker, cNIGHT Lessor should also set a broker lease end
    date that defines how long the Broker will be allowed to manage the leasing.
    Any agreements between the Broker and cNIGHT Lessor are outside of the scope
    of this specification.

  * cNIGHT Lessee DUST address is optional, i.e. there is no guarantee that
    cNIGHT tokens located at the leasing validator produce DUST.  In particular,
    cNIGHT Lessor who participates in a broker-managed leasing will likely send
    their tokens to the leasing validator with an empty cNIGHT Lessee DUST
    address.

  * Ability to change cNIGHT token ownership during an ongoing lease opens the
    door to creating a secondary market for locked cNIGHT tokens.  This is not
    in scope of this specification, but the option is there.

  * Broker may voluntarily shorten the broker lease end date by initiating a
    merge action with as little as a single UTxO and picking any shorter date
    for the resulting UTxO.

  * Fulfilment of some of the defined correctness criteria is delegated to the
    broker validator.  In particular, ensuring that the cNIGHT Lessor receives
    payment and the cNIGHT Lessee receives access to DUST production depends on
    the broker validator.  The proposed leasing validator does not enforce any
    particular conditions here.  The only thing that the leasing validator
    strictly guards against is that the cNIGHT Lessor does not lose their tokens
    and that every time a Broker alters entrusted tokens in some way, they must
    spend a UTxO from the broker validator address.  This spent UTxO serves as a
    proof that the Broker follows the rules defined by their validator.  See
    section below for a proof-of-concept broker validator that demonstrates how
    this works in practice.

  * In addition to above, the price a cNIGHT Lessor wishes to receive for
    leasing their tokens is not stored in the leasing validator, but rather on
    the broker validator.  It is thus up to the Broker to decide how a cNIGHT
    Lessor is allowed to set and update that price.

#### Proof-of-concept broker validator

With the proposed design of the leasing validator in place, it is now possible
to create a broker DApp.  Such a DApp should have one distinguished contract,
whose address will be set as the broker validator address in the leasing
validator datum.  broker validator should define fair rules for leasing access
to DUST production, ensuring that the cNIGHT Lessor receives their payment, and
the cNIGHT Lessee receives access to DUST production they paid for.  Below is a
proof-of-concept sketch of how such a broker DApp could work.

Broker consists of a single validator.  In order to lease tokens via the Broker,
both cNIGHT Lessors and cNIGHT Lessees have to register by submitting a UTxO to
the broker validator.  Each valid registration should have a datum attached,
containing the following information:

  * cNIGHT Lessor registration contains the owner information (`PubKeyHash`), a
    declared broker end lease date corresponding to the date in the leasing
    validator, and a desired price.

  * cNIGHT Lessee registration contains the owner information (`PubKeyHash`), a
    DUST address to charge, and the desired amount of cNIGHT tokens to lease,
    all stored in the datum.  Additionally, the UTxO must contain coins to pay
    for the purchase.

Recall that in scenario 4, in order to update an entry on the leasing validator,
it is necessary to spend at least one UTxO from the broker validator.  The idea
behind the proof-of-concept broker script presented here is that it is necessary
to spend a single cNIGHT Lessor and a single cNIGHT Lessee registration in the
same transaction.  These spent registrations must be returned to the script
unchanged (i.e. no changes in the datum), and in the process the broker can
change the DUST address and lease end date on the mapping validator.  Thus the
broker validator ensures that:

  * cNIGHT Lessor registration can only by withdrawn by its owner, but only
    after the declared broker lease end date has passed.

  * cNIGHT Lessee can always withdraw their registration

  * A cNIGHT Lessor registration can be spent if:

    - The owner indicated on the broker script is the same as the owner on the
      leasing validator script.

    - Lessor receives desired payment.

    - Registration is returned unchanged to the script.

  * A cNIGHT Lessee registration can be spent if:

    - DUST address on the mapping validator is updated to the Lessee's address.

    - cNIGHT Lessee is leased a requested amount of cNIGHT.

    - Registration is returned unchanged to the script.

The above specification demonstrates how a fair and honest broker could be
defined, but it omits several elements that a production-ready application would
need.  In particular:

  * Validator outlined above makes no connection between amount of tokens
    requested by the Lessee and the price demanded by the Lessor.  In practice
    the Lessor wants to think in terms of requested price per token per unit of
    time, while the Lessee likely wants to set a limit price of some sort.

  * If would make sense if the broker end lease date set in the registration and
    in the tokens on the leasing validator where initially identical, but this
    is not verified in any way.  Note that the Broker may voluntarily shorten
    the broker lease date for tokens stored on the leasing validator, but not in
    the registration stored on the broker validator, so in principle the two
    dates need not align.

  * It is likely that a cNIGHT Lessee thinks in terms of how much DUST they want
    to have on Midnight, rather than how much NIGHT tokens they want to lease on
    Cardano.  Connection between cNIGHT and DUST is not baked in any way into
    any of the validators.  Instead, the off-chain code should convert between
    requested DUST and required cNIGHT under the hood.  It is crucial that we do
    not bake the formula for computing DUST into the Cardano validators.  This
    would both make the validators more complicated but also prevent any future
    revisions of the formula.

  * Registrations in the proof-of-concept validator are not authenticated in any
    way, so theoretically it is possible to submit a registration on someone
    else's behalf.  This seems benign for Lessee registrations, but is a crucial
    security concern for the Lessor registrations: a malicious party could
    submit forged Lessor registration with zero asking price, allowing to lease
    cNIGHT tokens for free.  One solution to this would be to use the
    authentication tokens, described in scenario 2.


Other explored alternatives (and why they were discarded)
---------------------------------------------------------

### Scenario 2: Using distributed set to guarantee registration uniqueness

Below we outline a solution that guarantees uniqueness of registrations, but has
too high an overhead to be practical.

To address the requirements of scenario 2, we propose a solution, whose key
element is a mapping validator (a Plutus smart contract) that logically
implements a table of mappings, where each row contains:

  * a cNIGHT DUST User identifier
  * a DUST address
  * a flag that informs whether a given registration is active.  Only active
    registrations produce DUST.

From the implementation point of view, each row of the table is a UTxO with
datum attached.  To implement rows of the table described above, the datum must
include:

  * cNIGHT DUST User's Cardano wallet address represented as `PubKeyHash`
  * DUST address represented as `LedgerBytes`
  * activation flag is stored as a  `Boolean`

The above suffices to provide Midnight's observability layer with all the
required information.  However, we must also address two key security concerns.
Firstly, only the owner of the wallet may register and deregister it for DUST
production.  Secondly, it should be impossible to register an address more than
once.  To address the first concern, we will introduce special authentication
tokens, and to address the second concern we will use "distributed set", a
concept borrowed from the partner-chains project.  As a result, the datum will
include additional fields.

#### Authenticating registrations

Each valid registration must contain an authentication token that proves the
registration was made from the wallet indicated as the cNIGHT DUST User.  In
order to register a wallet address for DUST production for the first time, owner
of the wallet must submit a transaction that mints the authentication token and
sends it to the mapping validator, and also set the activity flag in the datum
to `True`.  The owner of the wallet is now allowed to modify their registration
by flipping the activity flag - setting it to `False` deregister an address from
DUST production, and setting it back to `True` registers it again - and change
the DUST address.  No other modifications are permitted, i.e. the amount of
tokens on the UTxO and the owner recorded in the datum cannot be changed.

The minting policy for authentication token checks that:

   * exactly one token is minted

   * the minted token is sent to the mapping validator with a datum attached

   * the datum sets the cNIGHT DUST User's `PubKeyHash` to one that also signs
     the minting transaction.  This is a crucial security measure that ensures
     that the token was minted by the owner of the key indicated in the datum.

In order to implement the second bullet, the minting policy must know the
address of the mapping validator.  To achieve this we parameterize the minting
policy with this address.

#### Ensuring registration uniqueness

To ensure that each wallet address can be registered at most once, we will have
the mapping validator be also a "distributed set".  Full implementation details
of a distributed set are given in [this document in the
partner-chains-smart-contracts
repository](https://github.com/input-output-hk/partner-chains-smart-contracts/blob/b58fbd96/docs/DistributedSet.md).
In essence, a distributed set is a validator that conceptually implements a set
of elements (keys) by representing it as an ordered graph that guarantees
uniqueness of entries.  Each node in the graph is represented by a UTxO whose
datum stores a single element of the set (key) and an edge to the next (in
order) element.  In our case, elements we are going to store in the set are
`PubKeyHash`es of registered wallets.  The mapping validator will implement all
the logic required by the distributed set, extended with logic required to
modify a registration (changing DUST address, flipping activity flag).  Datum
definition given above needs to be extended with fields required by the
distributed set.

#### Modifying a registration

In order to change the DUST address or flip the activity flag, the mapping
validator needs to check that:

  * UTxO being spent contains a valid datum.

  * Transaction is signed by `PubKeyHash` indicated in the datum.

  * Only one UTxO from the script is spent.

  * All tokens present in the spent UTxO are returned to the script

  * Output UTxO contains a valid UTxO with the same owner and unchanged
    distributed set fields.  Only the active flag and the DUST address may
    change in the datum.

We could also consider an alternative deregistration method.  In the proposed
method, once a registration is made, the only way to deregister is to flip the
flag.  As an alternative, we could thus permit removal of elements from the
distributed set.  If we did, it is crucial that none of the authentication
tokens are leaked from the validator.  This requires, among others, extending
authentication token minting policy with a case that permits burning tokens
unconditionally.

#### Correctness discussion

  * Proposed solution ensures, that only the owner of a particular wallet can
    register and deregister its address for DUST production.  Implementing the
    mapping validator as a distributed set ensures at most one registration per
    address can be made.

#### Possible implementation pitfalls

  * Implementation of distributed set used in the partner-chains project stores
    keys as token names.  This is a potential problem, since token names are
    limited in length to 32 bytes, whereas Byron addresses are encoded as Base58
    addresses.  One solution is to hash wallet addresses and use those hashes as
    keys (set elements).  Another possible solution is to treat the owner field
    (`PubKeyHash`) as the key (set element).

  * Storing the set as a linked list means that operations on the set require a
    linear search through the list.  As a result, as the set grows larger, using
    it becomes slower.  In the partner-chains project, building a transaction
    that inserts an element into a set would take as long as 40 minutes.  While
    it might be possible to develop a dedicated indexer to speed up set
    insertion, it would only be practical if an instance of such an indexer was
    easily accessible to users.

  * We could permit removal of elements from the distributed set, but we risk
    script sizes getting too large.  This is hard to estimate further without
    having an actual implementation.

In the end, this solution seems to be too complicated and costly.  The other
solution we proposed above, while theoretically allows multiple registrations,
should work fine if the user does not deliberately try to break it - and in case
they do break it, they can only harm themselves and not others.

### Scenario 2: Mapping validator address as a dynamic dependency

In the proposed solution for scenario 2, the minting policy for the
authentication token contains a hard-coded address of the mapping validator.  It
means that, once deployed, no changes can be made to involved policies.  Also,
no circular dependencies are allowed since these cannot be achieved statically.
This is why spending from the mapping validator requires that the outputs don't
contain any tokens except for Ada, rather than requiring that the outputs don't
contain authentication tokens - the mapping validator may not know the currency
symbol of the authentication token because this would introduce a circular
dependency.

Overcoming these limitations requires a system that enables runtime script
dependencies, such as the versioning system used by the partner-chains project.
If, at the time of implementing this, there is also a versioning system it
should be used instead of static script parameters.

### Scenario 2: Registrations stored in a wallet vs. central validator

The proposed solution for scenario 2 assumes that registrations are stored in a
central validator.  An alternative approach would be to have users mint an
authentication token and store it in their wallet.  However, ensuring safety of
such a solution would be an involved task.  Firstly, the minting policy would
have to be parameterized by a `PubKeyHash` to which it is assigned.  If we used
a non-parameterized minting policy, a malicious party could mint an
authentication token and then send it to someone else's wallet with a forged
datum, effectively registering that wallet for DUST production.  In the central
validator approach this scenario is impossible.  Secondly, the observability
layer would have to be able to track these parameterized tokens, which is a
technically non-trivial task.  We'd have to presume that any wallet that
contains cNIGHT can also contain a registration and check it for authentication
tokens.  The end result is a solution that is more difficult to implement and
has a higher runtime cost, for no clear benefit.

### Scenarios 3 and 4: Per-address granularity vs. per-UTxO granularity

An initial approach to the problem of monetizing cNIGHT started with an
assumption, that all cNIGHT tokens at the Owner's wallet will be available for
leasing.  The idea was that the Owner only needs to register their wallet
address for cNIGHT leasing once, and once that happens all their cNIGHT tokens
at this wallet get monetized.  The intention was to have a solution where the
user needs to take only a single action in order to make the most of their
cNIGHT tokens, instead of having to register any newly received cNIGHT tokens.

This approach was abandoned because the user could trade away their cNIGHT
tokens at any time, making any timed commitments impossible.

### Scenarios 3 and 4: Moving cNIGHT tokens to and from the mapping validator

An earlier iteration of the proposed solution assumed that the cNIGHT Lessor
deposits their cNIGHT tokens to a Broker's validator.  Then, leases would be
made by the Broker by moving cNIGHT UTxOs to and from the mapping validator.

This approach was abandoned to minimize the risk for the cNIGHT Lessor.  In the
approach outlined above the worst that can happen for the cNIGHT Lessor is not
receiving the requested payment - there is no way to lose the cNIGHT tokens.
However, if we assumed that the cNIGHT tokens are handled directly by the
Broker's validator there would exist a risk that the cNIGHT Lessor could lose
their tokens.
