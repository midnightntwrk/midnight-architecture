# Properties of Midnight Transactions

- Balance preservation: A transaction does not create or destroy funds, except to the extent permitted in contract mints.
- Binding: A made of multiple parts by a single user cannot have only a part of it used by another user.
- Infragility: A user cannot cause a transaction that would succeed to fail in its fallible section by merging it with something else.
- Causality: A user cannot use the output of a failed contract call to convince a succeeded contract call that this output is correct.
- Self-determination:
  a. A user cannot spend the funds of another user.
  b. A contract can only be modified according to the rules of the contract.
