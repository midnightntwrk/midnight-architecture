# Key derivation reference

This small project is a reference implementation of key derivation for Midnight Wallet. As such - it is used to generate test vectors.

## It optimizes for readability at a cost of security!

Scalar operations are not constant time and there is no attempt at cleaning memory from unnecessary copies of the secret key or data used to generate it.
