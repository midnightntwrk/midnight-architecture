# Key derivation and address format reference

This small project is a reference implementation of key derivation for Midnight Wallet and address formatting. As such - it is used to generate test vectors.

> [!WARNING] 
> It optimizes for readability and simplicity at a cost of security!
> Scalar operations are not constant time and there is no attempt at cleaning memory from unnecessary copies of the secret key or data used to generate it.
