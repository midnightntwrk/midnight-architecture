# Key derivation and address format reference

This small project is a reference implementation of key derivation for Midnight 
Wallet and address formatting. As such - it is used to generate test vectors.

> [!WARNING] 
> It optimizes for readability and simplicity at a cost of security!
> Scalar operations are not constant time and there is no attempt at cleaning 
> memory from unnecessary copies of the secret key or data used to generate it.

> [!NOTE]
> Whenever "hex" format is present in the generated test vectors, it is meant 
> to be a JSON-friendly representation of the data encoded.
> It is particularly important when interpreting data for address encoding, where 
> "hex" fields always contains exactly the same data, that need to be encoded in 
> the address binary part (which most of the time does not include network id), 
> whereas hex formats used in the deployments preceding implementation of the format 
> often contain network id.