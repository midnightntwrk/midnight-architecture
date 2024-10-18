# Glossary

There are certain terms and names that are used within this repository, code, APIs, other documentations and 
meetings that are important for everyone to think the same about.

Wallet
: Application that securely stores user secret key and allows to authenticate blockchain transactions using that key

Coin
: Term used to describe a singular piece representing certain amount of tokens of certain type that can be used as an input or output in a transaction. In unshielded UTxO–based chains usually the term "output" is being used in a very similar context, ZCash and related work tends to use term "note" to name the same concept 

Qualified Coin
: A coin, which is registered in ledger's commitment merkle tree and its index in the tree is known and thus — can be spent in a transaction. 

DApp
: An application that interacts with blockchain, typically delivers its functionality by a website application, smart 
contract(s) and a protocol allowing user to call the smart contract 

Domain Separation
: Approach in cryptography to provide additional input (called _domain separator_) when hashing data so that produced 
hashes of otherwise identical data can differ.
More: 
  - https://crypto.stackexchange.com/questions/66969/what-is-meant-by-domain-separation-in-the-context-of-kdf
  - https://kerkour.com/end-to-end-encryption-domain-separation-cryptography
  - https://eips.ethereum.org/EIPS/eip-712

Transaction balancing
: A process, where wallet receives a transaction, which is not balanced (that is - for a token type transaction has more 
value in outputs than in inputs, or the other way around) and provides necessary inputs and outputs to balance 
the transaction so that it can be accepted by the ledger

Native tokens
: user-defined token types managed by ledger alongside DUST using the same mechanics as for DUST (thus the word native - as in native for the ledger)

Custom spend logic
: Term used to indicate a potential feature of Midnight, where spending a coin involves executing attached logic so that certain invariants of token lifecycle can be enforced. An example use–case can be requiring known/allowed source of tokens.   

Hard-fork
: An update to protocol, which makes previously invalid events, valid. Such kind of update requires all clients connected to network (and most importantly - significant majority of block producers) to upgrade. Otherwise not upgraded clients would reject events performed after update, causing a fork in the network.
See: https://en.bitcoin.it/wiki/Hardfork
While in Bitcoin no intended hard-forks were executed, they are a common approach to bring new features in other networks, like Ethereum or Cardano. 

Soft-fork
: An update to protocol, which makes previously valid events, invalid. Such kind of update requires (significant majority of) block producers to upgrade, but other clients not necessarily.
See: https://en.bitcoin.it/wiki/Softfork

Commitment scheme 
: Cryptographic primitive, which allows to commit to a (potentially secret) value without necessarily revealing it. The data shared to commit to the value are called _commitment_. Commitment scheme has to guarantee 2 properties:
1. hiding property - it is not possible to recover value from the commitment
2. biding property - commitment verification can only pass with the same value that was committed to
More: https://en.wikipedia.org/wiki/Commitment_scheme
