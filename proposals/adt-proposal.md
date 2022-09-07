
# Proposal: Public Oracle ADT

If all assumptions are valid, the author's preference is option one.

## Option 1: Initialization Circuit

  In this approach each contract must define a circuit `initialize` that is dedicated to constructing the state of the public oracle. Abusing syntax, you might imagine an initialization function

  ```typescript
  circuit initialize (arg: Field): Set<Field> {
    return Set(arg)
  }
  ```

  where `Set` is a built-in `Set` ADT constructor.

  In the following example public state is represented as a nested ADT.

  ```typescript
  circuit initialize (arg: Field): Set<Counter> {
    return Set(Counter(arg))
  }
  ```

  where, again, `Counter` is a built-in ADT constructor.

  Note that `initialize` cannot be called explicitly anywhere in the contract in which it's defined. The arguments to `initialize` are specified by the user when the deploy transaction is constructed. Furthermore, because `initialize` is a circuit, the deployer of the contract does not need to explicitly reveal the arguments to `initialize`, in which case the explicit value of the public state is not known. This may be a bug of a feature.

  This approach has a number of benefits:

  1. It keeps open the possibility of using private oracle data in the initialization function, since circuits may contain private oracle queries. If a private oracle is accessed, the deploy transaction will need to contain a proof.
  
  2. Since the return type of the `initialize` circuit must be specified, `Abcirdc` could type-check queries to ensure that the operation the query is performing is valid with respect to the structure of the public oracle state. Ultimately, Abcirdc would compile the Abcird state representation into a Typescript representation. The Typescript representation would then need to be converted into a Rust representation for storage in the ledger.

  3. Relatively small number of additional features added to `Abcirdc`; mainly support for built-in ADT constructors.

  One potential drawback of this approach is that, since any ADT (nested or otherwise) constructable from the built-in constructor functions is returnable from a circuit, any ADT must also representable as an Abcird data type. The next section evaluates whether this is reasonable.

  ### Representing ADTs in Abcird

  Should all ADTs be representable as Abcird types? In other words, for any ADT `T`, can there exist a circuit?

  ```typescript
  circuit f (...) {
    ...
    const adt = ... // where type(adt) = T
    ...
  }
  ```

  If so, then having an `initialize` circuit for public state initialization is feasible. If not, then we must consider something else. However, note that if ADTs cannot be assigned to Abcird variables, then the public oracle language could not support getter queries for arbitrarily nested ADTs. For example, suppose you have a contract

  ```typescript
  circuit initialize (arg: Field): Map<Set<Field>> {
    return Map('a', Set(arg))
  }

  circuit f (...) {
    ...
    const set = public$get('a')
    ...
  }
  ```

  In the transition function `f`, `public$get` is a public oracle query (built-in ADT operation) that always operates over the current public oracle state, which is initialized with the value returned from `initialize`. In the initialization circuit approach, each public oracle query is automatically applied to the current public state, as in `public$get`.

  If ADTs are not representable as Abcird data types, then queries like `public$get('a')`, which return ADTs are unsupportable. The only lookup queries supportable are those on ADTs that contain the basic Abcird data types. However, if ADTs *are* representable as Abcird data types, then the initialization circuit approach is still feasible.

  ### Representing Queries in Transactions

  Public queries could be represented similarly to their current representation; that is, a record

  ```typescript
  type TranscriptEntry = {
    query: string
    args: AbcirdValue[]
    result: AbcirdValue
  }
  ```

  where `AbcirdType` is a type representing Abcird values. In the initialization circuit approach where ADTs are representable as Abcird values, `AbcirdValue` would also include values representing ADTs used in the public oracle state.

  Many ADT lookup queries will have a similar shape to `public$get('a')`. How these queries will be named is an open question. For example, one could alternatively refer to the built-in as `public$mapGet('a')` and the other ADT types similarly (e.g. `public$recordGet('a')`). In the event that we want to overload the query identifiers, the transcript entry would need to include a field to delineate the type of query being performed. For `public$get('a')`, the transcript entry would look something like

  ```typescript
  {
    adtType: 'map',
    query: 'public$get',
    args: ['a'],
    result: Set { ... }
  }
  ```

  to disambiguate the query for the transcript validator.

  ### When does state initialization occur?

  Given contract and oracle executables, state construction occurs during the execution of the MidnightTS `deploy` function by executing the `initialize` transition function execution. The `deploy` function installs the state in the ledger.

## Option 2: Initialization Query

  In this approach, `Abcird` is extended to allow the user to define a dedicated `initialize` statement that will construct public state. The `initialize` function body will be expressed in a limited sublanguage that only allows access to dedicated ADT constructor functions.

  ```typescript
  statement initialize(arg: Field): Set<Counter> {
      return Set(Counter(arg))
  }
  ```

  The result of `initialize` is always the initial state of the public oracle. It cannot be called explicitly anywhere in the contract in which it's defined. The arguments to `initialize` are provided by the user when the deploy transaction is constructed. A deploy transaction would include a public oracle transcript consisting of a single call to the `initialize`. The transcript would be validated as it would for a call transaction. 

  A downside of this approach is that the Abcird compiler would need to be extended to support defining and implementing an initialization function using ADT constructor built-ins. Allowing the definition of a *statement* would be an exceptional case since Abcird currently only allows defining circuits.

  A potential downside of this approach is that it precludes users from using private oracles to compute the initial state, which may be desireable or undesireable.

  An upside of this approach compared to (3) is that Abcird can type-check the public oracle queries used in a contract against the type of data returned from the `initialize` query. Hence, users would likely never need to look at the Typescript output for the public oracle or transition functions, just provide the private oracle implementation.

  ### When does state initialization occur?

  Given contract and oracle executables, state construction occurs during the execution of the MidnightTS `deploy` function by executing the `initialize` public oracle query. The `deploy` function installs the state in the ledger.

## Option 3: Typescript-based User Initialization

  A less structured (and possibly the fastest) approach would be to have developers construct representations of the initial state manually using a Typescript DSL. Effectively, users would be manually constructing the Typescript representation of the Abcird state representation from options (i) and (ii). Processing the deploy transaction would involve parsing and validating the structure of the state provided. 
  
  A downside is that manual construction could be error prone. In particular, there would be no concrete public state type specified to type-check public queries against.
  
  ### When does state initialization occur?

  Given contract and oracle executables, state construction occurs before the execution of the Midnight TS `deploy` function. The public state is constructed via Typescript DSL. The `deploy` function takes the initial state as a parameter and installs the state in the ledger.