# Proposal 0002: Error Handling in TS for good quality and good developer experience

Status: proposed, temporarily this proposal is freezed and development is moving forward with Option #3
Jira ticker: https://input-output.atlassian.net/browse/PM-3878

# Problem Statement
We want a common, consistent approach to raise and handle error across different components, so that overall experience exposed to DApp developers and other Midnight developers does not cause surprises. It is important to provide a way to exhaustively handle all of the expected errors coming from a given API so that one can be sure about not leaving things to pure luck (and, for example, learning about specific error only after dapp is deployed) or the happy path.


# Proposed Changes

## Possible solution 1 - unions all the way
Almost exclusively use discriminated unions to signal errors as part of the return 
type. This approach is in line with the functional programming and immutability (which 
I assume are the defaults in our code). It results with the code, where all the cases 
to handle are known and defined upfront (that is before running the code, or at least 
at the point of rudimentary check of certain paths) so that ignoring errors or passing 
them further becomes an explicit thing to express in code and a must-have.

For example:
```ts
type Res = {status: “ok”, value: string}
  | {status: “error”, message: string};

function doSth(param: number): Res { 
    //...
}

const a = doSth(42)
switch (a.status) {
    case “ok”:
        console.log(a.value);
        return;
    case “error”:
        console.error(a.message);
        return;
}
```


It renders a need for additional helpers to handle the value and provide a reasonable 
experience for pure JS client code, or even a better experience for TS code. For 
example (almost pseudocode, but I believe it's perfectly doable in TS):
```ts
import * as t from 'io-ts';

type KeysFromShape<T extends t.Interface> = keyof t.TypeOf<T>

//need to add the discriminator as well to the items
type UnionFromShape<T extends t.Interface> = t.TypeOf<T>[KeysFromShape<T>] 

type ValueAtKey<TShape extends t.Interface, TKey extends keyof TShape> = t.TypeOf<TShape>[TKey]

type Folder<A, TShape extends t.Interface> = {
    [K in KeysFromShape<TShape>]: (arg: ValueAtKey<TShape, K>) => A
}

interface Result<TDiscriminatorName extends String, TShape extends t.Interface> {
    [`mk${[K in KeysFromShape<TShape>]}`]: (arg: t.TypeOf<TShape>[K]) => {
        [TDiscriminatorName]: K} & ValueAtKey<TShape, K>
    fold<A>(arg: UnionFromShape<TShape>, folder: Folder<A, TShape>): A 
} 

function resultType<TDiscriminator extends string, TShape extends t.Interface>(
    shape: TShape, 
    discriminatorName: TDiscriminator): Result<TDiscriminator, TShape> {
    
}

```

Essentially sky is the limit when it comes to how defensive such kind of result types 
are, up to the point, where all actual values are held in private fields/behind 
unexported symbols, so that only functions defined within `resultType` can access the 
value, and thus - fully encapsulate and enforce proper handling of various cases, both 
in TypeScript and pure JS client code (including, for example, verification if folder 
passed to `fold` has all the cases defined). 


This approach has its problems though:
- it's not a common and widely used one in JS community
- to work very well for JS code it has to come with well-defined `resultType` helper
- it can only work really well in code, which, at least, does not rely on mutations, but on immutability (so that the result value is by default inspected) 
- it does not use common error channels, because those are almost by definition untyped in JS, which introduces new set of familiarity issues
- it has ergonomics issues related to function composition, which leads to further readability issues or, again, points to a need for a good `resultType` helper, which addresses that

## Possible solution 2 - exceptions and existing error channels all the way

In short - report all kinds of errors by throwing, `Promise.reject`, etc. 

This approach has a great value in familiarity and overall following existing patterns,
which is good. By subclassing `Error` class one can easily add more data to reported 
errors, so there's no limitation there. Good thing is that stack traces are usually 
useful in this style and that JS is able to collect stack traces even across async 
boundaries.   

I believe this proposal has couple of serious issues, which I'm not sure if are even possible to be reasonably addressed other than by "read documentation" or "we have this convention"
  - it's super easy to mix errors from different sources just by not handling all of 
    them at some place
  - it's super easy to ignore errors altogether
  - there is no point while writing code, where types can say "this error is not 
    handled yet", so, if documentation is not read fully - app can crash because of 
    developer not being reminded about need to handle certain errors

To some extent, following ideas from React hooks and algebraic effects, it should be 
possible to mitigate those issues by approaches like listed below:
  - lazy wrapper for promises/functions, which forces error to be handled before execution
  - "execution contexts", where a couple of helpers is defined:
    - one to list all of error types of certain function/API
    - one to help to handle all error types (within `catch` block, error callback in 
      Promise, etc.) based on the list of all errors
    - one to define "execution context" for certain function/API and at least helps to 
      verify that errors from the list do not leave such zone at all (they might be 
      converted into error more suitable to a layer above) or have proper marker, which 
      shows that they are explicitly allowed to be handled somewhere else
    - one to check whether certain function/API is run within such "execution context"

While there may be serious limitations to such measures, it also may be a good enough effort in terms of making sure reported errors are 
not a surprise when app is already long deployed and also that errors from lower 
layers do not leak to upper layers unnoticed.

In code it may look like this
```ts
//helper.ts
function errorsHelper<T extends Error[]>(...errors: T) {
    type ErrorHandler<T> = Record<Element<T>, (err: Element<T>) => T | void>
    
    let isAsyncContextSet: boolean;
    return {
        handleErrors<T>(handler: ErrorHandler<T>): (err: unknown) => T | void {
            //check if all defined
            //return the handler, etc.
        },
        async runAsync(thunk: () => Promise<T>, handler: ErrorHandler<T>): Promise<T> {
            isAsyncContextSet = true;
            try {
                return await thunk();
            } catch (e) {
                return this.handleErrors(handler);
            } finally {
                isAsyncContextSet = false;
            }
        },
        wrapAsyncFn<T extends Function>(fn: T): T {
            return (...arguments: Arguments<T>): ReturnType<T> => {
                if(!isAsyncContextSet) {
                    throw new Error(`Function ${fn.name} not called within its error 
                    handling context`);
                }
                return fn(...arguments);
            }
        }
    }
}

//fileIO.ts
abstract class FileIOError extends Error {}
class ReadError extends FileIOError {}
class PermissionError extends FileIOError {}

const fileErrors = errorsHelper(ReadError, PermissionError);

const doSth = fileErrors.wrapAsyncFn(async (value: number): Promise<string> => {
    return Promise.reject(new ReadError("boo"))
});

//app-storage.ts

class StorageError extends Error {}
function saveSth() {
    return fileErrors.runAsync(() => doSth(42), {
        [ReadError]: (err) => { throw new StorageError() },
        [PermissionError]: (err) => { throw new StorageError() }
    });
}


```

## Possible solution 3 - mix both and refer to "common sense"

In short: 
  - treat all errors as either part of the result type or an exception
  - don't let errors to change their way of handling/reporting (so an exception stays 
    as an exception, part of result type does not become an exception suddenly)
  - as a rule of thumb - errors that are reported to API caller (so they leave 
    component boundary) are exceptions, other errors can be (but don't have to) 
    reported as a part of result type

This approach is good, because it allows to rely on result type without reaching out 
for defensive helpers. It also conveys some of strong points of option #2 - reliance 
on existing (though far from perfect) mechanisms in existing APIs and ecosystem.

What is not good here, IMO, is:
  - it has all the issues of #2 on API boundary
  - it doesn't really answer when to reach for one or the other style, guideline of 
    not changing error "style" across its lifetime, while it makes perfect sense, 
    further complicates things, so it effectively pushes things towards more 
    imperative style and option #2 for consistency




# Desired Result
Easy to follow Midnight-wide guildeline for reporting and handling errors that is 
reliable enough for us (Midnight developers), that allows DApp developers to reliably build their 
applications.
