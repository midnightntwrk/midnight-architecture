# Proposal 0020: Local Proving Modalities
This is a template for writing new Midnight Architecture Proposals.  We want
this template to be lightweight, so that it does not impede the process of
capturing the proposals, and we to evolve this template over the time, as we
figure out the process of proposing changes to our architecture.

## Problem Statement

Midnight needs to offer good proving user experience for users. The 
state of proving at the time of writing this document is based on a proof 
server - a native application usually run locally in a docker container, which is 
accessed by the DApps and Wallet through an HTTP API. This approach has multiple 
issues though:
1. In production, where DApps will be served over HTTPS, Safari (and other 
   WebKit-based browsers) and Brave won't allow accessing local proof server over HTTP.
   In Brave it is a deliberate restriction implemented to protect privacy ( 
   https://brave.com/privacy-updates/27-localhost-permission/). In WebKit case it 
   seems to be overly restrictive implementation of origin separation, which is not 
   intended to be changed without other changes in related areas (https://bugs.webkit.org/show_bug.cgi?id=171934). 
2. Running the server requires command line and docker, which can not be expected to 
   be used or installed at all by non-technical users
3. It is easy to forget that the proof server needs to be run, and how it should be 
   configured for used DApp/wallet compatibility.

Therefore - there is a need for a proving solution, which does not suffer from above 
limitations:
1. Has chance of working consistently across browsers and operating systems
2. Does not centralize ownership of proving vendor to just Shielded
3. Does not require any technical expertise from user to successfully and securely 
   compute necessary proofs
4. If possible - does not require running any persistent background process

## Explored options

Two major paths were explored: usage of a native application enabled to communicate 
with DApp/Wallet and running proving code within browser. Technically speaking - there 
exists also a third option, but it was not explored, because of additional complexity 
it involves - a native application, which integrates wallet and native proving, and 
additionally runs browser component to run DApps within, somewhat similarly to the 
"contract kernel" idea, but implemented in a different layer. 
Electron seems to support this kind of usage, but depending on a framework it might 
differ (e.g. Tauri does not seem to support it as well as Electron). 

### Native application

There exist 3 major paths of communication between in-browser code and native 
applications. each with a different drawback:
1. HTTP - does not work universally across browsers (WebKit and Brave deliberately 
   restrict calling localhost HTTP from a remote HTTPS website), enabling it to 
   work across browsers requires steps that circumvent security posture (edit of /etc/hosts file, 
   installing custom root CA). Otherwise - it is the most common, seamless and supported 
   kind of interaction.
2. Native Messaging API (
   https://developer.chrome.com/docs/apps/nativeMessaging/#native-messaging-client, 
   https://developer.mozilla.org/en-US/docs/Mozilla/Add-ons/WebExtensions/Native_messaging#app_manifest) -
   only available to extensions, application needs to provide a manifest file, which 
   lists extensions, which can open it, as well as the extension needs to declare in 
   its manifest, what apps it wants to call. It allows to exchange messages, which are 
   routed to STDIN/from STDOUT of the native application. 
3. Custom URL schemes / deep linking - only one-way communication. Browser asks 
   whether to allow opening the native application (which can be reliably triggered with 
   `window.location.replace`). This mechanics is well-supported across various platforms:
   - https://v2.tauri.app/reference/javascript/deep-link/
   - https://www.electronjs.org/docs/latest/tutorial/launch-app-from-url-in-another-app
   - https://github.com/youssefaltai/linux-custom-url-scheme
   - https://unix.stackexchange.com/questions/497146/create-a-custom-url-protocol-handler
   - https://specifications.freedesktop.org/desktop-entry-spec/latest/
   - https://learn.microsoft.com/en-us/previous-versions/windows/internet-explorer/ie-developer/platform-apis/aa767914(v=vs.85)?redirectedfrom=MSDN
   - https://css-tricks.com/create-url-scheme/

### In-browser proving

Nowadays, there are no universal ways to run native code from within a website or 
browser extension. The only exception seems to be Safari, which can receive native 
extensions, being even companions to macOS desktop applications. 

The only alternative is WebAssembly. Initial proofs of concept (https://github.com/midnightntwrk/midnight-ledger-prototype/tree/akopec/wasm-proving-test,
https://github.com/midnightntwrk/midnight-ledger-prototype/tree/tkerber/wasm-proving-test)
render this approach promising in the future, but not ready for production just yet. 
One caveat is performance - proving benefits highly from parallelism. Generating 
proofs in a default, single-threaded setup is unacceptably slow - although successful,
it took minutes to generate a Zswap spend proof. On the other hand - enabling WASM to 
run in a multithreaded setup (by leveraging Web Workers, shared array buffers and 
[`wasm-bindgen-rayon` crate](https://github.com/RReverser/wasm-bindgen-rayon)) brings 
performance to noticeably slower than native, but somewhat acceptable levels (usually 
20-30s for a Zswap spend proof on a M1 Max/10 core machine). These times indicate 
possibility of reaching even 5 minutes proving time for real-world transactions on 
consumer hardware. There are multiple additional issues and considerations with 
this approach:
1. It requires using an unstable feature of Rust compiler (`target-features=+atomics`).
   This poses a stability risk - with possible future releases of the Rust toolchain, 
   behavior of this implementation might change in a way, which requires adjustments 
   of our (or our dependencies) code.
2. Usage of shared array buffers, crucial to enabling efficient memory sharing between 
   web workers, is constrained with cross-origin isolation in an aftermath of Spectre 
   vulnerability (https://web.dev/articles/coop-coep,
   https://developer.chrome.com/docs/extensions/develop/concepts/cross-origin-isolation). 
   It restricts possible interactions with third party websites (embedding, opening 
   new windows, etc.) to enable the API. These restrictions might significantly affect 
   some DApp integrations or complicate their UX/deployments/architecture.
3. There is no official support for node.js. It seems to be directly related 
   to the fact that `wasm-bindgen` and `wasm-pack` do not have an ESM node.js target. 
   I managed to generate a proof on node.js by replacing one file in the output with 
   a node.js counterpart. This implies additional work with packaging, or contributing 
   upstream (https://github.com/RReverser/wasm-bindgen-rayon/issues/24). Even then - 
   there are some gaps around `wasm-bindgen` and `wasm-pack` to provide proper ESM output 
   that could be used universally across varying targets. The fact that Deno has 
   officially separate target only complicates the situation when 
   taking Deno and Bun compatibility more seriously.
4. The WebAssembly code blocks its running thread, which requires additional web 
   worker to circumvent the issue, not a big deal on its own, but still additional 
   thing to keep take care of.
5. There is little traffic observed in the `wasm-bindgen-rayon` repository. While it 
   seems to indicate that the underlying core mechanics are done and quite stable, the 
   package also is involved in emitting target JS, for which runtime 
   capabilities improve dynamically in recent years.

## Proposed direction

Following are the recommendations:
1. As a short term solution (Brave-incompatible though) implement deep-linking technique, 
   which allows wallet to ad-hoc run a local proof server instance on a provided, random 
   port, while using existing HTTP API. This requires mostly a reusable packaging 
   effort on top of the existing proof server implementation, to manage its processes.
2. As a long-term solution, leverage Native Messaging API to enable wallet extensions 
   communicating with a locally installed, native proving application. It 
   involves:
   - definition of an interaction protocol, so that different wallet vendors and 
     different application vendors can provide and integrate their solutions.
   - definition of a proving TypeScript API suitable for utilization of locally installed 
     proving application, extend DApp Connector API appropriately, so that wallets can expose 
     such capability to DApps.
   - (Optionally) Rust-based-server and TypeScript-based-client libraries, as 
     means for implementing protocol test suite as well as ready to use and integrate 
     components in existing stack.
   Do not implement any additional discovery mechanism between wallet extensions and 
   proving applications. Wallet extensions identify applications to call by name, but 
   proving application needs to list extension ids allowed to call it. This calls for 
   a community-maintained list of wallet browser extensions. While it still 
   raises a security concern in case a malicious proving application gets installed, 
   it will help detecting usage of fake wallet extensions.
3. Implement an experimental WASM-based prover 
   implementation, which could be used with Midnight.js to prove contract calls. 
   Initially as a means of signalling to the community that this is a thing that is 
   being looked at, but also to streamline the process of integration of WASM proving 
   once necessary functionality of Rust toolchain stabilizes.
4. Given common issues with OpenGL in Tauri (which seem to be related directly to the 
   fact of using system-provided WebKit - https://github.com/tauri-apps/tauri/issues/5143),
   usage of Tauri as the proving application implementation framework might require 
   additional hardening work, like static linking of critical dependencies or other 
   packaging workarounds. Additionally, while compatibility on macOS and Windows should 
   not be a big issue (in both cases engines from Safari and Edge are used, and they are 
   kept relatively up-to-date by Apple and Microsoft), it might arise as an issue in Linux 
   environments, due to the variety of distributions, approaches to packages, etc. 
   Given all the above - Tauri should be the chosen framework only if the above 
   drawbacks and risks are outweighed by the fact of using Rust-first framework. 
   Otherwise - Electron is known to be stable, quite well-known solution (TypeScript-first though).

## Desired Result

To successfully transact on Midnight, DApp and wallet users do not need to utilize tools 
requiring technical expertise (like command line, Docker, or knowledge about networking 
ports), they also do not need to remember about running the proving application. 
