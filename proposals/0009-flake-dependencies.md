# Proposal 0009: Unified Flake Dependencies within Midnight

This proposal is to create a `midnight-flake-common` nix flake, specifying
external dependencies, and ensuring these are in common between Midnight
components.

# Problem Statement

Currently, each Midnight repository has their own `flake.nix`, `flake.lock`,
and specifies flake inputs independently of each other. Repositories that
depend on other Midnight repositories typically override their dependencies
inputs to match their own.

The inputs captured in `flake.lock` often diverge between repositories. This
has three main issues:
1. Flakes are used in a different environment from the one they are tested in.
2. Cached builds don't cross repository boundaries (this also bloats storage
   requirements for maintaining devshells in various projects).
3. `nix flake update` is costly and typically avoided, leading to drift between
   projects.

# Proposed Changes

This proposal is to capture common dependencies in one source location, and
ensure regular updates. 

1. Introduce a `midnight-flake-common` nix flake, consisting solely of inputs.
   * This would include common flake inputs, especially `nixpkgs`.
   * This should, at 1 month intervals, auto-commit a `nix flake update` to its
     `flake.lock`, and be otherwise low throughput.
2. Use `midnight-flake-common` as an input in all Midnight repositories, and
   `follow` inputs *from* it.
3. Change CI behaviour for PRs *only*, to run `nix flake update` before `nix
   build`.

This ensures that repositories use common versions of all common inputs. It
also encourages pinning or following specific versions of internal
dependencies, rather than relying on `flake.lock`. This clearly needs more work
in the future.

# Desired Result

Increased cache usage, decreased Midnight nix closure size, and more up-to-date
package versions being used.
