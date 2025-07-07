# Standardize Package Managers and Tooling for Midnight dApp Examples

## Status

Proposed

---
| -         | -                                                   |
|-----------|-----------------------------------------------------|
| date      | 2025-07-03                                          |
| deciders  | Midnight Framework Team, DevRel Team.               |
| consulted | Engineers                                           |
| informed  | ......                                              |
---

## Context and Problem Statement

The Midnight blockchain framework currently lacks standardized tooling and package management practices across dApp examples, leading to inconsistent developer experiences, fragmented documentation, and increased maintenance overhead. Developers encounter different package managers (npm, yarn, pnpm), varying ESLint configurations, and inconsistent build processes across example projects, creating confusion and reducing adoption efficiency.

How can we establish consistent tooling standards for TypeScript/JavaScript dApp examples that ensure reproducible builds, maintainable codebases, and a seamless developer onboarding experience?

## Decision Drivers

* **Developer Experience Consistency** - Developers should have predictable tooling across all Midnight dApp examples
* **Maintenance Efficiency** - Standardized tooling reduces maintenance burden and simplifies CI/CD processes
* **Build Reproducibility** - Consistent package management ensures reliable builds across different environments
* **Community Adoption** - Clear, consistent examples lower barriers to entry for new developers
* **Security and Compliance** - Standardized linting and formatting rules help maintain code quality and security practices
* **Documentation Clarity** - Uniform tooling simplifies documentation and tutorial creation
* **Ecosystem Alignment** - Align with modern JavaScript/TypeScript ecosystem best practices

## Considered Options

* **Option 1: npm + Standard ESLint Config** - Use npm as package manager with a shared ESLint configuration
* **Option 2: pnpm + Comprehensive Tooling Suite** - Use pnpm with ESLint, Prettier, TypeScript strict mode, and Husky
* **Option 3: Yarn Approach** - Use Yarn
* **Option 4: Bun + All-in-One Approach** - Use Bun as package manager and runtime with integrated tooling
* **Option 5: Mixed Approach** - Allow different package managers but standardize other tooling

## Decision Outcome

Chosen option: "**Option 2: pnpm + Comprehensive Tooling Suite**", because it provides the best balance of performance, modern tooling practices, and developer experience. pnpm offers superior disk space efficiency and faster installs, while the comprehensive tooling suite ensures consistent code quality and developer experience across all examples.

**Note**: While Bun (used in Glacier drop) offers compelling performance benefits, the ecosystem maturity and tooling compatibility of pnpm make it the safer choice for framework-wide standardization. Projects with specific performance requirements like Glacier drop may continue using Bun as an exception to this standard.

### Positive Consequences

* **Faster Development Setup** - pnpm's efficient dependency resolution and caching significantly reduces installation time
* **Consistent Code Quality** - Standardized ESLint, Prettier, and TypeScript configurations ensure uniform code style
* **Reduced Disk Usage** - pnpm's content-addressable storage reduces disk space requirements for developers working with multiple examples
* **Better Security** - pnpm's strict dependency resolution helps prevent dependency confusion attacks
* **Improved Maintainability** - Consistent tooling simplifies maintenance and updates across all examples
* **Enhanced Developer Onboarding** - Clear, consistent tooling reduces cognitive load for new developers

### Negative Consequences

* **Migration Overhead** - Existing examples using npm/yarn will need to be migrated
* **Learning Curve** - Some developers may need to learn pnpm-specific commands and workflows
* **Potential Ecosystem Compatibility** - Some tools may have limited pnpm support compared to npm/yarn

## Validation

Implementation compliance will be validated through:
* **Automated CI Checks** - All example repositories must pass standardized linting and formatting checks
* **Package Manager Verification** - CI pipelines will verify presence of `pnpm-lock.yaml` and absence of `package-lock.json`/`yarn.lock`
* **Documentation Compliance** - Ensure all setup instructions reference the standardized tooling

## Pros and Cons of the Options

### npm + Standard ESLint Config

Standard, widely-adopted package manager with basic linting standardization.

Positives:
* npm is universally known and supported
* minimal learning curve for developers
* extensive ecosystem compatibility
* Checkmarx support

Negatives:
* slower installation times than next gen package managers and larger disk usage
* less efficient dependency resolution
* limited modern tooling integration

### pnpm + Comprehensive Tooling Suite

Modern package manager with comprehensive development tooling suite.

Postitives:
* significantly faster installation and better disk space efficiency
* strict dependency resolution improves security
* comprehensive tooling ensures consistent code quality
* aligns with modern JavaScript ecosystem trends

Negatives:
* requires developers to learn pnpm-specific commands
* some tools may have limited pnpm support
* migration effort required for existing examples

### Bun + All-in-One Approach

Modern all-in-one runtime and package manager with integrated tooling capabilities.

Positives:
* extremely fast installation and execution performance
* single tool for package management, bundling, and testing
* excellent TypeScript support out of the box
* proven performance in projects like Glacier drop
* reduced tooling complexity with integrated features
* excellent Node.js compatibility

Negatives:
* newer tool with smaller community and ecosystem
* some tools may have limited Bun compatibility
* No checkmarx support :-(

### Yarn Approach

Yarn package manager.

Positives:
* Checkmarx support
* In the default PnP mode stricter dependency resolution than NPM.
* In the default PnP mode significantly faster installation and better disk space efficiency (likely simpler/faster than pnpm as no symlinks need creating)
* Can be used in backward compatible node_modules mode for projects where PnP would be an issue.

Negatives:
* larger disk usage compared to pnpm (if using legacy node_modules mode)
* slower than pnpm (if using legacy node_modules mode)
* Yarn 1 vs Yarn 2+ fragmentation in ecosystem
* Npm has closed the gap on yarn performance. EDIT: no it hasn't: Yarn PnP is faster than pnpm: https://pnpm.io/benchmarks

### Mixed Approach

Allow flexibility in package managers so that every project can pick a different package manager.

Positives:
* allows developer choice and flexibility
* no migration required!

Negatives:
* allows too much developer choice and flexibility!
* inconsistent developer experience (additional cognative load)
* increased maintenance complexity
* documentation complexity
* CI/CD pipeline complexity

## More Information

**Implementation Timeline:**
* Phase 1: Create standardized tooling configuration templates
* Phase 2: Migrate existing examples to new standards
* Phase 3: Update documentation and CI/CD pipelines

We would expect other JS/TS projects in midnight to use the standard tools (where this makes practical sense)

**Standard Tooling Configuration:**
* **Package Manager**: pnpm v8+ (with exceptions for specific projects like Glacier drop using Bun)
* **ESLint**: @typescript-eslint/parser with Midnight-specific rules
* **Prettier**: Standardized formatting configuration
* **TypeScript**: Strict mode enabled with consistent tsconfig.json
* **Husky**: Pre-commit hooks for linting and formatting

These could be preconfigured in the repo template.
