# Reading and reproducing the Hono source inventory

[coverage.json](../../verification/coverage.json) catalogs the root package at
[`5ca49b0720755c585c9a9835f0a479ceea36fb52`](https://github.com/honojs/hono/tree/5ca49b0720755c585c9a9835f0a479ceea36fb52).
It is a structural work list for the [full verification goal](hono-verification-goal.md).
Its count of source-connected theorems is **zero**. Conditional proof slices are
recorded separately in [proofs.json](../../verification/proofs.json); they do not
automatically close inventory rows.

| Inventory at this pin | Count |
| --- | ---: |
| Original package export-map entries | 77 |
| Concrete entry points after wildcard expansion | 103 |
| Runtime or mixed entry points / type-only entry points | 99 / 4 |
| Source modules / modules with runtime output | 189 / 176 |
| Exported symbol occurrences / runtime occurrences | 610 / 360 |
| One-level exported value-member occurrences | 195 |
| Indexed source declarations / unique referenced declarations | 4,596 / 4,774 |
| Computed, instance-write, reflective and proxy sites | 218 |
| Upstream test files indexed | 160 |
| Unresolved semantic diagnostics | 8 |

An occurrence can repeat the same declaration through another package entry
point. These numbers measure the inventory, not behavior coverage or proof
progress. A declaration can have many behaviors, and one behavior can cross
several declarations.

## What is recorded

The [scanner](../../verification/inventory.mjs) uses the TypeScript 6.0.3 AST and
checker. It follows named exports, aliases and star re-exports, including
type-only chains. Wildcard export keys expand to nested subpaths; explicit
package keys take precedence. The current `dist/*.js` to `src/*.ts`/`*.tsx`
mapping is checked for missing or ambiguous sources. This mapping is not a proof
about a published npm artifact or Hono's build pipeline.

The ledger records these independently:

- **Public surface:** export symbols, class constructors, inherited and own
  instance/static methods, accessors, arrow fields, parameter declarations and
  source-owned option properties. Runtime object-valued exports have one-level
  `valueShape` member candidates with declarations and callable signatures;
  classes use their separate class rows. Returned factory shapes and exported
  value shapes are type-inferred candidates requiring runtime review.
- **Implementation inputs:** every scanned module's hash, private/internal
  declarations and transitive source dependencies. Closure includes type-only
  imports and is deliberately conservative. It is not a path-sensitive runtime
  reachability proof.
- **Dynamic behavior:** computed assignments, direct `this` writes, selected
  reflective updates, proxies and unresolved dynamic imports. A resolved name
  list comes from syntax and initializers; aliasing and mutation can change it.
  Lexical class assignments identify candidate origins, not a theorem about
  JavaScript `this` or object lifetime. An inherited field's origin list follows
  its declaration class; subclass assignments remain separate dynamic sites.
  For example, `Hono.router` still needs inheritance/lifecycle provenance review
  to join the `HonoBase` declaration to the subclass initialization.
- **Test references:** static test imports and the target modules' transitive
  dependencies. No assertions are interpreted. Seven test files have no mapped
  source dependency and remain visible in the global test list.
- **Evidence state:** `modelProof`, `sourceConnection`, `conformance` and
  `contractOutcome` are separate fields. All generated states start unresolved;
  source connection is `absent`. `declarationEvidenceDefault` applies to the
  deduplicated declaration registry.

Declaration IDs combine relative source path, UTF-16 offsets and syntax kind.
The registry supplies source ranges and SHA-256 hashes; references reuse those
IDs. Hashes bind UTF-8 source text. Module source hashes, upstream test hashes,
the scanner hash, compiler implementation hash and the 63 standard-library
input hashes identify the scan's inputs. They do not prove the scanner correct.

Some details matter when reviewing Hono. `HonoRequest` is a type-only re-export
from the root entry but a runtime class from `./request`. The `./types` entry has
runtime output because its abstract `FetchEventLike` class survives erasure.
Hono's HTTP methods and `all` are assigned dynamically; `on` and `use` are also
assigned in the constructor. `fetch` is an arrow field. The ledger retains
these origins, inherited preset members, `HonoOptions` fields and reflective
`Object.assign` work. TypeScript `private` declarations remain implementation
dependencies because that modifier alone does not remove runtime fields.
`Children.map`, `forEach`, `count`, `only` and `toArray`, plus default JSX and DOM
API objects, have explicit one-level member candidates. Nested object surfaces,
reflective additions and all possible runtime property sets remain open; an
empty inferred member list does not prove that an object has no public members.

## Open classification work

The export map and scanned source set have been structurally enumerated. Public
behavior contracts, constructor/lifecycle behavior, callback effects, dynamic
surface exhaustiveness, complete per-behavior assumptions and source connections
remain open. The inventory cannot establish a complete JavaScript API by itself.

The gap list includes 107 unresolved computed-property sites, 18 computed sites
whose initializer names were found but whose behavior remains pending, four
reflective-update sites and one proxy. Direct instance-write rows also retain a
pending review state. One ambient Deno declaration is outside the conservative
export closure; this is not a proof that it is irrelevant at runtime.

External packages and platform typings are intentionally not installed for the
scan. Seven external import occurrences and eight semantic diagnostics remain
explicit. They concern Node/platform declarations; the import list also records
`cloudflare:workers`. Type-derived shapes can therefore be partial. Host and
intrinsic members are flagged as external type assumptions instead of becoming
invented Hono options. Read the [assumptions](../../verification/assumptions.json),
[divergences](../../verification/divergences.json) and
[trust boundary](hono-trust-boundary.md) alongside this catalog.

## Reproduce the catalog

Use Node 22 and a clean sibling `hono` checkout at the pinned revision. From the
repository root:

```sh
cd verification
npm ci --ignore-scripts
npm test
node inventory.mjs --hono ../../hono
node inventory.mjs --hono ../../hono --check
```

The default source path is already the sibling checkout. `--hono` supports a
different location. A previously installed exact compiler can be used with
`HONO_TYPESCRIPT=/path/to/typescript npm test` and
`node inventory.mjs --typescript /path/to/typescript --check`.

The scanner rejects a different upstream commit, tracked changes, untracked
files, source bytes that differ from Git blobs, syntax errors, missing internal
imports and unsupported export mappings. `--check` regenerates in memory and
requires a byte-identical ledger. Output uses relative paths, stable code-unit
ordering and no timestamps. Fixtures test re-exports, nested wildcards, erasure,
classes, options, factories, dynamic methods, dependency/test links, missing
inputs, deterministic output, stale ledgers and Git-clean line-ending changes.

The initial scan and all 13 inventory tests ran with a cached exact TypeScript
6.0.3 installation. The npm lock's package metadata came from that installation;
its integrity value came from an existing pinned Bun lock. Registry DNS was
unavailable during setup, so a fresh `npm ci` was not validated locally. The
compiler is a pinned discovery dependency, not part of the Lean proof kernel.
