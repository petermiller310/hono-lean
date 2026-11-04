# Lexical arrow invocation: audit boundary

This is an audit record for the completed conditional source-model milestone,
with full-Hono and native-runtime adequacy still open. The focused witnesses,
integrated build, original fresh replay and declaration/axiom audit pass.

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52` (4.13.13).
The source checker verifies all 315 pinned blobs and the actual contiguous796B
setup at `src/utils/url.ts`50–79, `[1127,1923)`, SHA256
`ad1203945736ef5e2219a39c3cd9b5173760c3c5e981e757ab7d1b1a8f74d30b`.
It reassembles the unchanged52B initializer and744B arrow declaration. Lean
parses the combined source into those actual programs and executes the parsed
initializer/declaration; there is no source-string-to-desired-AST oracle.

## Checked pieces so far

The final lexical runtime/expression gate passes65jobs (`75308`, terminal 0).
It includes nine kernel witnesses, closed-host environment preservation and
the concrete expression refinement theorem. Abstract host-frame parameters in
the internal generic library are discharged by proved closed-operation laws.
The exported expression theorem has no future-preservation-law premise.

The call/program gate passes93jobs and the subsequent composition gate passes
95 jobs (`95740`, terminal 0). The final gate 14012 passes96jobs with23public
witnesses and13actual axiom guards; its Examples check takes376s. These connect actual fresh parameter cells and live
free-variable reads to wildcard/miss/plain/warm/safe terminal-range contracts,
then connect actual setup to the exported value and two terminal→warm calls on
the same carried runtime. Parameterized initial domains, actual constructor
updates and both collision orders are inhabited kernel witnesses. All15new
Lean modules are frozen before the integrated/fresh gates.

Integrated 44340 passes753jobs with warnings as errors. Declaration audit 25754
resolves258advertised names (180theorems/78definitions) with duplicate absence,
actual environment kinds and correct retained source constants. Every one of
the180theorems passes the transitive standard-only axiom check; some use only a
subset of `propext`, `Classical.choice`, `Quot.sound`.

Original fresh 51174 completes with terminalexit 0 against the same15frozen
modules. It runs for an extended period at full CPU, with observed RSS around
15–26GB on this48GB host; the original process is retained through completion.
The four closed VM histories contribute to a27MB Examples.olean. This records
local reproducibility and its resource cost; no hosted CI execution is claimed.

The first audit hit the generated meta program's recursion limit. Its limit is
now 8192. The second caught45misqualified names in the root name extractor,
which had mistaken anonymous `mutual`/`section` ends for namespace ends. All 45
names were corrected and the full258/180audit passed; no name was omitted and
no Lean proof, statement or domain changed.

Public call inputs are initial registry/program, argument, lexical-cell,
realm, language, descriptor and constructor facts. No completed body, successful
invocation, future cache Get/Set, desired tuple or future realm is supplied.
Success premises in internal simulation/frame lemmas are discharged from the
existing independent body contracts before the final call theorems apply.

## Semantic scope

Cells distinguish an uninitialized binding from initialized `undefined`.
Nearest binding lookup stops at a TDZ shadow. Closures retain environment
references and lexical `this`; each call allocates new positional parameters.
The exported constant contains an ordinary function-object value coherently
linked to the arrow payload. Legacy intrinsic function handles remain separate.
Creation metadata includes name, length 2 and no own prototype; callable kind
determines nonconstructibility even if a prototype property is later added.

The actual AST evaluator reads cells at each variable occurrence. Its admitted
ordinary expression profile is variable/primitive/index evaluation; host label
and constructor operations are the existing closed intrinsic implementations.
Those operations do not receive the lexical-cell heap. This is a derived
stability fact for the closed profile, not an assumption that arbitrary user
callbacks preserve globals. Current constructor identity is saved before its
argument is evaluated.

Independent return contracts combine the prior heap/cache/tuple/compiled-range
properties with caller, old-cell, environment and closure preservation. Caller
restoration changes control fields while retaining actual body heap effects.
Source setup derives fresh cache separation; repeated calls carry the full
returned runtime rather than resetting cache, globals or metadata. Warm calls
reuse the cached value but still perform label matching and temporary
allocations before the cache lookup.

## Executable evidence and remaining gates

Final suite 29485 passes11groups in12.376s:348finite contexts/histories,
five source mutations, two unready model worlds, eight actual-full-module native
controls and one explicit reached-lookahead refusal. The signature-swap mutation
checks that bindings follow parsed parameter names. An independent oracle
derives expected arguments, metadata, cache descriptors and exposed identities.
Some finite cases exercise rejected/missing arguments or unwritable descriptors;
these are not silently included in a universal normal-call contract.

The selected native fixture loads the exact796B TypeScript setup once per
history, appending an explicitly unverified private-cache observer. Both pinned
Bun1.4.0 and Node22.22.2 execute it. Controls also execute the entire unmodified
pinned `url.ts` module. Type erasure, loader, module instantiation, observer and
native adequacy remain unverified. Hidden native allocation counts are not
observed; visible returned/cache graph identities are canonical observer IDs.

Earlier recheck 94953 started while Lake was rebuilding Source and failed to
load Source.olean in nine model groups. It did not exercise behavior. Final 29485
runs after the final focused gate and stable artifacts. No failure has been
erased or converted into a new compatibility allowance.

Frozen body 51824 passes10groups9.019s; terminal-cache63987 passes6groups19.710s.
Pinned comparison 24590 retains467agreements, one exactD1,98 appends and zero
unexpected failures. Inventory 70700 passes13fixtures1.799s and checks the
unchanged103entry points/189modules/4774unique declarations. The first local
inventory attempt lacked normal TypeScript resolution; replay explicitly
selected the existing exact6.0.3package, with no fresh install or source change.

The byte-exact setup copy retains upstream's final blank line 79. Staged checks
pass with default whitespace rules for every other file and
`core.whitespace=blank-at-eol,space-before-tab,-blank-at-eof` for this exact copy.
The independent reviewer replays both successfully. Source bytes and
repository/global whitespace settings stay unchanged; the source checker
separately enforces the copy's complete raw bytes.

Final independent reconciliation is clean across the source/contracts/proofs,
registry, finite checks, preservation invariants and final conditional-green/
open-amber diagram (25 active elements/eight bound arrows). All1005local Markdown
links resolve. All37prior clusters/36additional slices/30obligation statuses and
theorem arrays/36routing statuses/354old Lean modules, fixed SPEC/target/catalog/
D1/engine controls/benchmarks and all prior cache/body/terminal artifacts remain
unchanged. The full-Hono goal stays active and has no unconditional runtime claim.

## Open obligations

Generic handle-call lemmas describe the model registry, including arbitrary
model states. Source-created calls additionally establish fresh function-object
allocation and binding/value/payload coherence. Neither supplies a complete
native heap embedding or general runtime well-formedness theorem.

The selected fragment uses sequential persistent lexical frames. Full module
and block declaration instantiation, forward TDZ reads, general globals and
accessors/proxies, arbitrary callback mutation, caller argument-expression
evaluation, native function/module behavior and TypeScript frontend adequacy
remain open. The prototype parameter identifies an existing projected object;
the full native Function.prototype embedding remains an adequacy obligation.

Legacy body errors lose partial state. `outsideModel` therefore establishes no
native throw completion, rollback or failure-state frame. General regex/flags/
captures/coercions and reached67lookahead remain open. Lookahead native success
versus model refusal is recorded explicitly; constructor input uses a raw
slash while the native `.source` display escapes it. This introduces no D1 or
engine-control allowance. Full routers, dispatch, async, request/context and the
remaining runtime catalog are required by the active full-Hono goal.
