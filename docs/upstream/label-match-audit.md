# Audit: actual Hono label capture producer

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52`.

The complete59B url.ts60 declaration is `[1387,1446)`, SHA-256
`e1a741ae801aec83c5926a9d2b71e0b2a6dce9ee29406ef602a8d54a862d0207`.
The42B call and29B regex literal have separate checked spans/hashes. The external
checker verifies the clean Git pin, whole source identity, complete LF line and
all copied/generated artifacts. The kernel parses the exact generated declaration
to a retained literal-call AST and reparses/compiles its original regex units.
Python/Git/hash tooling and native/frontend adequacy remain explicit boundaries.

## Independent language, operational machine

`LabelRegExp.Label` describes colon + nonempty no-brace name, optionally followed
by braces containing a nonempty body without LF/CR/LS/PS. Names may contain those
terminators, NUL and lone surrogates. The body is RAW text, not an assumed valid
future regex. The language relation never calls the parser/compiler/VM.

The structural parser retains assertions, literal/negated-class/dot atoms,
consuming plus, captures and noncapturing optional groups. Compilation yields
real tests, capture saves, sequencing, greedy repetition and optional branches.
The ordered-candidate interpreter consumes actual code units, carries cursors
and immutable capture snapshots, and tries continuations in greedy order.
`execute_label_iff` and `execute_label_miss_iff` give universal success/capture
and miss characterizations. Uniqueness, exact spans, extraction, bounds and
progress are checked. Total structural recursion does not establish native
memory/time capacity. Canonical parser provenance is exact-source only; it is
not a universal adequacy theorem for every accepted frontend program.

The source-call frontend admits no-flags, structurally leading-anchored forms.
Unsupported valid-native `/i` and unanchored searching are explicit refusals,
not native SyntaxError or false-miss claims. Original Hono60 and all five
retained supported mutations remain admitted. General search, flags, lookaround,
nullable repeated captures and native parser/regex adequacy remain open.

## Real current calls, getters and identities

The receiver is evaluated and CURRENT String.match saved before argument
creation. The literal uses an intrinsic constructor/prototype interpretation;
it does not read lexical RegExp. Allocation begins with own lastIndex undefined,
actual literal parsing/compilation follows, and ordinary Set initializes 0.

Existing String.match gets typed Symbol.match and calls it with original O.
Selected 2025 RegExp@@match converts its input, reads/converts current flags,
then gets/calls current exec on the nonglobal path. The standard flags getter
performs eight CURRENT property reads with truthiness conversion. Current DATA
and missing getters dominate any old accessor identity metadata. Flag getters
use the original receiver, its Label/range OriginalFlags, or the specified
RegExpPrototype special case. Unknown getter identities refuse explicitly.

The new accessor sidecar refines an actual current unsupported-getter descriptor
with a closed callable identity; it never caches results. It cannot independently
prove native accessor identity/replacement coherence, function-object properties,
realm/bootstrap or arbitrary callback effects. Those are open interpretation
obligations. Model get-events record successful read completion; nested getter
reads can therefore precede the enclosing flags Get event in the trace.

The matcher reuses the OLD exec identity 5 rather than introducing a second
identity for the same native function. Six old registry partition bounds and
new-table disjointness ensure unambiguous identities in the admitted realm.
This preserves the current prototype across literal, constructor and route exec;
there is no staged prototype reset between source activations.

## Source contract and composition

`source_match_satisfies` starts from label plus OLD realm facts, not completed
captures. The independent Contract constrains the actual environment, fresh
three-entry result and seven property views from the language relation. An absent
optional capture is OWN2 undefined; a miss binds null and allocates no capture
array. Both outcomes still derive a fresh initialized literal. Old object/array,
Label/range result/brand, caller/function/private/set, iterator/symbol/accessor
frames and ordered protocol are retained. There is no arbitrary uint32 bound
on model input strings; native string/resource interpretation stays separate.

`produced_constructor_inputs` reads real index1/2 from the computed match array.
`source_match_then_construct_satisfies` covers supported safe ordered ranges.
`source_label_construct_binding_digits_exec_satisfies` additionally composes
actual 68→138→156 and RETAINS the final independent NodeRegExpExec.Contract:
actual language result, fresh match allocation and old-state frames. The query
and old realm/constructor/iterator identities are initial facts. Name/body/tuple/
future regex brand/matcher binding/m are derived in causal order.

These are selected activations. Actual wildcard/if/cache/terminal-vs-lookahead
selection, module closure reachability, child-pattern installation, intervening
search control and 146–154 query production are separate obligations. This does
not prove complete getPattern, Node.search, native execution or package coverage.

## Executable and native evidence

The independent Python oracle decomposes labels without using a regex or VM.
Seven groups pass with 5,193 labels and 3,970 selected four-stage contexts, all 1,953
safe endpoint pairs, five supported source faults and four nullable regression
cases. Native main matching is UNWRAPPED. All 315 pinned blobs and exact59/46/44/51
source bytes are checked. Caller/null-prototype and old regex canaries are aligned
with model descriptors/extensibility. Visible comparisons cover captures, seven
own descriptor views, tuple/constructor regex/bindings/exec outputs and old roots.
Sorted own-name sets are not raw native enumeration-order claims.

The temporary literal/iterator identities, internal records/code, allocations,
compiled-from-stored-source check and protocol traces are MODEL ONLY. Sensors
read actual stored model records/objects, not declaration echoes. Driver function
frame checks use an unverified representation serializer; independent formal
frames do not depend on that observer. Source wrappers, JSON/reference transport,
engine/frontend/realm embedding and partial error-state/error-class/rollback
correspondence remain unverified.

`ENGINE-FLAGS-1` preserves bounded per-engine evidence: pinnedNode22 reads global
directly while pinnedBun1.4 uses the selected 2025 flags path. An installed fresh
own flags getter throws only on Bun; Node succeeds with the ordinary capture
result. Exact traces/outcomes and complete prototype restoration replay in
`check-native.py`. This is native-only, outside the current standard realm.
Historical ENGINE-ELISION-1 and D1 records/allowlists are byte unchanged.

Root87b9b8 found a REAL generic model bug: accepted `/^()?$/` returned an empty
capture where both native engines returned undefined. Code.optional was repaired
to retain only strictly advancing body candidates before the ORIGINAL skip
snapshot. Monotonicity/consuming-prefix/zero-only lemmas prove the mechanism;
canonical statements/domains and all earlier witnesses remain. New kernel and
native/model regressions also retain an empty inner capture when its optional
parent consumes. See `nullable-regression.json`; this was not relabeled as a
frontend refusal or erased after a passing run.

## Completed gates and remaining interpretation

Generic repair 4843 passed 6 jobs,13 witnesses and 8 actual axiom guards. Concrete
69924 passed 64 jobs and combined 65 passed after repaired-core recompilation:
17 witnesses and 6 actual guards. Full 35172 passed 677 jobs with warnings as
errors. The advertised registry has 167 declarations (90theorems/77definitions)
and 20 transitive axiom targets. Audit 89708 resolved all actual Lean declaration
kinds and enforced the transitive standard-only allowlist; the 14 in-file guards
also pass. Fresh kernel 6987 completed terminal exit 0 with its original silent
handle preserved. All new Lean files were frozen before the root/fresh gates.

Root 86871 passes seven groups16.914s; binding regression 78212 passes six groups
29.692s, comparison 86893 retains 467 agreements/one exactD1/98 appends/zero
unexpected, and routing 1363 passes three groups1.460s. Independent proof/spec,
native/oracle and semantic-repair reviews and final metadata/diagram
reconciliation are clean. Source/name recheck 13111 reproduced all 167 names/20
targets, with source identity and both native-boundary replays independently checked.

Prior 33 source clusters/32 additional slices, original 30 assumption IDs/statuses/
source theorem lists, all 36 full routing statuses, all old Lean modules and fixed
SPEC/target/catalog/D1/comparison/benchmarks remain unchanged. The new record is
conditional; zero unconditional Hono runtime claims are asserted.
