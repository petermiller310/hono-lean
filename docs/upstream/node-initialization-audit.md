# Node data-field initialization: independent audit

This audit concerns Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`, with two separately translated
source windows in `src/router/trie-router/node.ts`:

| Window | Lines | Byte range | SHA-256 |
| --- | --- | --- | --- |
| Module preamble | 17–18 | `[417,470)` | `df69a2bc8c1a798a716361053f30aaca24ca5ec79e5195e2ff13aa5358185702` |
| Five private data fields | 21–26 | `[494,708)` | `cc620af41bea64739c5d2f8bc8cd512b222e665b0117c06ad9a30a25713b73e9` |

The [source metadata](../../verification/node-initialization/source.json) also
records the containing class as provenance. Its full text/hash does not make
the selected field parser a complete TypeScript class parser. In particular,
the actual private method `#pushHandlerSets` lies outside the data-field block.

## Fixed-edition initialization order

The comparison uses ECMA-262 2025. Its
[instance initialization](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-initializeinstanceelements)
adds private methods/accessors before processing the ordered fields.
[DefineField](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-definefield)
evaluates the initializer, or selects undefined when none exists, before
installing that field. [PrivateFieldAdd](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-privatefieldadd)
rejects an existing matching private identity and appends private storage; it
does not dispatch through ordinary property setters or extensibility flags.
Host rejection for relevant exotic objects remains a separate boundary.

Consequently, the optional uninitialized `#pattern` must receive an undefined
slot. A self or later-field read cannot be justified by preinstalling all five
slots. The selected data-field argument also cannot establish Node's omitted
private-method installation, default constructor, `newTarget`, heritage or
native class/module linking.

## Module and instance identities

The actual preamble allocates one null-prototype `emptyParams` object and
initializes the lexical order value to zero. Successful field initialization
must give each instance fresh methods and patterns arrays and a fresh children
null-object, while its params field initially aliases the module's shared
emptyParams object. Methods and patterns must also be distinct within one
instance. Ordinary reflection should not manufacture a matching private brand.

Private names belong to the evaluated class definition. Different instances of
one definition reuse those names but have different owner storage. Different
class definitions need distinct names even when neither has an instance yet.
The runtime's explicit persistent `PrivateWorld` allocator addresses
that reservation requirement; recomputing freshness only from installed owner
slots would be insufficient. `initialPrivateWorld_fresh` bounds every identity
in the initial active names or existing private slots, and
`successive_definitions_disjoint` separates reservations for successive
definitions before either is instantiated. Freshness requires initializing the
world once and threading it thereafter. The concrete initialization theorem
accepts a world parameter; it does not independently establish that caller
discipline for every arbitrary supplied world.
`parsed_fresh_initialization_seed` specializes that argument to the checked
initial cursor and additionally proves absence from every identity represented
in the initial store. Unrepresented prior native class definitions remain
outside that store model.

The admitted field parser deliberately excludes `this`, `super`,
private-dependent initializers and direct lexical increments. Native ordering
probes for those constructs test the surrounding semantic boundary, rather
than proving support for their syntax. Frozen captured value environments also
do not establish general mutable lexical-cell or helper-closure behavior: even a read-only
initializer could otherwise observe a binding changed after class definition.
The actual five Node initializers need only array allocation, the checked closed
helper invocation and reading the shared emptyParams binding.

## Source-to-model argument

`parses_preamble` and `parses_fields` tie both source windows to retained ASTs.
The field parser preserves nested generics, arrays, the optional marker and
union metadata, and rejects unsupported declarations and initializer forms.
Erasing TypeScript types is part of the model interpretation, without a proof
of the native transpiler. Parser examples include rejection of
`other.#name`, `this`, `super`, direct increments, duplicate names,
`#constructor`, methods, public/static/accessor fields and malformed boundaries.

The successful runtime argument allocates an empty owner, evaluates each
initializer, then adds that field's private slot before continuing. Its contract
preserves previous objects, arrays, private owner slots, functions and Sets;
it restores the caller's value environment and active private names. A supplied
prototype must be allocated, and dangling private-slot metadata at the next
owner address is rejected rather than overwritten. Private addition ignores
ordinary descriptors and extensibility, but still checks owner allocation and
duplicate private identity. The `Except` result does not model partial heaps
or captured side effects after a thrown initializer or duplicate-add error.

`parsed_initialization_seed` composes the parsed preamble, class-data
definition and instance contracts to derive the registration history's initial
owner, methods slot, empty methods array and zero counter. Its assumptions
retain the checked helper interpretation, an allocated old root, a supplied
prototype and fresh owner metadata. `classActivation` explicitly supplies the
source-derived data-name lexical context to later fragments; it does not
install the omitted private method or prove a native method call. No completed
registration `Seed`, desired slot contents or desired counter is an entry
assumption. The generic examples additionally exercise multiple instances,
successive definitions without instances, caller-scope restoration,
nonextensible private addition and initializer-error precedence over duplicate
addition.

The concrete examples start with nonempty old objects, arrays, Sets and private
storage. They reserve identities `32..36` and `37..41` before creating either
definition's instances, then execute the selected source fields for two
instances. A parsed registration push changes only the first instance's
methods array; children and patterns remain separate, params aliases the
module object and pattern reads undefined. A fresh-source Seed and an inhabited
GET hit/POST miss/ALL fallback pipeline use the general theorems. Three Lean
source-edit observations and two metadata controls also execute newly parsed
declarations. Deleting the pattern declaration produces a missing lexical-name
error, distinct from an existing-name/wrong-owner private-brand error.

`parsed_initialized_pipeline` composes this initial state with arbitrary
admitted source-push registration histories and the complete selected capture
loop. Its remaining context concerns caller bindings, actual parameter reads,
helper/realm interpretation, old prototype conditions and size bounds. It
retains the earlier boundary that insertion traversal supplies registration
events; it does not derive routing traversal or establish complete native
construction and method calls.

## Independent native observations

An independent Bun 1.4.0 probe checked the fixed revision, clean checkout and
all 315 pinned source/package blobs, then transpiled the exact two source
windows inside an explicit supplied class/helper wrapper. Input and emitted
wrapper hashes were:

- Input: `87c7524065dd112ad980bc3d3becc3dfb1423aae4e4bd238d553f808fa5ba8c0`.
- Emitted: `45a06f9e7d6daf95cb3fde2674478cad02bb84b660d02b8b95bf4e3d5e949f04`.

The wrapper observed fresh methods/patterns/children for two instances, distinct
own arrays, null-prototype children, installed undefined pattern, shared module
params, no public own fields and isolation after mutating one methods array.
A different class definition and a prototype-only clone both failed the
original definition's private reads.

Separate generic native probes observed self/later-field read failures,
successful earlier-field and undefined no-initializer reads, and private-method
availability during the first field initializer. Stamping a nonextensible
ordinary object succeeded. Attempting a second stamp with the same private name
ran the initializer again before throwing, leaving the observed initializer
counter at two. These bounded observations preserve ordering/failure boundaries;
they are not proofs of native construction or partial exception-state adequacy.
TypeScript transpilation is explicitly unverified.

The landed [native harness](../../verification/node-initialization/native.ts) was
also independently replayed with class instance-count vectors `[2,1]`,
`[0,2,0]` and `[]`, together with its scope probes. It verified the same source
identity and all 315 blobs. Its class-brand matrices, helper-call counts
`1 + instance count`, supplied prototypes, isolated allocations, shared module
params and boundary observations agreed with the intended cases. Its wrapper
contains the actual omitted private method as explicitly supplied native
scaffolding. Its input SHA-256 was
`4c238b3b9707a2918329f4ed230fff641a0af8a31593674202d0e94e1d286ea7`;
its emitted SHA-256 was
`e65922ab837cede0f661a4eabde741ed240fc99d0415da22ad1f29c515cd55a7`.
The separate source-identity checker passed independently as well.

## Review status

The shared runtime, freshness argument, generic examples, concrete
preamble/instance contracts, registration-history bridge and inhabited
nonempty-state/mixed-pipeline examples have been reviewed against the above
boundaries. Review caught and resolved private-dependent
initializer acceptance and the need to exclude direct lexical writes; persistent
identity reservations also remain explicit. No unresolved issue was found in
the reviewed domain.

The parent separately confirmed the integrated five-group differential suite
passed in 5.568 seconds: 341 exhaustive class/instance-count contexts, 131
seeded/long contexts, six runtime source mutations, two erased-metadata controls,
native boundary probes and artifact/hidden-checkout-edit failures. Direct driver
execution with prior stamps `[7,100]` and the existing five routing source
regression suites also passed after the shared syntax/runtime changes. These
are bounded tests, distinct from the Lean proofs and native adequacy.

The concrete implementation owner confirmed the final focused build passed
64 jobs in 18 seconds, along with the source-identity/embedding check. The parent
then confirmed the integrated root `lake build` passed 275 jobs. The main pinned
comparison retained 468 lookups, 467 agreements, the exact known D1 discrepancy
and 98 append checks; inventory byte checks preserved structural-only coverage
at zero. Split-path, query-string, null-object, adapter and routing regressions
also passed.

The parent separately confirmed `lake env leanchecker --fresh HonoLean`
completed with exit status zero. This fresh root replay checks the integrated
proof declarations in a fresh kernel environment. The successful builds,
kernel replay and finite tests leave the native class/module/caller/heap
adequacy boundaries stated above open.
