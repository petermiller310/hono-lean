# Selected Node private-element installation: independent audit

This audit concerns pinned Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`. The proposed connection combines
the module preamble at `src/router/trie-router/node.ts:17–18`, five private data
fields at lines 21–26 and the private method declaration at lines 64–84.
Registration and call composition reuse the exact push at lines 55–61 and the
selected call entries at lines 115 and 191.

The source file SHA-256 is
`faa72577fbea974a954c6c0e36546e3f53da97418ae154d2583ae43de1e5a825`.
The containing class is provenance. Public `insert`/`search` bodies, complete
class evaluation, native constructor/prototype lookup and whole routing
reachability do not become verified merely because selected private elements
share that containing source class.

## Fixed-edition order and sharing

The review uses ECMA-262 2025. Its
[private-name list](https://tc39.es/ecma262/2025/multipage/ecmascript-language-functions-and-classes.html#sec-static-semantics-privateboundidentifiers)
follows declaration order, and
[class evaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-functions-and-classes.html#sec-runtime-semantics-classdefinitionevaluation)
creates fresh private names. Node's selected list is `methods`, `children`,
`patterns`, `pattern`, `params`, then `pushHandlerSets`.

[InitializeInstanceElements](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-initializeinstanceelements)
installs private methods before processing fields.
[PrivateMethodOrAccessorAdd](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-privatemethodoraccessoradd)
rejects an existing identity and shares the definition's method value across
instances. Consequently, method installation order differs from the source
name-reservation order. A duplicate method stamp also fails before a second
field initializer can run. These rules do not prove host-exotic acceptance or
native engine adequacy.

## Required model boundary

The selected-private-elements runtime should derive one complete six-name map
and append a closure built from the parsed method, captured value environment
and that map. It must thread the private-name reservation cursor and method
table across definitions, including definitions created before any instances.
Reconstructing either allocator from only installed instances would lose live
definition reservations.

Review identified that a cursor seeded only from state names/slots would miss
private names captured by older method-table closures with no instances. The
runtime now uses `initialPrivateClassWorld`: its bound includes state identities
and every retained closure's private-name identities. Checked membership lemmas
cover both sources. A regression reserves above an old closure-only identity
1000, while an empty table agrees with the earlier seed. Unrepresented external
or zero-method definitions still require the persistent world protocol; an
arbitrary supplied world cannot establish global native-class freshness.

The existing method table occupies an explicitly disjoint function-handle range
from expression-only helper functions. Table append must preserve old entries,
derive each new handle from the previous table length, and retain the caller's
function-table separation condition. Native unified callable objects remain an
interpretation obligation.

A fresh ordinary owner must acquire its method read handle before ordered
data-field evaluation. The five data fields must preserve that installed handle,
allocate separate methods/patterns arrays and a separate children object, install
undefined for pattern and initially share the module's empty params object.
Old heap/private storage and caller scope must be framed. The owner prototype
and imported helper interpretation remain explicit inputs; ghost private
metadata at an unallocated owner must not silently become a valid new brand.

The existing private store represents values without field/method kind tags.
Using it for selected method reads therefore does not establish private-method
assignment semantics or read-only enforcement. Class home objects, `super`,
native closure creation, live module cells, arbitrary nested block calls and
partial exception-state effects remain outside this extension.

## Independent native evidence

An independent Bun 1.4.0 probe checked the exact revision, clean checkout and
all 315 pinned source/package blobs. It transpiled the exact preamble, selected
fields and method inside explicit class/default-constructor scaffolding, with
the exact registration push and selected call expressions in wrapper methods.
The wrapper input SHA-256 was
`d90d7b5133c37c04cb78406b8112ae04e6c3711d83b4fed8da7ff34a02ef217d`;
the emitted SHA-256 was
`a3f37045db6647127ec24311f6d2d2efc29388ad416e03aca1ce24aa26e40fe6`.

Two definitions were created before instances. Two instances of one definition
shared the same private method value but had distinct methods/patterns arrays
and children maps. A separately evaluated definition had a different method
value and private brand. Initial params shared the preamble's null-prototype
object. Foreign instances and prototype-only clones failed private reads.

The exact push registered GET, ALL and a POST miss with supplied duplicate key
events. Actual source calls to the resulting nonempty table returned GET/ALL
records with null-prototype captures. The four-argument call captured
`old0/old1`; the reversed five-argument call captured `old0/temp1`. Module order
was three. These observations cover explicit wrapper entry states, not the
surrounding insertion/search traversal.

Separate generic native controls observed a method during field initialization
and a duplicate method stamp failing before the second field initializer
(counter remained one). A direct native JavaScript control rejected assignment
to a private method. An initial combined TypeScript-wrapper write control was
removed after the transpiler warned/rejected it; the final write control uses
direct JavaScript evaluation, separate from the exact-source wrapper.
Transpilation is explicitly unverified. These bounded probes do not establish
general class, failure-state or native language adequacy.

The landed [native harness](../../verification/class-installation/native.ts) was
independently replayed with counts `[0,2,1]`, same-definition receiver/target,
GET/ALL/POST-miss registrations, duplicate key events, a reversed five-argument
call and its generic scope controls. All 315 blob guards passed. The observed
brand/method-sharing matrices separated definitions; the two hits had scores
one and two, module order three, retained method values and null-prototype
captures. Its wrapper input SHA-256 was
`12d3949dd1883a9d1b9e2c9a97d430677204a1e661ae4859cced4f225e501a04`;
its emitted SHA-256 was
`642e02fb15aac81f5fdef1ec5100c24092bb5d91c39e3e3ed6eb58f7e5aa8e5e`.
The source-identity/embedding checker passed independently as well.

Review also corrected an independent-oracle edge: in the four-argument call,
an old null capture falls through `??` to the omitted fifth argument's undefined.
It must not remain null. A separate landed-harness replay confirmed undefined
for that case. This repairs the oracle expectation; it is neither a new Hono
defect nor a change to source or model behavior.

## Review status

Architecture, fixed-edition ordering, the independent native controls and the
generic [selected-private-elements runtime](../../HonoLean/Upstream/SourceSubset/PrivateClass.lean)
have been reviewed. Its six-name reservation/captured closure/table append and
method-before-field execution definitions match the declared projection. The
runtime owner reported its generic examples build passed 15 jobs in 2.6 seconds.
Those examples cover threaded zero-instance definitions, shared method/isolated
data storage, pre-field method availability, a derived-handle source-body call,
duplicate-method error precedence and rejection/frame controls. That report is
separate from this review and is not an integrated validation claim.

The concrete Program/Runtime/Contract/Correctness modules have also been
reviewed. Exact source parsing feeds definition/table construction and ordered
initialization, deriving both the registration Seed and private-call Callable.
The independent instance contract retains the old allocation/frame/field
observations and adds the installed method lookup. Framed field evaluation
preserves that method. No desired closure, branded read handle or successful
body execution is assumed by the source initialization result.

The model driver, native wrapper and initial test corpus were reviewed. Query
params/private-write handoff remains explicit external staging; it does not
prove search traversal. The stronger concrete joint-freshness lemmas and
history/call composition were also reviewed: history frames the method handle,
the later collector preserves its callable context, and source argument
bindings join the existing history-derived protected Layout. That layout
derives capture readiness; no successful call execution is supplied.

The parent confirmed the final differential suite passed eight groups in
12.521 seconds after the driver selected the joint state/table seed directly.
It covers 1,418 contexts: 341 exhaustive and 131 seeded/long class/instance
contexts, plus 686 exhaustive and 260 seeded/long initialized registration/call
contexts. Nine source faults and four metadata controls, native boundary probes,
source/artifact guards and hidden-checkout-edit failures passed. These bounded
tests are attributed to the parent run, separate from independent replays.

The final inhabited examples have been reviewed. The direct source pipeline
executes parsed preamble/factory results, reserves two definitions before
instances, initializes two instances of the first definition, runs three exact
registration pushes, allocates the real later collector and executes the actual
five-argument call. It observes GET/ALL hits with two nonempty temporary captures,
separate data arrays, shared method handles, foreign-brand rejection and complete
caller/private-store restoration. The older closure-only identity 1000 forces
the joint seed to 1001; the newer second-definition handle does not replace the
first definition's handle. Temporary caller params remain explicit old input
cells, without a search-production claim.

No desired Callable, Seed, completed registration state or call output is an
input to that direct execution. The separate universal source initialization
and history/call theorems provide independent contracts and the compositional
frame argument. The final general history bridge separates the receiver from
the registration target and frames the receiver's old allocated object. A
nonempty structural Context for receiver 4 and target 6 proves initial reads,
realm/prototype conditions, key bounds and GET/ALL/miss cases. The resulting
`initialized_source_history_has_call_contract` uses the general independent
call contract, rather than only the closed result observation.

No unresolved semantic issue was found in the reviewed domain. The concrete
owner reported its final focused Examples build passed 76 jobs, including this
contract-domain strengthening and direct source execution; source identity and
embedding checks passed. The parent confirmed the integrated root build passed
311 jobs. The pinned main comparison retained 468 lookups, 467 agreements, the
same exact D1 discrepancy and 98 append checks. Routing's three groups and the
byte-identical structural inventory check passed; generated source-connected
coverage remained zero. Adapter checks passed, including 20 CLI scenarios,
52 lookups, two append events, 30 rejection fixtures and 14 failed-registration
sequences. The final suite checks five source families, comprising its own
artifacts and four dependency families. The walkthrough, diagram, driver and
final proof/assumptions registry were reviewed without an overclaim.

The parent confirmed `lake env leanchecker --fresh HonoLean` completed with
exit status zero. This fresh root replay checks the integrated proof
declarations in a fresh kernel environment. Final independent review found no
unresolved issue within the declared source/model domain. These build, replay
and finite-test results leave complete class/public-method/default-constructor
evaluation, native method kinds/read-only PrivateSet, unified function objects,
live lexical/module cells, actual insertion/search reachability and full native
language/host adequacy open.
