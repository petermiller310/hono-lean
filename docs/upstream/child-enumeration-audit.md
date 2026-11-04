# Child-enumeration source and proof audit

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52`.

## Exact source

The complete node.ts174–180 block occupies bytes`[5388,5705)`,317B, SHA-256
`fce614b83a4e70c4b00d6f4e8e609d20109770daf866b281b2677862be5168c2`.
The prefix 174–175 is88B, the existing 176–178 count/schedule dependency is191B,
and the suffix 179–180 is38B. The external checker compares the clean pinned
checkout's working bytes with Git and validates every artifact and dependency.
The kernel checks the original for-in/private-write/regexp/sparse/break syntax
and full reassembly. No body or break is supplied as a fabricated placeholder.

The new ForInSequence entry preserves old AST/value/state and parser admission.
RegExpSequence adds forwarding helpers only. Supported statements retain real
loop and break completion nodes; deleting break yields genuine repeated body
execution. The parser excludes head references to its own uninitialized binder,
body uses of that binder, lexical rebinds, visible increments, callbacks,
unsupported private-write shapes and relevant ordinary-object mutations.
This is an exact selected-source argument, not full TypeScript parser soundness.

## Domain and independent contracts

Initial facts identify the actual child binding, allocated owner/private brand,
raw DATA children slot and allocated null-prototype ordinary children object.
Its keys are primitive raw UTF-16 strings with unique own names and descriptor
flags. Enumeration does not read data/getter values. The independent enumerable
membership contract derives entry/emptiness from those descriptors.

The empty theorem does not require body inputs or writable params storage.
The entered theorem requires initial params DATA storage and binding, matched
string array/own0 UTF-16 input, input length bound, pending queue and initial
selected-target admission. The shared assignment evaluator updates the private
cell before the existing count/schedule semantics run. An initial enumerable
descriptor witness establishes entry; it does not choose the first iteration
key. No future count, queue or successful intermediate operation is a premise.

ForInState retains an explicit ambient State and authoritative RegExpState with
sparse arrays. Its computed view supplies current env/read-value array data;
ambient env/heap fields are not an alternate execution cache. Private writes
retain exactly the shared evaluator's private-store effect, with full frame
proofs for the admitted variable-only assignment. Scope restoration keeps the
private/array/regexp effects and removes iteration/body locals. Break is consumed.

All-order proofs quantify over permutations of the independent key set. The
actual source body derives a common endpoint for every such key. No first-key
order is supplied as a native fact. This superset of native orders is safe
because the key is unused and the body does not mutate the enumerated ordinary
object heap. The intended reference is
[ECMA-262 2025 ForIn/Of evaluation and enumeration](https://tc39.es/ecma262/2025/multipage/ecmascript-language-statements-and-declarations.html#sec-enumerate-object-properties).

General prototypes/inherited shadowing, symbols, exotic objects/proxies,
null/undefined/primitive heads and enumeration mutation are outside the formal
normal domain. Native probes preserve their observed behavior separately; a
model unsupported error is never asserted to be a corresponding native error.
Earlier field initialization suggests the intended null-prototype shape, but
full initialization/insertion/search reachability still needs composition.

Native interpretation also requires standard frozen String.match/RegExp@@match/
exec and array methods, ordinary writable array operations with clean numeric
prototypes, exact legal numeric indices and successful resources. The earlier
count slice's tracked-A/per-exec-array projection is retained. These are explicit
language/host interpretation premises, not assumptions of a Hono result.

## Finite checks and observation boundary

The main suite has 598 contexts:255 descriptor/skip-with-missing-or-invalid-body
inputs,156 raw UTF-16 strings,50 params/queue combinations,4 matched-array/queue
aliases,130 seeded contexts and 3 long slash runs. Node repeats 36 selected cases.
Eight admitted faults change real loop/private/count/scheduling syntax; negative
parser, layout, stale-artifact and hidden-source edit controls are separate.
Native boundary probes cover 12 cases per engine, including empty-string names,
getter avoidance, multiple-key break, readonly params, inheritance/shadowing,
symbols and null/undefined heads.

The independent oracle tests descriptor existence, enumerates slash indices,
and applies sparse own-slot/alias transitions; it never calls the source
evaluator or uses model/native outputs as expectations. Canonical graph roots
are all initial arrays plus final private values, in fixed order. BFS assigns
new reachable array IDs; ordinary descriptor maps are compared extensionally.
Unreachable internal A/iterator allocations are omitted, not fabricated as
observed native empty arrays. This observer does not check total allocation
counts or all internal full-store frames; the formal contracts cover those
modeled frames separately, and native adequacy remains open.

Uninstrumented native controls retain standard methods. Separately cloned
match/exec instrumentation records returned native matches, positions,
lastIndex observations and params at match entry. Initial lastIndex0 is a
read, not an observed reset write. Model traces compare actual appended regexp
cells with operational execution metadata; their returned-match list is
derived, with actual accumulator observations retained in the earlier count
suite. No fabricated model paramsAtMatch/getter event is compared. Native
getter reads are asserted zero. A separate reordered-write native fault
demonstrates an ordering difference despite identical final graphs.

The dynamic private class, fixture construction, initialization, source hashing,
wrappers, engines and graph transport are unverified evidence. Rejection checks
observe failure only, with no exact exception or partial-state equivalence.
The suite is replayed in the pinned CI workflow; a remote run and fresh parser
registry installation remain unvalidated environment checks.

## Remaining obligations

The registry records focused/integrated managed builds, fresh kernel replay,
actual declaration-kind resolution, standard-axiom audits and independent
review. No incomplete proof, custom axiom or native proof shortcut is accepted.

This closes a conditional selected-loop source contract. It does not close a
complete routing behavior unit, `matcher.exec` input production, surrounding
search control flow, final sorting/mapping or whole Hono. General language,
frontend/class/module/native/host adequacy and the entire fixed runtime catalog
remain explicit obligations of the active goal.
