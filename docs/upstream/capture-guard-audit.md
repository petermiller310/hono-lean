# Guarded-capture source and contract audit

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52`.

## Exact source and frontend boundary

The complete original block at lines 158–160 is 102 bytes, `[4838,4940)`, SHA-256
`beff10a225df509ff6010efcaa6271d564693b14a5f1d683d90937170d7c023b`.
The checker binds exact working/Git bytes, component artifacts, metadata and
generated Lean strings. Kernel equations parse the complete source and
reassemble guard, assignment and closing brace. No synthetic source body is
inserted. `matcher.exec` at line 156 and the outer `if (m)` are excluded.

Shared syntax admission adds only the method name `hasOwn` with two recursively
admitted arguments. The existing call AST/evaluation order, if branch and
assignment/index machinery remain. Frozen `objectConstructor` method preparation
and an intrinsic case call the existing ordinary `hasOwn` descriptor operation.
Expr/Stmt/Value/State ABI and Set/assignment behavior are unchanged. Admission
does not establish a complete JavaScript frontend or arbitrary receiver support.

`Object.hasOwn`'s ordinary-object/primitive-key specialization follows the fixed
[2025 algorithm](https://tc39.es/ecma262/2025/multipage/fundamental-objects.html#sec-object.hasown).
General receiver boxing and property-key coercion are outside this domain.
Method preparation precedes left-to-right argument evaluation; the intrinsic
observes the resulting current state. StandardObjectBinding respects a local
binding before the ambient constructor; shadowing is not silently ignored.

## Independent contracts and proof domain

HeaderInputs records the initial standard Object binding, actual params/name
bindings, allocated target ordinary object and unique own keys. OwnInputs adds
an existing descriptor only: no match, writable, enumerable or getter-call
readiness. The source theorem derives the skipped branch and exact unchanged
state for every descriptor value/kind/flag combination in this model.

AbsentInputs instead requires no own descriptor, actual initial m array/own-zero
string/length facts, and a finite DescriptorPath built from before-state object,
own lookup and prototype-link facts. Its depth supplies the existing property
fuel bound. No future evaluator/Set success or desired result is assumed.

An independent descriptor classification distinguishes creation, legacy setter
ignore, supported rejection and unsupported custom-setter execution. The actual
assignment derives its Set dispatch through the initial path. New data has
W/E/C flags; existing target properties/prototype/extensibility and all other
ordinary cells are framed. Arrays/environment/private/function/Set/this fields
remain exact. The legacy primitive-string setter case is unchanged/no-own even
if the receiver is nonextensible. Missing setter/read-only/nonextensible write
rejection is distinct from unsupported behavior.

The object model specializes the standard
[ordinary Set algorithm](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-ordinarysetwithowndescriptor)
and the normative-optional
[legacy prototype setter](https://tc39.es/ecma262/2025/multipage/fundamental-objects.html#sec-set-object.prototype.__proto__).
Native interpretation additionally requires a legal ordinary descriptor graph,
adequate finite traversal budget, standard realm/intrinsics, primitive key and
string capture, and successful resources. Generic setters, proxies, symbols,
boxing/coercions and general native/host/engine adequacy are visible gaps.
An unsupported getter descriptor can still be safely present when never called.

## Preparation and composition limits

The inhabited examples execute selected class/constructor/registration source
preparation before applying the universal capture contract. A separately parsed
ordinary-object/m-array fixture supplies that local preparation. It does not
erase or prove the other arm of the actual line-123 conditional/spread, execute
Node.insert traversal, derive a regexp result, or establish intervening search
reachability. A source-prepared witness proves the domain is inhabited; it does
not generalize the fixture into all runtime callers.

Local params and final handler output are distinct objects. The legacy setter
leaves the local object without an own `__proto__`; a later inherited read can
copy Object.prototype into an own key on final null-prototype output. Whole-router
finite regexp probes reproduce the existing D1 shape, without changing its
baseline/allowlist or claiming a complete helper/search composition.

## Native/model evidence and observer

Fixtures allocate every referenced array/object on both sides, preserve initial
array identities, and observe object own descriptors, prototype references and
extensibility. The harness sorts descriptors extensionally; it claims no native
own-key enumeration order. No getter is invoked merely to observe a descriptor.
Native getter/setter counters are actual fixture-callback observations, removed
from model comparison rather than fabricated in the model.

The independent oracle searches initial descriptors and classifies the outcome;
it does not execute either implementation. The main corpus has 672 own-skip
and 1,012 absent/prototype contexts, including 128 particular throwing custom
setters. Those 128 cases compare rejection only; they do not show that every
custom setter rejects. The source model reports that execution as unsupported.
There are also 37 Node contexts, six explicit binding controls and six Bun
whole-router regexp scenarios. Full-window native execution checks all 315
pinned blobs and inserts the exact original 102 bytes into a strict wrapper.
The whole-router probe uses unverified Bun TypeScript loading. Native-only
boundary probes exercise unsupported prototype mutation, boxing and long
chains separately. Failed cases compare rejection only, not error taxonomy,
partial state or rollback. Six admitted source faults and artifact/hidden-edit
identity failures are required, alongside syntax controls.

Focused/root warnings-as-errors builds, fresh kernel replay, imported names/kinds,
axiom audits and independent final review are recorded in the proof registry.
No unfinished proofs, custom axioms or native proof shortcuts are accepted.
CI is configured; remote CI and a fresh parser-registry install are not claimed.
All fixed runtime coverage, full routing behavior units and native adequacy
obligations remain open.
