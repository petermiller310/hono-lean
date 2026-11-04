# Builtin range-plus exec: source and contract audit

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52`.

## Source identity

The actual line 156 declaration is51B `[4766,4817)`, SHA-256
`dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625`.
The separate21B line 157 header is `[4817,4838)`, SHA-256
`042e769ef1bf1960c8afe661fb6685043688d65289af9f4e6611beaa86d4336f`.
`verification/builtin-exec/source.py` checks the clean revision, working/Git
source bytes, metadata, committed fragments and generated Lean strings. The
kernel parses actual 156 using the previous declaration parser. It checks 157's
header tokens and evaluates its variable test. No replacement body is invented.

## Generic machine and independent contracts

`RangeRegExp.Grammar` independently describes the exact eight-unit source
syntax with safe ordered alphanumeric endpoints. `parse_iff` proves both
directions. `compile_anchoredPlus` yields start, consume-range, repeat-range,
end and accept instructions. The operational machine consumes actual input and
advances its cursor. `Accepted` independently requires nonempty input and every
unit within the interval; `execute_anchoredPlus`, `execute_success_iff`,
`execute_matched_iff`, `parsed_execution` and nonexhaustion theorems connect it
to execution and exact whole-input/no-capture spans.

The compiler also admits some manually constructed syntax. The source grammar
and headline machine theorem are specifically anchored range-plus programs;
they do not establish general compiler or native-regex adequacy for arbitrary
ASTs, bytecode lists or branded records. Concrete source Inputs requires
`initializeRangeRecord digitsPattern [] = some record`, tying its actual
internal program to the checked digit parser/compiler. It does not accept a
desired match, completed call or arbitrary result callback.

## Callable identity, brand and state

The new closed dispatcher preserves ordinary `MemberClosure` execution and adds
an explicit builtin callable interval. It saves the current receiver/property
before arguments, then selects the saved function identity, never the spelling
`exec`. Checked range separation excludes the prior NoArg/private/function/
member kinds from the new builtin range; it does not prove all older tables
mutually well formed or make the old NoArg interval natively noncallable.

The builtin checks brand before primitive-string argument admission, reads the
current ordinary lastIndex descriptor, performs the modeled exact-safe-integer
ToLength, checks the internal empty-flags program and executes it. No cached
lastIndex exists in the internal record. No public source/flag getter determines
the program. For these no-g/y programs there is no lastIndex Set, including on
a miss. String/object/fractional/nonfinite/negative-zero/Symbol lastIndex
coercions and all flags remain outside this formal numeric/string domain. An out-of-domain
model rejection is not automatically a corresponding native exception.

The interpretation follows ECMA-2622025
[RegExp.prototype.exec](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-regexp.prototype.exec)
and [RegExpBuiltinExec](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-regexpbuiltinexec).
Those specification/native interpretation links remain reviewed assumptions,
not a formal native-language adequacy theorem.

## Result and source composition

Success appends exactly one dense modeled array with its whole matched string;
failure returns null and appends none. A sidecar retains only index/input;
zero/length are read from current heap contents. The five descriptors include
OWN groups undefined, with ordinary W/E/C attributes and the special length
attributes. There is no groups object, indices property or global accumulator.
This five-property observation projection does not implement every native
descriptor/prototype/enumeration/mutation rule. Existing sidecars/heap frames
are tested; arbitrary malformed/stale sidecar tables lack a global adequacy
claim.

`source_exec_satisfies` derives actual 156 and its independent digit-language,
value/heap/metadata/lastIndex/old-cell/scope/private/function/brand contracts.
`produced_guard_test` connects that value to the identified 157 test.
`source_init_builtin_created_collect_satisfies` starts before 123, retains both
initializer arms, computes 156 and composes actual full188B158–161 on the
accepted-digit/create path. Current map reads, target method rows and helper
layout are derived after the match append. The collector is an old heap cell,
so its append cannot overwrite the fresh match array; zero/groups preservation
is proved. No future Layout, early m, prepared match or reordered source 123 is
an input. Private closure/table installation, tuple/input production, omitted
146–154 and broader source control flow remain explicit assumptions/gaps.

An inhabited representative witness also derives its registration/collector
state from the parsed preamble, class/METHOD installation, GET/ALL registration
source and 202 write. It then adds the declared RegExp/prototype/brand fixture
projection before proving the pipeline. This strengthens source preparation
for that example without proving Hono's matcher constructor/cache/tuple path.

## Finite evidence and refusal boundaries

The independent Python oracle uses integer intervals, not Python regex syntax.
It checks 11718 core cases (1953 pairs ×6) and 758 full-world contexts against
the bounded model. Full-world cases also execute the exact plain-JS source on
Bun1.4.0/Node22.22.2. Four parsed source faults alter method, primitive-string
argument, receiver and declaration name. A borrowed name is a positive identity
control. The wrapper conservatively recognizes only pure DATA fixtures; its
callee-attribution lookup, JSON transport and observation are unverified.

The normal observer includes old heap contents, five match properties, exact
ordinary descriptors/prototype/extensibility, caller canaries, and bounded
fresh returned arrays. It separately asserts native result Array.prototype,
exact five own string keys/no symbols and intrinsic descriptor frames. These
finite assertions do not become formal full-Array theorems. Success-state
observations are compared extensionally; key order/physical or unreachable
allocation/native closure identity creation is not proved. Main failures expose
only rejection, without partial-error-state, exception-class or rollback
equivalence.

Handle 0 is a genuine old native function returning 0. The new dispatcher refuses
that old table interval; the suite records model refusal/native success
explicitly, rather than comparing it to a native numeric noncallable. Native
`^[0-9]*$` success likewise remains a grammar-refusal control. Resource
exhaustion is distinct from a regex miss. Four mutations and all refusals retain
their cases without changing the historical D1 baseline.

Native-only scripts record brand-before-ToString, input then lastIndex
coercion, ignored shadowed source/throwing flags, proxies, readonly/frozen
nonglobal behavior, g/y writes/failures and custom/noncallable exec. Actual
pinned getPattern/cache/tuple and whole-router probes check 18+15 queries; they
are explicitly finite/unverified and do not close constructor/cache/tuple
provenance. All native scripts assert 315 pinned source/package blobs.

The frozen SPEC/target/catalog, old 30 proof clusters, old 29 additional slices,
original 30 assumption statuses/theorem lists, all 36 full-routing statuses,
historical benchmarks and comparison/D1 stay intact. The new conditional
cluster does not establish an unconditional Hono runtime claim.

## Reproduce the checks

After the normal managed build, run:

```sh
python3 verification/builtin-exec/source.py --hono ../hono
python3 verification/builtin-exec/tests.py --hono ../hono
python3 verification/builtin-exec/audit.py
lake env leanchecker --fresh HonoLean
```

The declaration/axiom audit reads the exact names from the committed registry,
checks theorem versus definition kinds, and rejects any axiom outside propext,
Classical.choice and Quot.sound. Runtime fixtures require the pinned Bun1.4.0
and Node22.22.2; use HONO_NODE to select that Node binary. Test wrappers and the
source-identity checker remain external tooling, as the ledger states.

Final local gates:149 focused jobs and 609 full build jobs passed;114 exact
registry names resolved (74 theorems/40 definitions),15 transitive axiom audits
used only standard logical axioms, and fresh kernel replay 63408 completed
exit 0. All 29 public witnesses and 13 in-file axiom guards remain checked.
The first two audit-script runs failed on a reserved local name and a missing
CollectAxioms import; fixing the checker retained every target and allowlist.
The registry preserves the earlier local proof/checker repair history.
