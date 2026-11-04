# Complete body and arrow syntax: audit boundary

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52` (4.13.13).
Focused 74871 passes85jobs, Source79s and Examples4.2s. Root 59374 passes723jobs
with warnings as errors. Original fresh 77654 completed terminalexit 0 after all
seven new Lean modules were frozen. Audit 12260 completed exit0:48actual names
(32theorems/16definitions), all32transitive standard-only targets, and actual
parse-theorem source-constant type checks. All13witnesses/eight guards pass.

The [source checker](../../verification/getpattern-body/source.py) checks315clean
blobs and exact guard42B56–58, body576B56–77, declaration744B51–79, header78B51
and leading comments87B52–55. Reassembly is checked both externally and in Lean:
body=guard+LF+the frozen533B cache body; declaration=header+comments+body+closing
brace/LF/blank LF. The closing brace is line 78 and line 79 is blank. No actual
source byte or prior parser/runtime/AST was changed.

The declaration and leading-comment excerpts intentionally end with the pinned
upstream blank lines. The final staged default whitespace check flagged those
two EOFs after the local milestone commit was prepared. Their bytes are retained:
all other files pass the default whitespace check against5299cb6; those two
exact copies pass blank-at-eol/space-before-tab checks with only blank-at-eof
excluded. The source checker independently enforces their complete raw bytes.
This is a documented artifact-format boundary, with no D1/source-case allowance
or repository-wide whitespace configuration change. The scoped command uses
`core.whitespace=blank-at-eol,space-before-tab,-blank-at-eof` for those two files;
omitting the explicit minus option keeps Git's default EOF warning enabled.

## Advertised claims

The conditional cluster `url.getPattern.wildcard-body.source-subset.v1` has
48 actual public declarations:32theorems/16definitions,13 witnesses and eight
in-file axiom guards. The new audit resolves actual environment kinds and
audits all32theorems transitively against the permitted standard axiom set.
It also checks that actual parse-theorem TYPES refer to the retained body and
declaration constants, excluding splitPath's similarly named source.

| Claim | Entry facts and conclusion |
| --- | --- |
| Wildcard | Only current primitive label=`*`; return`*`, exact entire state identity, arbitrary model context/world |
| Nonstar relation | Current value binding unequal to`*`; exact delegation to old533B interpreter with one fuel step, including errors |
| Miss | Previous Label/std-realm miss facts PLUS explicit nonstar; independent null/frames contract |
| Warm/plain/terminal | Prior initial-only DATA/realm/constructor/range profiles; nonstar derived from colon language; original independent contracts retained |
| Actual50/reuse | Initial root-path/freshness facts derive two full576B activations on the same entire state/cache; Init/Terminal/Warm retained |
| Arrow syntax | Structural names/typed optional parameters/return union/raw inner source/comments/complete body; execution is body projection only |

The safe terminal domain remains the ordered safe-endpoint range-plus grammar,
all four typed terminal-next forms and arbitrary valid UTF16 names/suffixes.
Warm values may be any truthy DATA value. No completed m, successful Get/Set,
future tuple/brand/realm or desired call result is supplied as a public premise.
The generic error relation compares model outcomes; it does not prove native
error partial states or rollback.

The declaration grammar is restricted: single-line header, named parameters
with retained old TypeSyntax, optional markers and return annotation. Duplicate
names, ambient shadows, default/rest/destructured parameters, unsupported object
types, block/trailing comments and nonASCII prefix-comment text refuse. Leading
ASCII `//` comments require CR/LF termination. Refusal of a closing brace inside
an unterminated comment and LS/PS line-separator cases prevents silent code
erasure. This is a checked canonical source parse, not general frontend adequacy.

Function creation/invocation, argument binding, live lexical/global cells,
closure/module/export/bootstrap/cache lifetime and TypeScript type-system or
erasure correctness remain separate. Neither the new parser nor declarationBody
creates a function object or establishes a formal complete-getPattern theorem.

## Executable evidence

Suite 32360 passes10groups7.807s. There are384normal contexts/histories:
80 wildcard readiness combinations (three calls each),261 mixed persistent
histories,11exact-star boundary strings and32plain/safe-range profiles. The
independent oracle inserts zero-effect wildcard observations into the frozen
label/key/descriptor cache history. It never calls either executable to decide
the expected answer.

The model parses actual576B source through the frozen Driver; native Bun1.4.0
and Node22.22.2 execute the same unwrapped body with one explicit caller-owned
cache per history. Observations retain visible cache descriptors, exposed
reference identity and prior canary/metadata frames. Native hidden literal or
capture allocations and protocol records are not invented. Native initialization
is a fixture cache; actual typed52B initialization remains separately modeled.

Four supported source faults change star→@, equality→inequality, return star→!,
or remove the guard. Twelve declaration cases (two accepted, ten refused)
observe actual metadata/raw inner source/body; the repr comparison observer is
explicitly unverified, separate from the kernel's actual source parse theorem.
Two unready worlds are model-only whole-state sensors, not correspondence with
native unallocated realms.

The [native-only records](../../verification/getpattern-body/control-evidence.json)
have three Bun and two Node controls. Poisoned matching/proxy cache/constructor/
next return`*` with empty effects. A custom object label reaches its own match
without primitive coercion. The third Bun record imports the actual pinned
TypeScript module before getter poisoning and calls its real export twice;
loader/invocation/module adequacy stays unverified. Intrusive descriptors are
restored and compared exactly. No D1 allowance changes.

One explicit complete576B cold 67 case preserves native success versus model
grammar refusal, outside ordinary agreement. Earlier 49974 had a Python mixed
history variable-shadow UnboundLocalError; renaming the local loop variable
retained all261cases. Suite 28129 then passed6groups5.895s,48067 passed9groups
6.741s, and independent review requested the retained full body lookahead control
before final 32360 passed10groups. Agent early42610/88112 focused commands
overlapped accidentally but both became terminal; subsequent managed gates were
strictly sequential. A local decide/rfl normalization was repaired, with no
theorem/domain/case weakening or source/runtime change.

Prior36proof clusters/35additional slices,30 original assumption statuses and
theorem arrays,36full-routing statuses,347 old Lean modules/shared ABI, source
target/SPEC/catalog/D1/comparison/benchmarks and every old cache/terminal artifact
remain preserved. Unconditional upstream runtime claims remain empty. See the
[walkthrough](getpattern-body-walkthrough.md),
[diagram source](../diagrams/getpattern-body.excalidraw) and
[invocation plan](getpattern-invocation-plan.md).
