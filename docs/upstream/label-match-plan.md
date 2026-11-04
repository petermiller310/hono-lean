# Label matching: original source-producer plan

The admitted source producer and selected downstream composition are now
implemented and checked. See the [walkthrough](label-match-walkthrough.md) and
[audit](label-match-audit.md) for the current guarantee and native interpretation
limits. The next bridge is [cache control](getpattern-cache-plan.md).

The original plan below records the obligations for deriving the match array
previously supplied to constructor/binding proofs. It advances the real producer
chain rather than adding an unrelated routing fragment.

## Bind the actual source

The selected source is url.ts60 at pinned Hono
`5ca49b0720755c585c9a9835f0a479ceea36fb52`:

```ts
const match = label.match(/^\:([^\{\}]+)(?:\{(.+)\})?$/)
```

The complete const line is59B `[1387,1446)`, SHA-256
`e1a741ae801aec83c5926a9d2b71e0b2a6dce9ee29406ef602a8d54a862d0207`.
The call is42B `[1403,1445)`, SHA-256
`a98a32751f6acbeab063921e57fd41e2e4bd7a27840a95f957c3ea1e823fbad8`.
The literal is29B `[1415,1444)`, SHA-256
`47817d28fa608a72aa9430717bf92373f21dec0f2b85758148b99d8d5a89ee94`.
Line 61 is the containing `if(match)` header, not this producer. Exact literal
and const/call syntax must be retained and checked against source bytes.

## Genuine capturing regex execution

Parse the literal's actual pattern units into explicit syntax, compile real
instructions, and execute a cursor/capture-span matcher with greedy choice and
backtracking. The required constructs are anchors, literals/identity escapes,
the negated brace character class, greedy plus, a noncapturing optional group,
and two captures. Do not implement a trusted match-label primitive, exact-source
to-decomposition switch or callback that supplies the desired capture array.

Prove execution against an independent decomposition relation. A match is a
colon followed by a nonempty name containing neither opening nor closing brace,
optionally followed by opening brace, a nonempty body and closing brace. Name
characters may include every line terminator; body dot characters exclude LF,
CR, LS and PS. The body may contain inner braces and must retain greedy captures.
For example `:id{a}{b}` captures body `a}{b`. Prove completeness, soundness,
capture positions/uniqueness and sufficient execution budget; exhaustion must
remain distinct from a miss. General regex/native adequacy remains open.

Successful output is one fresh length 3 capture array:
`[fullLabel, name, bodyOrUndefined]`, with `index = 0`, input and own groups undefined.
An absent optional capture has an OWN index 2 whose value is undefined, never a
hole or null. A miss returns null and allocates no capture array. The regex
literal itself is freshly allocated per execution and initialized lastIndex0;
there is no nonglobal global-match accumulator.

## Connect actual call semantics

Save CURRENT label.match before creating its regex-literal argument. A literal
uses the intrinsic RegExp constructor; a lexical binding named RegExp must not
redirect it. Then follow current typed Symbol.match dispatch, ordinary flags
lookup and current exec under an explicitly declared standard realm.

String.match gets Symbol.match before receiver ToString. RegExp@@match reads
ToString(Get(rx,'flags')) and checks nonglobal behavior before RegExpExec; do not
replace that with direct originalFlags/global facts. The standard flags getter
and relevant accessor/intrinsic/property effects need a real closed semantics
or an honest additional open interpretation boundary. Do not assume desired
flags/capture outputs or silently call the range-only exec for another program.
General override/coercion/callback/abrupt behavior stays explicit until modeled.

From primitive label and initial realm/source facts, derive actual match/null,
environment binding, fresh identities, metadata and old-state frames. For a
label built as colon + name + braces + safe range body, derive the existing
PatternConstruct.Inputs from the produced array's actual index1/2 contents.
Then compose construction, actual 138 binding and digit 156 where supported.
Cache choice, private installation, query production and full search are still
separate source links; do not pretend these selected activations prove them.

## Evidence

Kernel examples and independent generated/native/fault checks should include:

- `:id` with OWN2 undefined; `:id{}` and `:{a}` misses.
- Greedy inner braces, empty names, NUL/lone-surrogate/line-terminator names,
  and line terminators in body causing a miss.
- Raw labels and unescaped/ungrouped body text; no sanitization or repairs.
- Current method and Symbol.match/exec/flags order, with native-only overridden
  getter/callback probes kept distinct from the normal formal domain.
- Actual parsed quantifier/capture/optional/prefix mutations against an
  independent language/capture oracle, not mutations of a supplied match fixture.
- Tagged undefined/own-property observations; JSON arrays alone turn undefined
  into null and are inadequate evidence.

Preserve all prior source clusters, fixed target/SPEC/D1, historical benchmarks
and the exact ENGINE-ELISION-1 native records. The whole runtime goal stays open.
