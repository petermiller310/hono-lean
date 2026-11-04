# Retained plan: bind the wildcard guard and function boundary

The [body walkthrough](getpattern-body-walkthrough.md) and
[audit](getpattern-body-audit.md) now cover the actual wildcard guard, complete
body and structural arrow syntax described below. Function creation/invocation,
lexical environment and module activation remain separate source obligations;
the [next invocation plan](getpattern-invocation-plan.md) states them concretely.
The original plan is retained for reviewing this boundary.

At fixed revision `5ca49b0720755c585c9a9835f0a479ceea36fb52`, retain the actual
guard 56–58 and complete body 56–77. Parse the real wildcard condition and return,
then compose the retained post-wildcard body. No fabricated empty branches,
copied headers around translated statements or assumed guard result.

| Retained source | Bytes and half-open offsets | SHA-256 |
| --- | --- | --- |
| Guard 56–58 |42, `[1344,1386)`|`734404478b6c51421deb9724609c9a67cadbebd27628c0ca4906bb3db5a9ce8f`|
| Body 56–77 |576, `[1344,1920)`|`f72f8a61edff659809d83048b3b8861b2baf00885682c86943e4e55fdedc7419`|
| Arrow declaration 51–79 |744, `[1179,1923)`|`1b018616846cebc56098792f451ad6243d9a3c08f17f80abf95b2df95bc4423c`|

A read-only capability probe confirms that the existing parser accepts the
complete576B body. With only the `label = '*'` binding and no allocated
objects/arrays, execution returns `*` and retains zero allocations. This is a
planning example, not the required general wildcard theorem or function proof.

The wildcard contract needs only the current exact primitive `*` label binding:
return `*`, preserve the entire state and skip label.match, cache, next and
constructor reads. It must work without their readiness facts. Non-wildcard
contracts derive passage to actual 60, then retain the applicable existing
miss/warm/plain/terminal independent contracts and their actual domains. Keep
reached 67 lookahead refusal visible. Add source faults that alter the wildcard
comparison/return and checks that invalid cold bindings are skipped.

Also pin and parse the actual exported arrow declaration 51–79, including its
parameter/type syntax and complete body. Distinguish checked declaration/body
syntax from function-object creation, invocation and lexical semantics. Do not
rename a body-entry proof a whole-function or module theorem.

Model the missing invocation/closure boundary next. Actual 50 creates one cache;
the exported closure must retain its reference across calls, while current
global/intrinsic bindings are resolved at the appropriate time. Capturing a
snapshot of RegExp at definition time would miss later changes. Model lexical
bindings/caller frames explicitly, derive argument-to-label/next binding, and
preserve heap aliases and exception/effect order. General TDZ, live lexical
cells, global accessors/proxies and frontend/native module adequacy remain
visible obligations until genuinely handled. No successful call or desired
function result may be an entry assumption.

After that, implement real lookahead 67 and remaining regex semantics, then
compose actual tuple installation, query preparation and complete traversal.
All routers/framework dispatch/async/request/context and the remaining pinned
published runtime catalog stay in the active full-Hono goal. Keep the source
target, original contracts/assumptions/statuses, historical proofs, counterexamples
and benchmarks; use independent review, actual source/axiom/fresh gates and an
editable exported diagram for each checkpoint.
