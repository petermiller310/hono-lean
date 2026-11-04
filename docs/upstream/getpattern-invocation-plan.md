# Next: derive body entry from a real closure call

The complete576B body now has wildcard/nonstar source contracts and lifted
independent cache contracts. The actual744B arrow declaration is parsed with
parameters/types/comments/body retained. Calling its body with prebound variables
does not yet model actual function creation, invocation or module initialization.

1. Model lexical binding cells/environments and an arrow closure holding an
   environment reference. Retain actual source 50's initialized cache reference
   and source 51's parsed arrow. Do not capture a copied cache/map or snapshot
   current global RegExp values at definition time.
2. Execute initialization and declaration to derive the shared cache cell and
   exported callable. Link callable identity to its actual function object and
   arrow payload. Record relevant name/length/prototype/nonconstructibility
   properties rather than assigning a desired function result.
3. Derive label/next cells from actual supplied argument values, binding missing
   next to undefined. Preserve shadowing, caller environment and arrow lexical
   this. Extra arguments, argument-expression order, TDZ and abrupt completions
   need explicit admitted semantics or visible remaining boundaries.
4. Project live lexical/global lookup into the existing body evaluator with a
   checked relation. Current RegExp must be read at its evaluation point; a
   user callback can change a global before a later read. A before-entry value
   snapshot is only adequate for profiles whose preservation has been proved.
5. Compose creation→call→return for wildcard and admitted normal cache profiles,
   deriving body readiness from initial caller/realm/cell facts. Then call the
   same exported closure twice and prove shared cache/tuple identity, including
   a raw-key collision. No completed body evaluation, future cache lookup or
   successful invocation may be a public premise.
6. Retain caller and heap effects on throw explicitly. The current model's
   Except result does not establish partial error state or rollback; do not
   turn it into a broad native exception theorem. General getters/proxies,
   closures/global objects, TypeScript frontend and native module/host adequacy
   remain required work until genuinely connected.

Existing wildcard-body and safe-range claims remain distinct from general
lookahead/regex semantics. After the closure boundary, implement actual 67 and
remaining regex behavior, then actual tuple installation, query preparation,
complete traversal/all routers, framework dispatch/handlers/async/request/context
and the remaining published runtime catalog. Preserve all original proof/status/
assumption/source/benchmark/counterexample evidence, use focused agents and
independent review, actual source/fault/native checks, warnings-as-errors,
fresh replay/axiom audits and an editable exported diagram.
