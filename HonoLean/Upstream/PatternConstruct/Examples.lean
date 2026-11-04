import HonoLean.Upstream.PatternConstruct.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.PatternConstruct.Examples
open SourceSubset ECMA2025
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def priorText : JSString := [112, 114, 105, 111, 114]
private def oldPrivate : PrivateMethodClosure := ⟨⟨"old", [], .named "void", []⟩, [], []⟩
private def oldFunction : StringFunctionClosure := ⟨⟨"old", "input", []⟩, [], []⟩
private def ordinary : MemberClosure := ⟨⟨"exec", "input", [.ret (.variable "input")]⟩, [], []⟩
private def prototypeObject : OrdinaryObject :=
  ⟨[(NodeExecKey, .data (.function 5) true false true)], some 0, true⟩
where NodeExecKey : JSString := [101, 120, 101, 99]
private def context : RegExpConstructContext :=
  ⟨⟨1, [oldPrivate]⟩, ⟨2, [oldFunction]⟩, ⟨3, [ordinary, ordinary]⟩,
    ⟨5, [.regexpExec]⟩, ⟨6, [⟨2⟩]⟩⟩

/-- Supplied old realm/callable/array graph; the standard constructor identity,
prototype and newTarget interpretation are explicit inputs, not native bootstrap
proofs. Old regex3/result0 are unrelated prior state and must remain unchanged. -/
private def before (label name : JSString) (lower upper : UInt16) : RegExpCallState :=
  {ambient := {
      environment := [("label", .string label), ("match", .array 1), ("RegExp", .function 6), ("frame", .string priorText)]
      objects := [objectPrototypeProjection [], emptyNullObject, prototypeObject, initializedRegExpObject 2]
      heap := [[.string priorText], [.string label, .string name, .string (rawBody lower upper)]]
      functions := [⟨⟨"old", .number 0⟩, []⟩]
      sets := [[priorText]]
      thisValue := .object 1
      privates := PrivateStore.ofData [("caller", 7)] [(1, [(7, .array 0)])] }
   brands := [(3, digitsRecord)]
   results := [(0, ⟨0, priorText⟩)]}

private theorem inputs (label name : JSString) (lower upper : UInt16)
    (lowerSafe : RangeRegExp.SafeEndpoint lower) (upperSafe : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) :
    Inputs (before label name lower upper) context label name 1 6 [.string label, .string name, .string (rawBody lower upper)] lower upper ⟨2⟩ prototypeObject :=
  ⟨rfl, rfl, rfl, rfl, rfl, by change 3 ≤ 4294967295; decide, lowerSafe, upperSafe, ordered, rfl,
    by change 1 ≤ 6; decide, by decide, by decide, by decide, by decide, by decide, rfl, rfl⟩

/-- All arbitrary safe ordered range endpoints and primitive UTF16 labels/names
have a genuine initial domain. No tuple, brand or compiled outcome is staged. -/
theorem arbitrary_safe_range_domain_has_source_contract (label name : JSString) (lower upper : UInt16)
    (lowerSafe : RangeRegExp.SafeEndpoint lower) (upperSafe : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) :
    sourceConstruct 16 context (before label name lower upper) = some (.ok (.array 2, resultState (before label name lower upper) 2 lower upper label name)) ∧
    Contract (before label name lower upper) (resultState (before label name lower upper) 2 lower upper label name) (.array 2) label name 2 lower upper ∧
    ConstructionPhases 0 (before label name lower upper) context label name 6 lower upper 2 :=
  source_construct_satisfies 0 _ context label name 1 6 _ lower upper ⟨2⟩ prototypeObject (inputs label name lower upper lowerSafe upperSafe ordered)

/-- Source construction supplies the record for direct standard builtin exec.
This says nothing about current matcher.exec or actual138 destructuring. -/
theorem produced_tuple_supplies_direct_builtin_without_brand_input (label name query : JSString) (lower upper : UInt16)
    (lowerSafe : RangeRegExp.SafeEndpoint lower) (upperSafe : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) :
    let constructed := resultState (before label name lower upper) 2 lower upper label name
    sourceConstruct 16 context (before label name lower upper) = some (.ok (.array 2, constructed)) ∧
    Contract (before label name lower upper) constructed (.array 2) label name 2 lower upper ∧
    ConstructionPhases 0 (before label name lower upper) context label name 6 lower upper 2 ∧
    invokeProducedBuiltin (.array 2) query constructed = .ok (rangeExecValue lower upper constructed query, rangeExecState lower upper constructed query) :=
  source_construct_then_direct_builtin_satisfies 0 _ context label name query 1 6 _ lower upper ⟨2⟩ prototypeObject
    (inputs label name lower upper lowerSafe upperSafe ordered)

private def constructView (label name : JSString) (lower upper : UInt16) :=
  (sourceConstruct 16 context (before label name lower upper)).map (fun outcome => outcome.map (fun (returned, after) =>
    (returned, after.ambient.heap[2]?, after.ambient.objects[4]?, after.brands.lookup 4,
      decide (after.ambient.heap.take 2 = (before label name lower upper).ambient.heap ∧
        after.ambient.objects.take 4 = (before label name lower upper).ambient.objects ∧
        after.brands.lookup 3 = some digitsRecord ∧ after.results = (before label name lower upper).results ∧
        after.ambient.environment = (before label name lower upper).ambient.environment ∧
        after.ambient.privates = (before label name lower upper).ambient.privates ∧
        after.ambient.thisValue = (before label name lower upper).ambient.thisValue ∧
        after.ambient.sets = (before label name lower upper).ambient.sets))))

theorem digit_tuple_is_fresh_and_old_graph_is_framed :
    constructView [58, 105, 100] [105, 100] 48 57 = some (.ok (.array 2,
      some [.string [58, 105, 100], .string [105, 100], .object 4], some (initializedRegExpObject 2),
      some (constructedRangeRecord 48 57), true)) := by
  simp only [constructView, sourceConstruct, parses_source, Option.map_some]
  cbv

theorem utf16_label_and_name_are_retained_without_coercion :
    constructView [0xd800, 47, 0xdc00] [945, 0xd83d, 0xde00] 65 122 = some (.ok (.array 2,
      some [.string [0xd800, 47, 0xdc00], .string [945, 0xd83d, 0xde00], .object 4], some (initializedRegExpObject 2),
      some (constructedRangeRecord 65 122), true)) := by
  simp only [constructView, sourceConstruct, parses_source, Option.map_some]
  cbv

/-- Actual27B constructor is also parsed/executed. The undefined descriptor
phase is observable in ConstructionPhases; no tuple ArrayCreate occurs here. -/
theorem constructor_subexpression_initializes_without_tuple_allocation :
    (sourceConstructor 16 context (before [] [] 48 57)).map (fun outcome => outcome.map (fun (returned, after) =>
      (returned, after.ambient.heap.length, after.ambient.objects[4]?, after.brands.lookup 4))) =
      some (.ok (.object 4, 2, some (initializedRegExpObject 2), some (constructedRangeRecord 48 57))) := by
  simp only [sourceConstructor, parses_constructor, Option.map_some]
  cbv

private def directView (lower upper : UInt16) (query : JSString) := do
  let outcome ← sourceConstruct 16 context (before [58, 114] [114] lower upper)
  pure do
    let (returned, constructed) ← outcome.mapError (fun _ => RegExpCallError.representation)
    let (returned, after) ← invokeProducedBuiltin returned query constructed
    pure (returned, after.ambient.heap[3]?, observeRegExpResult after 3 .groups,
      (after.ambient.objects[4]?).bind (fun object => object.own.lookup lastIndexKey))

theorem inclusive_range_keeps_punctuation_inside_alphanumeric_endpoints :
    directView 65 122 [91, 92, 93, 94, 95, 96] = some (.ok (.array 3,
      some [.string [91, 92, 93, 94, 95, 96]], some (.data .undefined true true true), some (.data (.number 0) true false false))) := by
  simp only [directView, sourceConstruct, parses_source, Option.map_some]
  cbv

theorem digit_execution_comes_from_constructed_tuple :
    directView 48 57 [49, 50] = some (.ok (.array 3, some [.string [49, 50]],
      some (.data .undefined true true true), some (.data (.number 0) true false false))) ∧
    directView 48 57 [49, 10] = some (.ok (.null, none, none, some (.data (.number 0) true false false))) := by
  constructor <;> simp only [directView, sourceConstruct, parses_source, Option.map_some] <;> cbv

/-- A replaced constructor identifier is NOT selected by its variable spelling.
This is a model admission result, not a claim that all native custom constructors
throw. Array/argument errors carry no partial-state/rollback guarantee. -/
theorem changed_constructor_identity_is_not_name_dispatch :
    sourceConstruct 16 context {(before [] [] 48 57) with ambient := {(before [] [] 48 57).ambient with
      environment := [("label", .string []), ("match", .array 1), ("RegExp", .function 5)]}} = some (.error .constructorDomain) := by
  simp only [sourceConstruct, parses_source, Option.map_some]
  cbv

end HonoLean.Upstream.PatternConstruct.Examples
