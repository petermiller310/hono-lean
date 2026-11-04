import HonoLean.Upstream.SourceSubset.ArrayBindingRules

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace HonoLean.Upstream.SourceSubset.ArrayBindingChecks
open ECMA2025

private def oldContext : RegExpConstructContext :=
  ⟨⟨1, [⟨⟨"old", [], .named "void", []⟩, [], []⟩]⟩,
   ⟨2, [⟨⟨"old", "input", []⟩, [], []⟩]⟩,
   ⟨3, [⟨⟨"echo", "input", [.ret (.variable "input")]⟩, [], []⟩,
        ⟨⟨"other", "input", [.ret .null]⟩, [], []⟩]⟩,
   ⟨5, [.regexpExec]⟩, ⟨6, [⟨1⟩]⟩⟩
private def context : ArrayIteratorContext := ⟨oldContext, ⟨7, [.arrayValues, .arrayNext]⟩, 2, 4, 0⟩
private def sourceText := "          const [, name, matcher] = pattern\n"
private def declaration : ArrayBindingDecl := ⟨[.elision, .binding "name", .binding "matcher"], .variable "pattern"⟩
private def prior : JSString := [112, 114, 105, 111, 114]
private def name : JSString := [110, 97, 109, 101]
private def tuple : List Value := [.string [58, 110], .string name, .object 6]
private def before (values : List Value := tuple) : ArrayBindingState :=
  {regexp := {
    ambient := {
      environment := [("pattern", .array 1), ("alternate", .array 2), ("name", .object 5), ("matcher", .object 5)]
      heap := [[.string prior], values, [.number 17]]
      objects := [objectPrototypeProjection,
        ⟨[([101, 120, 101, 99], .data (.function 5) true false true)], some 0, true⟩,
        ⟨[], some 0, true⟩, ⟨[], some 0, true⟩,
        ⟨[(iteratorNextKey, .data (.function 8) true false true)], some 3, true⟩,
        emptyNullObject, initializedRegExpObject 1]
      functions := [⟨⟨"old", .number 0⟩, []⟩]
      thisValue := .object 5
      privates := .ofData [("caller", 9)] [(5, [(9, .number 17)])]
      sets := [[name]]}
    brands := [(6, digitsRecord)]
    results := [(0, ⟨0, prior⟩)]}
   symbols := [(.object 2, [(.iterator, .data (.function 7) true false true)])]}

private def stepCount (state : ArrayBindingState) : Nat := state.trace.countP (fun event => match event with | .resultAllocated _ _ _ => true | _ => false)
private def valueCount (state : ArrayBindingState) : Nat := state.trace.countP (fun event => match event with | .valueGet _ _ => true | _ => false)
private def closeCount (state : ArrayBindingState) : Nat := state.trace.countP (fun event => match event with | .returnGet _ _ => true | _ => false)
private def observe (result : Except ArrayBindingError (ArrayIteratorRecord × ArrayBindingState)) :=
  result.map (fun (record, state) => (record, state.regexp.ambient.environment, state.regexp.ambient.heap,
    state.iterators.lookup 7, stepCount state, valueCount state, closeCount state,
    state.regexp.brands, state.regexp.results, state.regexp.ambient.privates, state.regexp.ambient.thisValue))
private def firstRecord : ArrayIteratorRecord := ⟨7, .function 8, false⟩

/-- Actual const/ArrayBindingPattern/elision/RHS retained, not three index reads. -/
theorem parses_exact_source_and_preserves_trailing_comma_semantics :
    parseArrayBinding sourceText ["pattern"] = some declaration ∧
    (parseArrayBinding "const [name,] = pattern" ["pattern"]).map ArrayBindingDecl.elements = some [.binding "name"] ∧
    (parseArrayBinding "const [,,name] = pattern" ["pattern"]).map ArrayBindingDecl.elements =
      some [.elision, .elision, .binding "name"] := by cbv

/-- TDZ self/head names, duplicate/reserved binders and callback RHS reject. -/
theorem rejects_tdz_duplicates_callbacks_and_unsupported_patterns :
    (["const [name] = name", "const [name,name] = pattern", "const [eval] = pattern",
      "const [arguments] = pattern", "const [name = 0] = pattern", "const [...name] = pattern",
      "const [[name]] = pattern", "let [,name] = pattern", "const [,name] = f()",
      "const [,name] = pattern garbage", "const [,name] = ++pattern"] |>.all
      (fun text => (parseArrayBinding text ["pattern", "name", "f"]).isNone)) = true := by cbv

/-- Universal opaque tuple DATA. New bindings shadow while preserving the
entire caller tail; three results, two value Gets and one Close, never a fourth
next. A native embedding must additionally allocate any opaque reference Values. -/
theorem arbitrary_dense_tuple_binds_current_values (labelValue nameValue matcherValue : Value) :
    observe (runArrayBinding 8 defaultSplitLimit context declaration (before [labelValue, nameValue, matcherValue])) =
      .ok (firstRecord,
        ("matcher", matcherValue) :: ("name", nameValue) :: (before [labelValue, nameValue, matcherValue]).regexp.ambient.environment,
        (before [labelValue, nameValue, matcherValue]).regexp.ambient.heap,
        some ⟨some 1, 3⟩, 3, 2, 1, before.regexp.brands, before.regexp.results,
        before.regexp.ambient.privates, .object 5) := by cbv

/-- Genuine parsed execution includes index0 Get but NOT result0.value Get.
ENGINE-ELISION-1 is a custom accessor boundary outside these default DATA cells. -/
theorem parsed_elision_uses_step_without_result_value_get :
    (parseArrayBinding sourceText ["pattern"]).map (fun program =>
      (runArrayBinding 8 defaultSplitLimit context program before).map (fun (record, after) =>
        (record.done, after.trace.contains (.elementGet 1 0 (.string [58, 110])),
         after.trace.contains (.valueGet 8 (.string [58, 110])), stepCount after, valueCount after,
         after.regexp.ambient.objects.length))) =
      some (.ok (false, true, false, 3, 2, 11)) := by cbv

/-- Exhaustion is tested once, then later bindings get undefined without any
additional next/result allocation or Close. A one-entry tuple takes two nexts. -/
theorem empty_and_short_exhaustion :
    (runArrayBinding 8 defaultSplitLimit context declaration (before [])).map (fun (record, after) =>
      (record.done, after.regexp.ambient.environment.take 2, stepCount after, valueCount after, closeCount after, after.iterators.lookup 7)) =
      .ok (true, [("matcher", .undefined), ("name", .undefined)], 1, 0, 0, some ⟨none, 0⟩) ∧
    (runArrayBinding 8 defaultSplitLimit context declaration (before [.number 0])).map (fun (record, after) =>
      (record.done, after.regexp.ambient.environment.take 2, stepCount after, valueCount after, closeCount after, after.iterators.lookup 7)) =
      .ok (true, [("matcher", .undefined), ("name", .undefined)], 2, 0, 0, some ⟨none, 1⟩) := by cbv

/-- Array reference is retained, not a creation-time elements snapshot. A
current old cell replacement is observed on the second next. -/
theorem next_reads_current_heap_after_first_yield :
    (getArrayIterator context (.array 1) before).bind (fun (record, state) => do
      let (_, _, state) ← iteratorStep context record state
      let state := {state with regexp := {state.regexp with ambient := {state.regexp.ambient with
        heap := state.regexp.ambient.heap.set 1 [.number 10, .number 42, .object 6]}}}
      let (value, _, after) ← iteratorStepValue context record state
      pure (value, after.iterators.lookup 7)) = .ok (.number 42, some ⟨some 1, 2⟩) := by cbv

/-- Changing the current next property after acquisition does not change the
saved next method. A subsequent new iterator sees the replacement instead. -/
theorem saved_next_identity_survives_current_property_replacement :
    (getArrayIterator context (.array 1) before).bind (fun (record, state) => do
      let object := newDataObject (arrayIteratorObject 4) iteratorNextKey (.number 17)
      let state := {state with regexp := {state.regexp with ambient := {state.regexp.ambient with
        objects := state.regexp.ambient.objects.set 7 object}}}
      let (value, _, after) ← iteratorStepValue context record state
      pure (value, after.iterators.lookup 7)) = .ok (.string [58, 110], some ⟨some 1, 1⟩) := by cbv

/-- The full current return chain reaches IteratorPrototype, so adding a
non-nullish DATA return there is detected. null remains GetMethod-absent. -/
theorem close_reads_late_full_prototype_chain_without_done_flip :
    (getArrayIterator context (.array 1) before).bind (fun (record, state) =>
      let state := {state with regexp := {state.regexp with ambient := {state.regexp.ambient with
        objects := state.regexp.ambient.objects.set 3 (newDataObject ⟨[], some 0, true⟩ iteratorReturnKey (.function 3))}}}
      closeArrayIterator record state) = .error .returnDomain ∧
    (getArrayIterator context (.array 1) before).bind (fun (record, state) => do
      let state := {state with regexp := {state.regexp with ambient := {state.regexp.ambient with
        objects := state.regexp.ambient.objects.set 3 (newDataObject ⟨[], some 0, true⟩ iteratorReturnKey .null)}}}
      let after ← closeArrayIterator record state
      pure (record.done, after.iterators.lookup 7, closeCount after)) = .ok (false, some ⟨some 1, 0⟩, 1) := by cbv

/-- Cursor completion persists even if its original array later grows. Direct
next still allocates a done result, but performs no new length/index Get. -/
theorem completed_iterator_cannot_revive_after_append :
    (getArrayIterator context (.array 1) (before [])).bind (fun (record, state) => do
      let (_, _, state) ← iteratorStep context record state
      let state := {state with regexp := {state.regexp with ambient := {state.regexp.ambient with
        heap := state.regexp.ambient.heap.set 1 tuple}}}
      let (result, after) ← arrayIteratorNext context record.iterator state
      let value ← iteratorValue result after
      pure (value.1, after.iterators.lookup 7,
        after.trace.countP (fun event => match event with | .lengthGet _ _ => true | _ => false))) =
      .ok (.undefined, some ⟨none, 0⟩, 1) := by cbv

/-- Symbol keys are typed: a string property cannot override the protocol.
An actual typed own override to another function is a model-domain refusal. -/
theorem typed_symbol_override_and_saved_noncallable_next_boundaries :
    getArrayIterator context (.array 1) {before with symbols :=
      (.array 1, [(.iterator, .data (.function 3) true true true)]) :: before.symbols} = .error .iteratorDomain ∧
    (getArrayIterator context (.array 1) {before with regexp := {before.regexp with ambient := {before.regexp.ambient with
      objects := before.regexp.ambient.objects.set 4 (newDataObject ⟨[], some 3, true⟩ iteratorNextKey (.number 17))}}}).bind
      (fun (record, state) => iteratorStep context record state) = .error .iteratorDomain := by cbv

/-- Actual projected iterator/result cells have ordinary prototypes and DATA
value/done properties; source arrays/regex metadata/private context stay framed. -/
theorem allocated_objects_and_nonallocation_frames :
    (runArrayBinding 8 defaultSplitLimit context declaration before).map (fun (_, after) =>
      (after.regexp.ambient.objects.drop 7, after.regexp.ambient.functions.length,
       after.regexp.ambient.sets, after.regexp.ambient.thisValue, after.symbols)) =
      .ok ([arrayIteratorObject 4,
        iteratorResultObject 0 (.string [58, 110]) false,
        iteratorResultObject 0 (.string name) false,
        iteratorResultObject 0 (.object 6) false], 1, before.regexp.ambient.sets, .object 5, before.symbols) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.iterator_lookup_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iterator_lookup_append
/-- info: 'HonoLean.Upstream.SourceSubset.symbolOwn_fresh_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms symbolOwn_fresh_array
/-- info: 'HonoLean.Upstream.SourceSubset.getArrayIterator_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms getArrayIterator_standard
/-- info: 'HonoLean.Upstream.SourceSubset.arrayIteratorNext_yield' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrayIteratorNext_yield
/-- info: 'HonoLean.Upstream.SourceSubset.closeArrayIterator_nullish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closeArrayIterator_nullish
/-- info: 'HonoLean.Upstream.SourceSubset.ArrayBindingChecks.arbitrary_dense_tuple_binds_current_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms arbitrary_dense_tuple_binds_current_values

end HonoLean.Upstream.SourceSubset.ArrayBindingChecks
