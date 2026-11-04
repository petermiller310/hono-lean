import HonoLean.Upstream.PatternConstruct.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.PatternConstruct
open SourceSubset ECMA2025

theorem tables_separated (before : RegExpCallState) (context : RegExpConstructContext) (label name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context label name matched handle values lower upper constructor prototypeObject) :
    constructorTablesSeparated context before.ambient = true := by
  simp [constructorTablesSeparated, inputs.noArgBefore, inputs.methodsBefore, inputs.functionsBefore, inputs.membersBefore, inputs.builtinsBefore]

theorem inputs_tupleStage (before : RegExpCallState) (context : RegExpConstructContext) (label name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (contents : List Value) (inputs : Inputs before context label name matched handle values lower upper constructor prototypeObject) :
    Inputs (tupleStage before contents) context label name matched handle values lower upper constructor prototypeObject := by
  refine ⟨inputs.labelBinding, inputs.matchBinding, ?_, inputs.nameFound, inputs.bodyFound, inputs.lengthBound,
    inputs.lowerSafe, inputs.upperSafe, inputs.ordered, inputs.constructorBinding, inputs.noArgBefore, inputs.methodsBefore,
    inputs.functionsBefore, inputs.membersBefore, inputs.builtinsBefore, inputs.handleBound, inputs.identity, inputs.prototypeFound⟩
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp inputs.matchedFound).1).trans inputs.matchedFound

theorem eval_index (extra : Nat) (before : RegExpCallState) (matched index : Nat) (values : List Value) (value : Value)
    (binding : before.ambient.environment.lookup "match" = some (.array matched))
    (found : before.ambient.heap[matched]? = some values) (atIndex : values[index]? = some value) :
    evalExpression (extra + 4) defaultSplitLimit (.index (.variable "match") (.number index)) before.ambient = .ok (value, before.ambient) := by
  simp [evalExpression, lookupVariable, binding, readProperty, found, atIndex, bind, Except.bind, pure, Except.pure]

theorem append_tuple_stage (before : RegExpCallState) (contents : List Value) (value : Value) :
    appendConstructElement before.ambient.heap.length value (tupleStage before contents) =
      .ok (tupleStage before (contents ++ [value])) := by
  simp [appendConstructElement, appendLiteralElements, tupleStage, List.set_append_right, Except.mapError, Except.map]

theorem eval_template (extra : Nat) (before : RegExpCallState) (context : RegExpConstructContext) (label name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context label name matched handle values lower upper constructor prototypeObject) :
    evalRegExpConstruct (extra + 11) defaultSplitLimit context templateExpr before = .ok (.string (assembledSource lower upper), before) := by
  have body := eval_index (extra + 6) before matched 2 values (.string (rawBody lower upper)) inputs.matchBinding inputs.matchedFound inputs.bodyFound
  have substituted := evalRegExpConstruct_template (extra + 10) defaultSplitLimit context [94] [36] (rawBody lower upper) bodyExpr before before.ambient body
  simpa [templateExpr, assembledSource] using substituted

theorem eval_constructor (extra : Nat) (before : RegExpCallState) (context : RegExpConstructContext) (label name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context label name matched handle values lower upper constructor prototypeObject) :
    evalRegExpConstruct (extra + 12) defaultSplitLimit context constructorExpr before =
      .ok (.object before.ambient.objects.length, regExpConstructedState before constructor.prototype (constructedRangeRecord lower upper)) := by
  have callee : evalExpression (extra + 11) defaultSplitLimit (.variable "RegExp") before.ambient = .ok (.function handle, before.ambient) := by
    simp [evalExpression, lookupVariable, inputs.constructorBinding]
    rfl
  have substituted := eval_template extra before context label name matched handle values lower upper constructor prototypeObject inputs
  have saved := evalRegExpConstruct_saved (extra + 11) defaultSplitLimit context (.variable "RegExp") templateExpr before before (.function handle)
    (.string (assembledSource lower upper)) before.ambient callee substituted
  have identity : constructorAt context.constructors (.function handle) = some constructor := by
    simp [constructorAt, inputs.handleBound, inputs.identity]
  have invoked := invokeRegExpConstructor_range context (.function handle) before constructor prototypeObject lower upper
    (tables_separated before context label name matched handle values lower upper constructor prototypeObject inputs) identity inputs.prototypeFound inputs.lowerSafe inputs.upperSafe inputs.ordered
  exact saved.trans invoked

theorem construction_phases (extra : Nat) (before : RegExpCallState) (context : RegExpConstructContext) (label name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context label name matched handle values lower upper constructor prototypeObject) :
    ConstructionPhases extra before context label name handle lower upper constructor.prototype := by
  have stage1 := inputs_tupleStage before context label name matched handle values lower upper constructor prototypeObject [.string label] inputs
  have stage2 := inputs_tupleStage before context label name matched handle values lower upper constructor prototypeObject [.string label, .string name] inputs
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [evalExpression, labelExpr, lookupVariable, inputs.labelBinding, tupleStage]
    rfl
  · exact eval_index (extra + 8) _ matched 1 values (.string name) stage1.matchBinding stage1.matchedFound stage1.nameFound
  · simp [evalExpression, lookupVariable, inputs.constructorBinding, tupleStage]
    rfl
  · exact eval_template extra _ context label name matched handle values lower upper constructor prototypeObject stage2
  · exact (regExpAllocate_descriptor (tupleStage before [.string label, .string name]) constructor.prototype).1
  · exact initializeAllocatedRegExp_range (tupleStage before [.string label, .string name]) constructor.prototype lower upper inputs.lowerSafe inputs.upperSafe inputs.ordered

theorem evaluate_source (extra : Nat) (before : RegExpCallState) (context : RegExpConstructContext) (label name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context label name matched handle values lower upper constructor prototypeObject) :
    evalRegExpConstruct (extra + 16) defaultSplitLimit context program before =
      .ok (.array before.ambient.heap.length, resultState before constructor.prototype lower upper label name) := by
  have labelRead := (construction_phases extra before context label name matched handle values lower upper constructor prototypeObject inputs).labelRead
  have nameRead := (construction_phases extra before context label name matched handle values lower upper constructor prototypeObject inputs).nameRead
  have stage2 := inputs_tupleStage before context label name matched handle values lower upper constructor prototypeObject [.string label, .string name] inputs
  have created := eval_constructor extra _ context label name matched handle values lower upper constructor prototypeObject stage2
  have labelLeaf : evalRegExpConstruct (extra + 14) defaultSplitLimit context (.ordinary labelExpr) (tupleStage before []) = .ok (.string label, tupleStage before []) := by
    simp only [evalRegExpConstruct, labelRead, Except.mapError, Except.map]
  have nameLeaf : evalRegExpConstruct (extra + 13) defaultSplitLimit context (.ordinary nameExpr) (tupleStage before [.string label]) = .ok (.string name, tupleStage before [.string label]) := by
    simp only [evalRegExpConstruct, nameRead, Except.mapError, Except.map]
  have third := append_tuple_stage (regExpConstructedState before constructor.prototype (constructedRangeRecord lower upper)) [.string label, .string name] (.object before.ambient.objects.length)
  change (do
    let after ← evalRegExpConstructElements (extra + 15) defaultSplitLimit context before.ambient.heap.length
      [.ordinary labelExpr, .ordinary nameExpr, constructorExpr] (tupleStage before [])
    pure (Value.array before.ambient.heap.length, after)) = _
  rw [evalRegExpConstructElements, labelLeaf]
  dsimp only [bind, Except.bind]
  rw [append_tuple_stage]
  dsimp only [bind, Except.bind]
  simp only [List.nil_append]
  rw [evalRegExpConstructElements, nameLeaf]
  dsimp only [bind, Except.bind]
  rw [append_tuple_stage]
  dsimp only [bind, Except.bind]
  simp only [List.cons_append, List.nil_append]
  rw [evalRegExpConstructElements, created]
  dsimp only [bind, Except.bind]
  have thirdCanonical : appendConstructElement before.ambient.heap.length (.object before.ambient.objects.length)
      (regExpConstructedState (tupleStage before [.string label, .string name]) constructor.prototype (constructedRangeRecord lower upper)) =
      .ok (resultState before constructor.prototype lower upper label name) := by
    simpa only [regExpConstructedState, tupleStage, resultState, tupleValues, List.cons_append, List.nil_append] using third
  have objectLength : (tupleStage before [.string label, .string name]).ambient.objects.length = before.ambient.objects.length := rfl
  rw [objectLength, thirdCanonical]
  rfl

theorem result_contract (before : RegExpCallState) (label name : JSString) (prototype : Nat) (lower upper : UInt16) :
    Contract before (resultState before prototype lower upper label name) (.array before.ambient.heap.length) label name prototype lower upper := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [resultState, regExpConstructedState, tupleStage]
  · simp [resultState, regExpConstructedState, tupleStage]
  · simp [resultState, regExpConstructedState, tupleStage]
  · simp [resultState, regExpConstructedState, tupleStage]
  · simp [resultState, regExpConstructedState, tupleStage]
  · intro reference bound
    exact List.getElem?_append_left bound
  · intro reference bound
    exact List.getElem?_append_left bound
  · intro reference different
    have unequal : (reference == before.ambient.objects.length) = false := beq_false_of_ne different
    simp only [resultState, regExpConstructedState, tupleStage, List.lookup_cons, unequal]

/-- Universal arbitrary safe ordered range endpoints. The actual46B expression
creates both identities, with source/compiled record and phase order derived
from the BEFORE strings and actual dense match slots. -/
theorem source_construct_satisfies (extra : Nat) (before : RegExpCallState) (context : RegExpConstructContext) (label name : JSString)
    (matched handle : Nat) (values : List Value) (lower upper : UInt16) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context label name matched handle values lower upper constructor prototypeObject) :
    sourceConstruct (extra + 16) context before = some (.ok (.array before.ambient.heap.length, resultState before constructor.prototype lower upper label name)) ∧
    Contract before (resultState before constructor.prototype lower upper label name) (.array before.ambient.heap.length) label name constructor.prototype lower upper ∧
    ConstructionPhases extra before context label name handle lower upper constructor.prototype := by
  exact ⟨by simpa [sourceConstruct, parses_source] using congrArg some (evaluate_source extra before context label name matched handle values lower upper constructor prototypeObject inputs),
    result_contract before label name constructor.prototype lower upper, construction_phases extra before context label name matched handle values lower upper constructor prototypeObject inputs⟩

/-- info: 'HonoLean.Upstream.PatternConstruct.source_construct_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_construct_satisfies
/-- info: 'HonoLean.Upstream.PatternConstruct.construction_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms construction_phases
/-- info: 'HonoLean.Upstream.PatternConstruct.evaluate_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evaluate_source

end HonoLean.Upstream.PatternConstruct
