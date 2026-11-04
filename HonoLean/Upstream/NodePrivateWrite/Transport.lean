import HonoLean.Upstream.MethodsLoopInitial.Contract

namespace HonoLean.Upstream.NodePrivateWrite

open SourceSubset ECMA2025

theorem parameterRead_frame {before after : State} {key : JSString} {receiver value : Value}
    (objects : after.objects = before.objects)
    (read : NodeParamAssignment.ParameterRead before key receiver value) :
    NodeParamAssignment.ParameterRead after key receiver value := by
  cases read with
  | object reference value read => exact .object reference value (by simpa [objects] using read)
  | nullish receiver missing => exact .nullish receiver missing

/-- Layout admission uses public heaps, lexical bindings and helper definitions.
Changing only private storage or dynamic this cannot supply a desired result;
the same independent initial reads still establish admission. -/
theorem layout_frame {before after : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List MethodsLoopInitial.Record}
    {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (layout : MethodsLoopInitial.Layout before rows method collector keyBound records parameterReceiver nodeParams initial)
    (environment : after.environment = before.environment) (objects : after.objects = before.objects)
    (heap : after.heap = before.heap) (functions : after.functions = before.functions) :
    MethodsLoopInitial.Layout after rows method collector keyBound records parameterReceiver nodeParams initial := by
  refine {
    collectorBinding := by simpa [environment] using layout.collectorBinding
    parameterBinding := by simpa [environment] using layout.parameterBinding
    nodeBinding := by simpa [environment] using layout.nodeBinding
    allBinding := by simpa [SearchEntry.AllImportBinding, environment] using layout.allBinding
    helper := ?_
    collectorFound := by simpa [heap] using layout.collectorFound
    capacity := layout.capacity
    closed := by simpa [objects] using layout.closed
    protectedParents := by simpa [MethodsLoopInitial.Protected, objects] using layout.protectedParents
    nodeProtected := by simpa [MethodsLoopInitial.Protected, objects] using layout.nodeProtected
    parameterProtected := by simpa [MethodsLoopInitial.Protected, objects] using layout.parameterProtected
    recordsFound := ?_
    handlerParents := by simpa [MethodsLoopInitial.Protected, objects] using layout.handlerParents
    rowChoices := by simpa [MethodsLoopInitial.Protected, SearchEntry.Choice, environment, objects] using layout.rowChoices }
  · obtain ⟨reference, helperEnvironment, bound, found, standard⟩ := layout.helper
    exact ⟨reference, helperEnvironment, by simpa [environment] using bound,
      by simpa [functions] using found, standard⟩
  · intro record member
    have facts := layout.recordsFound record member
    refine {
      found := by simpa [objects] using facts.found
      possibleKeys := facts.possibleKeys
      keysFound := by simpa [heap] using facts.keysFound
      separate := facts.separate
      resettable := by simpa [objects] using facts.resettable
      unique := facts.unique
      legalKeys := facts.legalKeys
      keyBound := facts.keyBound
      reads := ?_ }
    intro key used
    obtain ⟨parameter, node⟩ := facts.reads key used
    exact ⟨parameterRead_frame objects parameter, by simpa [objects] using node⟩

/-- The existing pure parameter-read relation depends on the object heap, not
the dynamic this value. This transports structural admission, not executions. -/
theorem parameterRead_with_this {before : State} {key : JSString} {receiver value : Value}
    (read : NodeParamAssignment.ParameterRead before key receiver value) (thisValue : Value) :
    NodeParamAssignment.ParameterRead {before with thisValue} key receiver value := by
  cases read with
  | object reference value read => exact .object reference value read
  | nullish receiver missing => exact .nullish receiver missing

/-- Introducing the actual method receiver does not change the protected
heap/read layout. No method-body success, trace or final value is assumed. -/
theorem layout_with_this {origin : State} {rows : List Value} {method : JSString}
    {collector keyBound : Nat} {records : List MethodsLoopInitial.Record}
    {parameterReceiver : Value} {nodeParams : Nat} {initial : List Value}
    (layout : MethodsLoopInitial.Layout origin rows method collector keyBound records parameterReceiver nodeParams initial)
    (thisValue : Value) :
    MethodsLoopInitial.Layout {origin with thisValue} rows method collector keyBound records parameterReceiver nodeParams initial := by
  refine {
    collectorBinding := layout.collectorBinding
    parameterBinding := layout.parameterBinding
    nodeBinding := layout.nodeBinding
    allBinding := layout.allBinding
    helper := layout.helper
    collectorFound := layout.collectorFound
    capacity := layout.capacity
    closed := layout.closed
    protectedParents := layout.protectedParents
    nodeProtected := layout.nodeProtected
    parameterProtected := layout.parameterProtected
    recordsFound := ?_
    handlerParents := layout.handlerParents
    rowChoices := layout.rowChoices }
  intro record member
  have facts := layout.recordsFound record member
  refine {
    found := facts.found
    possibleKeys := facts.possibleKeys
    keysFound := facts.keysFound
    separate := facts.separate
    resettable := facts.resettable
    unique := facts.unique
    legalKeys := facts.legalKeys
    keyBound := facts.keyBound
    reads := ?_ }
  intro key used
  obtain ⟨parameter, node⟩ := facts.reads key used
  exact ⟨parameterRead_with_this parameter thisValue, node⟩

end HonoLean.Upstream.NodePrivateWrite
