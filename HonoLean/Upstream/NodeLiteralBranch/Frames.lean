import HonoLean.Upstream.NodeLiteralBranch.Contract

namespace HonoLean.Upstream.NodeLiteralBranch

open SourceSubset ECMA2025

theorem privateGet_growth {before after : State} (receiver : Nat) (spelling : String) (value : Value)
    (storage : after.privates = before.privates)
    (bound : before.objects.length ≤ after.objects.length)
    (read : privateGet (.object receiver) spelling before = .ok value) :
    privateGet (.object receiver) spelling after = .ok value := by
  cases scope : before.privates.names.lookup spelling with
  | none => simp [privateGet, scope, bind, Except.bind] at read
  | some identity =>
    cases found : before.objects[receiver]? with
    | none => simp [privateGet, scope, found, bind, Except.bind] at read
    | some object =>
      have inside : receiver < after.objects.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 bound
      have currentFound : after.objects[receiver]? = some after.objects[receiver] :=
        List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
      simpa [privateGet, storage, scope, found, currentFound] using read

theorem processed_extra_frames {origin before : State} {rows : List Value} {method : JSString}
    {collector count : Nat} {selected : List ObjectRef}
    (trace : MethodsLoop.Processed origin rows method collector count before selected) :
    before.thisValue = origin.thisValue ∧ before.functions = origin.functions ∧ before.sets = origin.sets := by
  induction trace with
  | start => exact ⟨rfl, rfl, rfl⟩
  | skip _ _ _ _ ih => exact ih
  | @capture _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ contract ih =>
    obtain ⟨output, captured, rfl⟩ := contract
    exact ih

theorem call_frames {before origin after : State} {rows : List Value} {method : JSString}
    {collector : Nat}
    (contract : NodePrivateCall.CallContract before origin rows method collector .undefined after)
    (originHeap : origin.heap = before.heap)
    (originObjects : origin.objects = before.objects)
    (originFunctions : origin.functions = before.functions)
    (originSets : origin.sets = before.sets)
    (originElements : origin.privates.elements = before.privates.elements) :
    after.environment = before.environment ∧ after.thisValue = before.thisValue ∧
    after.privates = before.privates ∧ after.functions = before.functions ∧ after.sets = before.sets ∧
    before.objects.length ≤ after.objects.length ∧
    ∀ reference, reference ≠ collector → after.heap[reference]? = before.heap[reference]? := by
  obtain ⟨_, bodyAfter, ⟨completed, selected, trace, rfl⟩, rfl⟩ := contract
  have frames := MethodsLoop.processed_frames (methods := collector + 1) trace (by omega)
  have extra := processed_extra_frames trace
  refine ⟨rfl, rfl, ?_, extra.2.1.trans originFunctions, extra.2.2.trans originSets, ?_, ?_⟩
  · cases before
    simp only [restoreMethodCaller]
    simp only [frames.1, originElements]
  · simpa only [restoreMethodCaller, originObjects] using frames.2.2
  · intro reference different
    have frames := MethodsLoop.processed_frames (methods := reference) trace (Ne.symm different)
    exact frames.2.1.trans (congrArg (fun heap => heap[reference]?) originHeap)

theorem callable_after_call {before after : State} {table : PrivateMethodTable}
    {closure : PrivateMethodClosure} {receiver handle : Nat}
    (callable : NodePrivateCall.Callable before table closure receiver handle)
    (privates : after.privates = before.privates) (functions : after.functions = before.functions)
    (bound : before.objects.length ≤ after.objects.length) :
    NodePrivateCall.Callable after table closure receiver handle :=
  ⟨callable.sourceProgram, functions ▸ callable.tableSeparate, callable.handleBound, callable.closureFound,
    privateGet_growth receiver "pushHandlerSets" (.function handle) privates bound callable.privateRead⟩

theorem storage_after_call {before after : State} {closure : PrivateMethodClosure}
    {target stamp methods collector : Nat} {rows : List Value}
    (storage : NodePrivateCall.Storage before closure target stamp methods collector rows)
    (privates : after.privates = before.privates)
    (arrays : ∀ reference, reference ≠ collector → after.heap[reference]? = before.heap[reference]?)
    (bound : before.objects.length ≤ after.objects.length) :
    NodePrivateCall.Storage after closure target stamp methods collector rows := by
  obtain ⟨object, found⟩ := storage.targetFound
  have inside : target < after.objects.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 bound
  exact ⟨⟨after.objects[target], List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩, storage.privateName,
    privates ▸ storage.privateSlot, (arrays methods (Ne.symm storage.separate)).trans storage.methodsFound,
    storage.separate, storage.legalLength⟩

end HonoLean.Upstream.NodeLiteralBranch
