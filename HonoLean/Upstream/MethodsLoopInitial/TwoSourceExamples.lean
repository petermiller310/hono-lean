import HonoLean.Upstream.MethodsLoopInitial.TwoSource
import HonoLean.Upstream.SourceSubset.ObjectInit
import HonoLean.Upstream.HandlerRecord.Contract

set_option autoImplicit false

namespace HonoLean.Upstream.MethodsLoopInitial.TwoSourceChecks

open SourceSubset ECMA2025
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def getKey : JSString := [71, 69, 84]
private def badKey : JSString := [66, 65, 68]
private def idKey : JSString := [105, 100]
private def zeroKey : JSString := [122]
private def missKey : JSString := [109]
private def keys : List JSString := [idKey, protoKey, constructorKey, zeroKey, missKey]
private def handler : OrdinaryObject := HandlerRecord.innerRecord (.number 7) 0 1
private def parent : OrdinaryObject :=
  {own := [(idKey, .data (.string [112]) true true true), (zeroKey, .data (.number 8) true true true),
    (missKey, .data (.boolean false) true true true)]
   prototype := some 0}
private def exactRow : OrdinaryObject := HandlerRecord.outerRecord getKey 2
private def allRow : OrdinaryObject :=
  {own := [(getKey, .data (.number 0) true true true), (SearchEntry.allKey, .data (.object 2) true true true)]
   prototype := some 0}
private def missingRow : OrdinaryObject := {own := [(getKey, .data (.boolean false) true true true)], prototype := some 0}
private def rows : List Value := [.object 3, .object 4, .object 3, .object 5]
private def initial : List Value := [.object 2, .object 1]
private def before : State :=
  {environment := [("METHOD_NAME_ALL", .string badKey), ("createNullObject", .number 99),
      ("params", .number 71), ("nodeParams", .number 72)]
   objects := [objectPrototypeProjection [], parent, handler, exactRow, allRow, missingRow, {prototype := some 0}]
   heap := [keys.map Value.string, rows, initial]
   functions := [⟨CreateNullObject.createProgram, []⟩]
   sets := [[idKey]]
   thisValue := .object 6
   privates := PrivateStore.ofData [("methods", 9)] [(6, [(9, .array 1)])]}
private def captures : List (String × Value) :=
  [("METHOD_NAME_ALL", .string SearchEntry.allKey), ("createNullObject", .function 0)]
private def closure : PrivateMethodClosure := ⟨NodePrivateCall.methodProgram, captures, [("methods", 9)]⟩
private def bareRecord : Record := ⟨2, handler, 0, ⟨keys, fun _ => .undefined, fun _ => .undefined⟩⟩

private theorem safe_before (reference : Nat) (bound : reference < 7) (different : reference ≠ 2) :
    Protected before [bareRecord] reference := by
  refine ⟨bound, ?_⟩
  intro record member
  have same : record = bareRecord := by simpa using member
  subst record
  exact different

private theorem parent_is_zero (reference : Nat) (object : OrdinaryObject)
    (found : before.objects[reference]? = some object) (ancestor : Nat)
    (prototype : object.prototype = some ancestor) : ancestor = 0 := by
  have member := List.mem_of_getElem? found
  change object ∈ [objectPrototypeProjection [], parent, handler, exactRow, allRow, missingRow, {prototype := some 0}] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact (Option.some.inj prototype).symm | cases prototype

/-- The first input has an allocated nonempty collector, live record alias in
its prefix, repeated GET rows, a falsy-direct ALL fallback and a miss. No q,
parameter read values or generated call formals are present in this domain. -/
theorem initial_frame_without_future_parameter_map :
    TwoSourceFrame before captures rows getKey 2 5 [bareRecord] initial := by
  refine {
    allBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    collectorFound := rfl
    capacity := by decide
    closed := ?_
    protectedParents := ?_
    recordsFound := ?_
    handlerParents := ?_
    rowChoices := ?_ }
  · intro reference _ object found ancestor prototype
    have same := parent_is_zero reference object found ancestor prototype
    subst ancestor
    decide
  · intro reference _ object found ancestor prototype
    have same := parent_is_zero reference object found ancestor prototype
    subst ancestor
    exact safe_before 0 (by decide) (by decide)
  · intro record member
    have same : record = bareRecord := by simpa using member
    subst record
    exact ⟨rfl, rfl, rfl, by decide, ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩, by decide, by decide, by decide⟩
  · intro record member ancestor prototype
    have same : record = bareRecord := by simpa using member
    subst record
    have same : ancestor = 0 := by simpa [bareRecord, handler, HandlerRecord.innerRecord] using prototype.symm
    subst ancestor
    exact safe_before 0 (by decide) (by decide)
  · intro count inside
    have cases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by change count < 4 at inside; omega
    rcases cases with rfl | rfl | rfl | rfl
    · refine ⟨3, .object 2, rfl, safe_before 3 (by decide) (by decide), ?_, fun _ => ⟨bareRecord, by simp, rfl⟩⟩
      exact ⟨.object 2, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
    · refine ⟨4, .object 2, rfl, safe_before 4 (by decide) (by decide), ?_, fun _ => ⟨bareRecord, by simp, rfl⟩⟩
      exact ⟨.number 0, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
    · refine ⟨3, .object 2, rfl, safe_before 3 (by decide) (by decide), ?_, fun _ => ⟨bareRecord, by simp, rfl⟩⟩
      exact ⟨.object 2, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
    · refine ⟨5, .undefined, rfl, safe_before 5 (by decide) (by decide), ?_, ?_⟩
      · exact ⟨.boolean false, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
      · intro impossible; cases impossible

private def qObject : OrdinaryObject :=
  newDataObject (newDataObject emptyLiteralObject idKey (.string [108])) zeroKey (.number 0)
private def current : State :=
  {before with environment := ("params", .object 7) :: before.environment
               objects := before.objects ++ [qObject]}

/-- A real parsed literal creates q. Its fresh reference/separation are proved
from allocation, not an initial guessed map or future body Layout. The complete
source123/guard chain is a separate concrete composition. -/
theorem parsed_literal_produces_parameter_map :
    (parseObjectInit "const params = { ['id']: 'l', ['z']: 0 }" []).map
      (fun program => executeObjectInit 64 defaultSplitLimit program before) = some (.ok current) := by cbv

theorem fresh_map_is_protected_and_old_gets_survive :
    Protected current [bareRecord] before.objects.length ∧
    getProperty 31 current.objects 1 protoKey = .ok (.object 0) ∧
    getProperty 31 current.objects 1 constructorKey = .ok .objectConstructor := by
  refine ⟨fresh_parameter_protected initial_frame_without_future_parameter_map (by decide), ?_, ?_⟩
  · rw [get_after_fresh_object 31 before current 1 protoKey initial_frame_without_future_parameter_map.closed (by decide)]
    · rfl
    · intro reference inside; exact List.getElem?_append_left inside
  · rw [get_after_fresh_object 31 before current 1 constructorKey initial_frame_without_future_parameter_map.closed (by decide)]
    · rfl
    · intro reference inside; exact List.getElem?_append_left inside

private def parameterValue (key : JSString) : Value :=
  if key = idKey then .string [108] else if key = protoKey then .object 0 else
    if key = constructorKey then .objectConstructor else if key = zeroKey then .number 0 else .undefined
private def nodeValue (key : JSString) : Value :=
  if key = idKey then .string [112] else if key = protoKey then .object 0 else
    if key = constructorKey then .objectConstructor else if key = zeroKey then .number 8 else .boolean false
private def records : List Record := revalueRecords [bareRecord] (fun _ => parameterValue) (fun _ => nodeValue)

/-- Snapshot read functions can be replaced AFTER map creation without adding
any assumption to the original frame. References, keys and choices stay fixed. -/
theorem current_frame_and_derived_two_source_reads :
    TwoSource current captures rows getKey 2 5 records 1 (.object 7) initial := by
  have frame := frame_after_fresh_object before current captures rows getKey 2 5 [bareRecord] initial qObject
    initial_frame_without_future_parameter_map rfl rfl rfl
    (fun ancestor prototype => by
      have same : ancestor = 0 := (Option.some.inj prototype).symm
      subst ancestor
      exact safe_before 0 (by decide) (by decide))
  refine ⟨frame_withReadValues current captures rows getKey 2 5 [bareRecord] initial _ _ frame, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · apply (protected_revalueRecords current [bareRecord] _ _ 1).mpr
    refine ⟨by decide, ?_⟩
    intro record member
    have same : record = bareRecord := by simpa using member
    subst record
    decide
  · intro reference equal
    have same : reference = 7 := (Value.object.inj equal).symm
    subst reference
    exact (protected_revalueRecords current [bareRecord] _ _ 7).mpr fresh_map_is_protected_and_old_gets_survive.1
  · intro record member key used
    have same : record = withReadValues bareRecord parameterValue nodeValue := by simpa [records, revalueRecords] using member
    subst record
    change key ∈ [idKey, protoKey, constructorKey, zeroKey, missKey] at used
    simp only [List.mem_cons, List.not_mem_nil, or_false] at used
    rcases used with rfl | rfl | rfl | rfl | rfl <;> exact ⟨.object 7 _ rfl, rfl⟩

private theorem storage : NodePrivateCall.Storage current closure 6 9 1 2 rows :=
  ⟨⟨{prototype := some 0}, rfl⟩, rfl, ⟨[(9, .array 1)], rfl, rfl⟩, rfl, by decide, by decide⟩

theorem actual_formals_and_stored_rows_derive_body_layout :
    MethodsLoop.Inputs (NodePrivateCall.bodyState current closure (.object 6) 2 6 getKey 1 (.object 7)) 6 9 1 2 rows getKey ∧
    Layout (NodePrivateCall.bodyState current closure (.object 6) 2 6 getKey 1 (.object 7)) rows getKey 2 5 records (.object 7) 1 initial :=
  body_inputs_layout_from_twoSource current captures rows getKey 2 5 records 1 (.object 7) initial closure (.object 6) 6 9 1
    current_frame_and_derived_two_source_reads rfl storage

theorem source_loop_execution_follows_from_only_current_facts :
    ∃ after,
      runBlock 112 MethodsLoop.program (NodePrivateCall.bodyState current closure (.object 6) 2 6 getKey 1 (.object 7)) = .ok (.normal after) ∧
      MethodsLoop.LoopContract (NodePrivateCall.bodyState current closure (.object 6) 2 6 getKey 1 (.object 7)) after rows getKey 2 := by
  exact NodePrivateCall.body_satisfies current closure (.object 6) 6 9 1 2 5 rows getKey 1 (.object 7) records initial
    storage actual_formals_and_stored_rows_derive_body_layout.2

private def observe (state : State) : Option (Option (List Value) × Nat × Option PropertyDescriptor × Option PropertyDescriptor ×
    Option PropertyDescriptor × Option PropertyDescriptor × Option PropertyDescriptor) := do
  let record ← state.objects[2]?
  let .data (.object output) _ _ _ ← record.own.lookup NodeParamAssignment.paramsKey | none
  let object ← state.objects[output]?
  return (state.heap[2]?, output, object.own.lookup idKey, object.own.lookup protoKey,
    object.own.lookup constructorKey, object.own.lookup zeroKey, object.own.lookup missKey)

/-- The preexisting first collector entry still denotes the same live handler.
Three captures reset it; every alias sees the LAST params object, not a stale
snapshot. Optional zero does not override parent8; parent false and inherited
proto/constructor values survive the actual source selection. -/
theorem shared_live_prefix_observes_latest_capture :
    (runBlock 112 MethodsLoop.program (NodePrivateCall.bodyState current closure (.object 6) 2 6 getKey 1 (.object 7))).map
      (fun result => match result with | .normal state => observe state | .returned _ _ => none) =
      .ok (some (some [.object 2, .object 1, .object 2, .object 2, .object 2], 10,
        some (.data (.string [108]) true true true), some (.data (.object 0) true true true),
        some (.data .objectConstructor true true true), some (.data (.number 8) true true true),
        some (.data (.boolean false) true true true))) := by cbv

theorem argument_positions_and_capture_imports_are_not_caller_shadows :
    (NodePrivateCall.bodyState current closure (.object 6) 2 6 getKey 1 (.object 7)).environment.lookup "nodeParams" = some (.object 1) ∧
    (NodePrivateCall.bodyState current closure (.object 6) 2 6 getKey 1 (.object 7)).environment.lookup "params" = some (.object 7) ∧
    (NodePrivateCall.bodyState current closure (.object 6) 2 6 getKey 1 (.object 7)).environment.lookup "METHOD_NAME_ALL" =
      some (.string SearchEntry.allKey) ∧
    before.environment.lookup "METHOD_NAME_ALL" = some (.string badKey) := by cbv

/-- info: 'HonoLean.Upstream.MethodsLoopInitial.body_inputs_layout_from_twoSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.MethodsLoopInitial.body_inputs_layout_from_twoSource
/-- info: 'HonoLean.Upstream.MethodsLoopInitial.frame_after_fresh_object' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.MethodsLoopInitial.frame_after_fresh_object
/-- info: 'HonoLean.Upstream.MethodsLoopInitial.frame_withReadValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.MethodsLoopInitial.frame_withReadValues

end HonoLean.Upstream.MethodsLoopInitial.TwoSourceChecks
