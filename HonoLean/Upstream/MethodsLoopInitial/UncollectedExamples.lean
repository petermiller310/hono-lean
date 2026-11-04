import HonoLean.Upstream.MethodsLoopInitial.Uncollected
import HonoLean.Upstream.HandlerRecord.Contract

namespace HonoLean.Upstream.MethodsLoopInitial.UncollectedChecks

open SourceSubset ECMA2025

private def getKey : JSString := [71, 69, 84]
private def badKey : JSString := [66, 65, 68]
private def idKey : JSString := [105, 100]
private def handler : OrdinaryObject := HandlerRecord.innerRecord (.number 7) 0 1
private def before : State :=
  {environment := [("METHOD_NAME_ALL", .string badKey), ("createNullObject", .number 99), ("Object", .number 123)]
   heap := [[.string idKey], [.number 17]]
   objects := [objectPrototypeProjection [], emptyNullObject, handler, HandlerRecord.outerRecord SearchEntry.allKey 2]
   functions := [⟨CreateNullObject.createProgram, []⟩]}
private def captures : List (String × Value) :=
  [("METHOD_NAME_ALL", .string SearchEntry.allKey), ("createNullObject", .function 0)]
private def record : Record :=
  ⟨2, handler, 0, ⟨[idKey], fun _ => .undefined, fun _ => .undefined⟩⟩
private def records : List Record := [record]
private def rows : List Value := [.object 3] ++ [.object 3]
private def closure : PrivateMethodClosure := ⟨NodePrivateCall.methodProgram, captures, []⟩

private theorem safeReference (reference : Nat) (bound : reference < 4) (different : reference ≠ 2) :
    Protected before records reference := by
  refine ⟨bound, ?_⟩
  intro current member
  have same : current = record := by simpa [records] using member
  subst current
  exact different

private theorem parent_zero (reference : Nat) (object : OrdinaryObject)
    (found : before.objects[reference]? = some object) (parent : Nat)
    (prototype : object.prototype = some parent) : parent = 0 := by
  have member := List.mem_of_getElem? found
  change object ∈ [objectPrototypeProjection [], emptyNullObject, handler,
    HandlerRecord.outerRecord SearchEntry.allKey 2] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    first | exact (Option.some.inj prototype).symm | cases prototype

private theorem initial_record : UncollectedRecordFacts before 1 1 record := by
  refine {
    found := rfl, possibleKeys := rfl, keysFound := rfl
    resettable := ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
    unique := by decide, legalKeys := by decide, keyBound := by decide
    parameterUndefined := fun _ _ => rfl
    nodeReads := fun _ _ => rfl }

/-- Both calls use the same row and same mutable record. All fields refer to
the old heap and captured module imports, with no initial collector cell. -/
theorem shared_nonempty_initial_domain : Uncollected before captures rows getKey 1 records 1 := by
  refine {
    allBinding := rfl
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩
    capacity := by decide
    closed := ?_, protectedParents := ?_
    nodeProtected := safeReference 1 (by decide) (by decide)
    recordsFound := ?_, handlerParents := ?_, rowChoices := ?_ }
  · intro reference _ object found parent prototype
    have same := parent_zero reference object found parent prototype
    subst parent
    decide
  · intro reference _ object found parent prototype
    have same := parent_zero reference object found parent prototype
    subst parent
    exact safeReference 0 (by decide) (by decide)
  · intro current member
    have same : current = record := by simpa [records] using member
    subst current
    exact initial_record
  · intro current member parent prototype
    have same : current = record := by simpa [records] using member
    subst current
    have same : parent = 0 := by simpa [record, handler, HandlerRecord.innerRecord] using prototype.symm
    subst parent
    exact safeReference 0 (by decide) (by decide)
  · intro count inside
    have cases : count = 0 ∨ count = 1 := by change count < 2 at inside; omega
    have rowChoice : SearchEntry.Choice (capturedView before captures) 3 getKey (.object 2) :=
      ⟨.undefined, rfl, Or.inr ⟨(by intro impossible; cases impossible), SearchEntry.allKey, rfl, rfl⟩⟩
    rcases cases with rfl | rfl <;>
      exact ⟨3, .object 2, rfl, safeReference 3 (by decide) (by decide), rowChoice,
        fun _ => ⟨record, by simp [records], rfl⟩⟩

theorem collector_is_absent_and_keys_are_old :
    before.environment.lookup "handlerSets" = none ∧ before.heap[2]? = none ∧
    before.heap[0]? = some [.string idKey] ∧ before.heap[1]? = some [.number 17] ∧
    record.keysArray < before.heap.length ∧ before.heap.length ≠ record.keysArray :=
  ⟨rfl, rfl, rfl, rfl, (uncollected_keys_before_collector initial_record).1,
    (uncollected_keys_before_collector initial_record).2⟩

private def after : State :=
  {before with
    environment := [("queue", .array 3), ("collector", .array 2)] ++ before.environment
    heap := before.heap ++ [[], [.number 17]]}

/-- The future heap in this example is obtained by actual parsed allocation;
it is not an initial Layout assumption or an invented collector read. -/
theorem parsed_allocations_produce_append :
    (parseBlock "const collector = []\nconst queue = [17]" []).map
      (fun source => execute 32 defaultSplitLimit source before) = some (.ok (.normal after)) := by cbv

theorem append_derives_layout_for_shared_union :
    Layout (NodePrivateCall.bodyState after closure (.object 0) 2 0 getKey 1 .undefined)
      rows getKey 2 1 records .undefined 1 [] :=
  body_layout_from_uncollected before after captures rows getKey 1 records 1 closure (.object 0) 0 [[.number 17]]
    shared_nonempty_initial_domain rfl rfl rfl rfl

theorem generated_formals_and_imports_follow_actual_capture :
    (NodePrivateCall.bodyState after closure (.object 0) 2 0 getKey 1 .undefined).environment.lookup "handlerSets" =
      some (.array 2) ∧
    (NodePrivateCall.bodyState after closure (.object 0) 2 0 getKey 1 .undefined).environment.lookup "params" =
      some .undefined ∧
    (NodePrivateCall.bodyState after closure (.object 0) 2 0 getKey 1 .undefined).environment.lookup "nodeParams" =
      some (.object 1) ∧
    (NodePrivateCall.bodyState after closure (.object 0) 2 0 getKey 1 .undefined).environment.lookup "METHOD_NAME_ALL" =
      some (.string SearchEntry.allKey) ∧
    (NodePrivateCall.bodyState after closure (.object 0) 2 0 getKey 1 .undefined).environment.lookup "createNullObject" =
      some (.function 0) ∧ before.environment.lookup "METHOD_NAME_ALL" = some (.string badKey) := by cbv

theorem caller_shadow_does_not_supply_initial_row_choice :
    ¬ SearchEntry.Choice before 3 getKey (.object 2) := by
  rintro ⟨direct, read, choice⟩
  have value : direct = .undefined := (Except.ok.inj read).symm
  subst direct
  rcases choice with ⟨impossible, _⟩ | ⟨_, fallback, binding, selected⟩
  · cases impossible
  · have key : fallback = badKey := (Value.string.inj (Option.some.inj binding)).symm
    subst fallback
    cases selected

/-- info: 'HonoLean.Upstream.MethodsLoopInitial.body_layout_from_uncollected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.MethodsLoopInitial.body_layout_from_uncollected

end HonoLean.Upstream.MethodsLoopInitial.UncollectedChecks
