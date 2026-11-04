import HonoLean.Upstream.NodePrivateCall.Correctness

namespace HonoLean.Upstream.NodePrivateCall.Examples

open SourceSubset ECMA2025

private def getKey : JSString := [71, 69, 84]
private def idKey : JSString := [105, 100]
private def secondKey : JSString := [115, 101, 99, 111, 110, 100]
private def old0 : Value := .string [111, 108, 100, 48]
private def old1 : Value := .string [111, 108, 100, 49]
private def temp0 : Value := .string [116, 101, 109, 112, 48]
private def temp1 : Value := .string [116, 101, 109, 112, 49]
private def root : OrdinaryObject := objectPrototypeProjection []
private def missed : OrdinaryObject := {prototype := some 0}
private def hit : OrdinaryObject := newDataObject {prototype := some 0} getKey (.object 4)
private def every : OrdinaryObject := newDataObject {prototype := some 0} SearchEntry.allKey (.object 4)
private def handler : OrdinaryObject := newDataObject {prototype := some 0} NodeParamLoop.possibleKeysKey (.array 0)
private def oldParams : OrdinaryObject := newDataObject (newDataObject emptyNullObject idKey old0) secondKey old1
private def tempParams : OrdinaryObject := newDataObject (newDataObject emptyNullObject idKey temp0) secondKey temp1
private def rows : List Value := [.object 1, .object 2, .object 3]

private def closure : PrivateMethodClosure :=
  ⟨methodProgram, [("METHOD_NAME_ALL", .string SearchEntry.allKey), ("createNullObject", .function 0)],
    [("methods", 19), ("params", 21), ("pushHandlerSets", 20)]⟩
private def table : PrivateMethodTable := ⟨1, [closure]⟩

/-- Root receiver9, target node7, and caller's source node8 are distinct.
Caller import/parameter names deliberately shadow the captured/body bindings. -/
private def before : State :=
  {environment := [("handlerSets", .array 2), ("nextNode", .object 7), ("child", .object 7),
      ("method", .string getKey), ("node", .object 8), ("params", .object 6),
      ("nodeParams", .number 99), ("METHOD_NAME_ALL", .number 123), ("callerOnly", .number 42)],
    heap := [[.string idKey, .string secondKey], rows, []],
    objects := [root, missed, hit, every, handler, oldParams, tempParams,
      {prototype := some 0}, {prototype := some 0}, {prototype := some 0}],
    functions := [⟨CreateNullObject.createProgram, []⟩],
    privates := ⟨[("pushHandlerSets", 20), ("params", 21)],
      [(7, [(19, .data (.array 1))]), (8, [(21, .data (.object 5))]), (9, [(20, .method (.function 1))])]⟩}

private def primary (parameterized : Bool) : Nat := if parameterized then 6 else 5
private def optional (parameterized : Bool) : Value := if parameterized then .object 5 else .undefined
private def origin (parameterized : Bool) : State :=
  bodyState before closure (.object 9) 2 7 getKey (primary parameterized) (optional parameterized)
private def snapshot (parameterized : Bool) : NodeParamLoop.Snapshot :=
  ⟨[idKey, secondKey],
    fun key => if parameterized then if key = idKey then old0 else old1 else .undefined,
    fun key => if parameterized then if key = idKey then temp0 else temp1
      else if key = idKey then old0 else old1⟩
private def record (parameterized : Bool) : MethodsLoopInitial.Record := ⟨4, handler, 0, snapshot parameterized⟩

private theorem callable : Callable before table closure 9 1 := by
  exact ⟨rfl, by decide, by decide, rfl, rfl⟩
private theorem storage : Storage before closure 7 19 1 2 rows :=
  ⟨⟨{prototype := some 0}, rfl⟩, rfl, ⟨[(19, .array 1)], rfl, rfl⟩, rfl, by decide, by decide⟩
private theorem fourReads : FourReads before 2 7 getKey 5 :=
  ⟨rfl, rfl, rfl, .object 8, rfl, rfl⟩
private theorem fiveReads : FiveReads before 2 7 getKey 6 (.object 5) :=
  ⟨rfl, rfl, rfl, rfl, .object 8, rfl, rfl⟩

private theorem protected_iff (mode : Bool) (reference : Nat) :
    MethodsLoopInitial.Protected (origin mode) [record mode] reference ↔ reference < 10 ∧ reference ≠ 4 := by
  simp [MethodsLoopInitial.Protected, origin, bodyState, before, record]

private theorem closed (mode : Bool) : NodeParamLoop.PrototypeClosed (origin mode).objects (origin mode).objects.length := by
  intro reference _ object found parent prototype
  have member := List.mem_of_getElem? found
  change object ∈ [root, missed, hit, every, handler, oldParams, tempParams,
    {prototype := some 0}, {prototype := some 0}, {prototype := some 0}] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [root, missed, hit, every, handler, oldParams, tempParams, newDataObject, emptyNullObject,
      objectPrototypeProjection] at prototype <;>
    subst parent <;> simp [origin, bodyState, before]

private theorem protected_parents (mode : Bool) :
    ∀ reference, MethodsLoopInitial.Protected (origin mode) [record mode] reference → ∀ object,
      (origin mode).objects[reference]? = some object → ∀ parent,
      object.prototype = some parent → MethodsLoopInitial.Protected (origin mode) [record mode] parent := by
  intro reference _ object found parent prototype
  have member := List.mem_of_getElem? found
  change object ∈ [root, missed, hit, every, handler, oldParams, tempParams,
    {prototype := some 0}, {prototype := some 0}, {prototype := some 0}] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [root, missed, hit, every, handler, oldParams, tempParams, newDataObject, emptyNullObject,
      objectPrototypeProjection] at prototype <;>
    subst parent <;> exact (protected_iff mode 0).mpr (by decide)

private theorem record_facts (mode : Bool) :
    MethodsLoopInitial.RecordFacts (origin mode) 2 2 (optional mode) (primary mode) (record mode) := by
  refine ⟨rfl, rfl, rfl, by change 2 ≠ 0; decide, ?_,
    by change [idKey, secondKey].Nodup; decide,
    by change 2 ≤ 4294967295; decide, by change 2 ≤ 2; decide, ?_⟩
  · exact ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  · intro key member
    change key ∈ [idKey, secondKey] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cases mode
    · exact ⟨.nullish _ (Or.inr rfl), rfl⟩
    · exact ⟨.object 5 _ rfl, rfl⟩
    · exact ⟨.nullish _ (Or.inr rfl), rfl⟩
    · exact ⟨.object 5 _ rfl, rfl⟩

private theorem layout (mode : Bool) :
    MethodsLoopInitial.Layout (origin mode) rows getKey 2 2 [record mode] (optional mode) (primary mode) [] := by
  refine {
    collectorBinding := rfl, parameterBinding := rfl, nodeBinding := rfl, allBinding := rfl,
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩,
    collectorFound := rfl, capacity := by decide,
    closed := closed mode, protectedParents := protected_parents mode,
    nodeProtected := ?_, parameterProtected := ?_, recordsFound := ?_, handlerParents := ?_, rowChoices := ?_ }
  · cases mode <;> exact (protected_iff _ _).mpr (by decide)
  · intro reference equal
    cases mode
    · cases equal
    · have same : reference = 5 := (Value.object.inj equal).symm
      subst reference
      exact (protected_iff true 5).mpr (by decide)
  · intro other member
    have same : other = record mode := by simpa using member
    subst other
    exact record_facts mode
  · intro other member parent prototype
    have same : other = record mode := by simpa using member
    subst other
    have sameParent : parent = 0 := by simpa [record, handler, newDataObject] using prototype.symm
    subst parent
    exact (protected_iff mode 0).mpr (by decide)
  · intro count inside
    have choices : count = 0 ∨ count = 1 ∨ count = 2 := by change count < 3 at inside; omega
    rcases choices with rfl | rfl | rfl
    · refine ⟨1, .undefined, rfl, (protected_iff mode 1).mpr (by decide), ?_, ?_⟩
      · exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
      · intro impossible; simp [NodeParamAssignment.Truthy] at impossible
    · refine ⟨2, .object 4, rfl, (protected_iff mode 2).mpr (by decide), ?_, ?_⟩
      · exact ⟨.object 4, rfl, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
      · intro _; exact ⟨record mode, by simp, rfl⟩
    · refine ⟨3, .object 4, rfl, (protected_iff mode 3).mpr (by decide), ?_, ?_⟩
      · exact ⟨.undefined, rfl, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, rfl, rfl⟩⟩
      · intro _; exact ⟨record mode, by simp, rfl⟩

/-- Both universal call theorems have inhabited nonempty protected domains.
Three rows combine a miss, GET hit and ALL fallback; both hits capture two keys. -/
theorem source_calls_have_nonempty_contracts :
    (∃ after,
      (parsePrivateMethodCall pinnedFourSource fourBindings classPrivateNames).map
        (fun call => runPrivateMethodCall 108 defaultSplitLimit table ⟨.object 9⟩ call before) =
          some (.ok (.undefined, after)) ∧
      CallContract before (origin false) rows getKey 2 .undefined after) ∧
    (∃ after,
      (parsePrivateMethodCall pinnedFiveSource fiveBindings classPrivateNames).map
        (fun call => runPrivateMethodCall 108 defaultSplitLimit table ⟨.object 9⟩ call before) =
          some (.ok (.undefined, after)) ∧
      CallContract before (origin true) rows getKey 2 .undefined after) := by
  constructor
  · exact (parsed_four_satisfies before table closure 9 1 7 19 1 2 2 rows getKey 5 [record false] []
      callable fourReads storage (layout false)).2
  · exact (parsed_five_satisfies before table closure 9 1 7 19 1 2 2 rows getKey 6 (.object 5) [record true] []
      callable fiveReads storage (layout true)).2

private def observe (result : Except EvalError (Value × State)) (caller : State := before) :
    Except EvalError (Value × Option (List Value) × Except EvalError Value × Except EvalError Value × Bool × Bool) := do
  let (returned, after) ← result
  return (returned, after.heap[2]?, getProperty propertyFuel after.objects 11 idKey |>.mapError .objectError,
    getProperty propertyFuel after.objects 11 secondKey |>.mapError .objectError,
    decide (after.environment = caller.environment) && decide (after.thisValue = caller.thisValue), decide (after.privates = caller.privates))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
/-- Closed executions preserve caller state and expose positional capture:
direct call gets old0/old1; the five-argument call gets old0/temp1. Repeated
rows retain the same handler reference twice, with freshly reset params. -/
theorem source_argument_order_changes_capture :
    ((parsePrivateMethodCall pinnedFourSource fourBindings classPrivateNames).map
      (fun call => observe (runPrivateMethodCall 108 defaultSplitLimit table ⟨.object 9⟩ call before)) =
        some (.ok (.undefined, some [.object 4, .object 4], .ok old0, .ok old1, true, true))) ∧
    ((parsePrivateMethodCall pinnedFiveSource fiveBindings classPrivateNames).map
      (fun call => observe (runPrivateMethodCall 108 defaultSplitLimit table ⟨.object 9⟩ call before)) =
        some (.ok (.undefined, some [.object 4, .object 4], .ok old0, .ok temp1, true, true))) := by
  rw [parses_four, parses_five]
  cbv

private def sameScopeBefore : State :=
  {before with privates := {before.privates with names := closure.privateNames}}

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
/-- A same-supplied-class-scope control retains the same direct captures and
restores that shared lexical private map. The different-scope witness above
tests closure transport; neither asserts surrounding Node state reachability. -/
theorem source_same_private_scope_control :
    (parsePrivateMethodCall pinnedFourSource fourBindings classPrivateNames).map
      (fun call => observe (runPrivateMethodCall 108 defaultSplitLimit table ⟨.object 9⟩ call sameScopeBefore)
        sameScopeBefore) =
          some (.ok (.undefined, some [.object 4, .object 4], .ok old0, .ok old1, true, true)) := by
  rw [parses_four]
  cbv

end HonoLean.Upstream.NodePrivateCall.Examples
