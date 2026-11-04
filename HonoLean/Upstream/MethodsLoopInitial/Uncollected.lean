import HonoLean.Upstream.NodePrivateCall.Contract

namespace HonoLean.Upstream.MethodsLoopInitial

open SourceSubset ECMA2025

/-- Only the initial caller environment is replaced by the already captured
module values. All heaps/stores remain exactly those before startup. No call
formal, collector reference or future allocation is present in this view. -/
def capturedView (before : State) (captureEnvironment : List (String × Value)) : State :=
  {before with environment := captureEnvironment}

/-- Initial handler facts without a collector or a guessed future separation.
The actual four-argument helper's optional parameter is undefined; nodeParams
denotes the source emptyParams object selected by the earlier private reset. -/
structure UncollectedRecordFacts (before : State) (keyBound nodeParams : Nat) (record : Record) : Prop where
  found : before.objects[record.reference]? = some record.object
  possibleKeys : record.object.own.lookup NodeParamLoop.possibleKeysKey =
    some (.data (.array record.keysArray) true true true)
  keysFound : before.heap[record.keysArray]? = some (record.snapshot.keys.map Value.string)
  resettable : NodeParamLoop.Resettable before.objects record.reference record.object
  unique : record.snapshot.keys.Nodup
  legalKeys : record.snapshot.keys.length ≤ 4294967295
  keyBound : record.snapshot.keys.length ≤ keyBound
  parameterUndefined : ∀ key ∈ record.snapshot.keys, record.snapshot.parameter key = .undefined
  nodeReads : ∀ key ∈ record.snapshot.keys,
    getProperty propertyFuel before.objects nodeParams key = .ok (record.snapshot.node key)

/-- One INITIAL structural domain before the collector exists. Repeated rows
and shared mutable records are permitted. Captured imports are independent of
same-spelling caller shadows. There is no future State/Layout, formal binding,
collector cell, completed allocation or successful-evaluation premise. -/
structure Uncollected (before : State) (captureEnvironment : List (String × Value))
    (rows : List Value) (method : JSString) (keyBound : Nat) (records : List Record) (nodeParams : Nat) : Prop where
  allBinding : captureEnvironment.lookup "METHOD_NAME_ALL" = some (.string SearchEntry.allKey)
  helper : ∃ reference helperEnvironment,
    captureEnvironment.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, helperEnvironment⟩ ∧
    StandardObjectBinding {before with environment := helperEnvironment}
  capacity : rows.length ≤ 4294967295
  closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length
  protectedParents : ∀ reference, Protected before records reference →
    ∀ object, before.objects[reference]? = some object →
    ∀ parent, object.prototype = some parent → Protected before records parent
  nodeProtected : Protected before records nodeParams
  recordsFound : ∀ record ∈ records, UncollectedRecordFacts before keyBound nodeParams record
  handlerParents : ∀ record ∈ records, ∀ parent,
    record.object.prototype = some parent → Protected before records parent
  rowChoices : ∀ count, count < rows.length → ∃ row chosen,
    rows[count]? = some (.object row) ∧ Protected before records row ∧
    SearchEntry.Choice (capturedView before captureEnvironment) row method chosen ∧
    (NodeParamAssignment.Truthy chosen → ∃ record ∈ records, chosen = .object record.reference)

/-- Existing key snapshots already occupy old heap cells, so the allocator's
fresh collector index is distinct without any caller-supplied disjointness. -/
theorem uncollected_keys_before_collector {before : State} {keyBound nodeParams : Nat} {record : Record}
    (facts : UncollectedRecordFacts before keyBound nodeParams record) :
    record.keysArray < before.heap.length ∧ before.heap.length ≠ record.keysArray := by
  have inside := (List.getElem?_eq_some_iff.mp facts.keysFound).1
  exact ⟨inside, by omega⟩

private theorem old_array_append {before after : State} {extra : List (List Value)}
    (heap : after.heap = before.heap ++ ([] :: extra)) (reference : Nat) (values : List Value)
    (found : before.heap[reference]? = some values) : after.heap[reference]? = some values := by
  rw [heap, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- Construct ordinary loop admission after REAL source append/frame facts.
The source private reset and all caller/header environments may differ: only
ordinary objects, old arrays and immutable helpers are relevant here. Generated
call formals are introduced by the existing bodyState definition in the
CONCLUSION, rather than presumed in the initial input predicate. -/
theorem body_layout_from_uncollected (before after : State) (captureEnvironment : List (String × Value))
    (rows : List Value) (method : JSString) (keyBound : Nat) (records : List Record) (nodeParams : Nat)
    (closure : PrivateMethodClosure) (receiver : Value) (target : Nat) (extra : List (List Value))
    (facts : Uncollected before captureEnvironment rows method keyBound records nodeParams)
    (captured : closure.environment = captureEnvironment)
    (objects : after.objects = before.objects) (functions : after.functions = before.functions)
    (heap : after.heap = before.heap ++ ([] :: extra)) :
    Layout (NodePrivateCall.bodyState after closure receiver before.heap.length target method nodeParams .undefined)
      rows method before.heap.length keyBound records .undefined nodeParams [] := by
  let origin := NodePrivateCall.bodyState after closure receiver before.heap.length target method nodeParams .undefined
  have originObjects : origin.objects = before.objects := objects
  have originFunctions : origin.functions = before.functions := functions
  have originHeap : origin.heap = before.heap ++ ([] :: extra) := heap
  have safe : ∀ reference, Protected origin records reference ↔ Protected before records reference := by
    intro reference
    simp only [Protected, originObjects]
  change Layout origin rows method before.heap.length keyBound records .undefined nodeParams []
  refine {
    collectorBinding := rfl
    parameterBinding := rfl
    nodeBinding := rfl
    allBinding := ?_
    helper := ?_
    collectorFound := ?_
    capacity := by simpa using facts.capacity
    closed := by simpa [originObjects] using facts.closed
    protectedParents := ?_
    nodeProtected := (safe nodeParams).mpr facts.nodeProtected
    parameterProtected := ?_
    recordsFound := ?_
    handlerParents := ?_
    rowChoices := ?_ }
  · simpa [SearchEntry.AllImportBinding, origin, NodePrivateCall.bodyState, captured, List.lookup_cons] using facts.allBinding
  · obtain ⟨reference, helperEnvironment, binding, found, standard⟩ := facts.helper
    refine ⟨reference, helperEnvironment, ?_, by simpa [originFunctions] using found, ?_⟩
    · simpa [origin, NodePrivateCall.bodyState, captured, List.lookup_cons] using binding
    · simpa [StandardObjectBinding] using standard
  · simp [originHeap]
  · intro reference safeReference object found parent prototype
    exact (safe parent).mpr (facts.protectedParents reference ((safe reference).mp safeReference) object
      (by simpa [originObjects] using found) parent prototype)
  · intro reference equal
    cases equal
  · intro record member
    have initial := facts.recordsFound record member
    refine {
      found := by simpa [originObjects] using initial.found
      possibleKeys := initial.possibleKeys
      keysFound := old_array_append originHeap record.keysArray _ initial.keysFound
      separate := (uncollected_keys_before_collector initial).2
      resettable := by simpa [originObjects] using initial.resettable
      unique := initial.unique
      legalKeys := initial.legalKeys
      keyBound := initial.keyBound
      reads := ?_ }
    intro key used
    rw [initial.parameterUndefined key used]
    exact ⟨.nullish _ (Or.inr rfl), by simpa [originObjects] using initial.nodeReads key used⟩
  · intro record member parent prototype
    exact (safe parent).mpr (facts.handlerParents record member parent prototype)
  · intro count inside
    obtain ⟨row, chosen, atRow, safeRow, choice, admitted⟩ := facts.rowChoices count inside
    refine ⟨row, chosen, atRow, (safe row).mpr safeRow, ?_, admitted⟩
    simpa [SearchEntry.Choice, capturedView, origin, NodePrivateCall.bodyState, captured, objects, List.lookup_cons] using choice

end HonoLean.Upstream.MethodsLoopInitial
