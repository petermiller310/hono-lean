import HonoLean.Upstream.MethodsLoopInitial.Uncollected
import HonoLean.Upstream.NodePrivateCall.Correctness

set_option autoImplicit false

namespace HonoLean.Upstream.MethodsLoopInitial

open SourceSubset ECMA2025

/-- Current-call handler shape and immutable key snapshot. Neither parameter
source nor a future body environment occurs in these facts. -/
structure TwoSourceRecordFacts (before : State) (collector keyBound : Nat) (record : Record) : Prop where
  found : before.objects[record.reference]? = some record.object
  possibleKeys : record.object.own.lookup NodeParamLoop.possibleKeysKey =
    some (.data (.array record.keysArray) true true true)
  keysFound : before.heap[record.keysArray]? = some (record.snapshot.keys.map Value.string)
  separate : collector ≠ record.keysArray
  resettable : NodeParamLoop.Resettable before.objects record.reference record.object
  unique : record.snapshot.keys.Nodup
  legalKeys : record.snapshot.keys.length ≤ 4294967295
  keyBound : record.snapshot.keys.length ≤ keyBound

/-- Structural facts in the actual current caller state, before formals are
bound. The collector already exists and may have a live, nonempty prefix.
Repeated rows and repeated mutable records are allowed. Helper imports are
those of the closure, independently of same-spelling caller shadows. -/
structure TwoSourceFrame (before : State) (captureEnvironment : List (String × Value))
    (rows : List Value) (method : JSString) (collector keyBound : Nat) (records : List Record)
    (initial : List Value) : Prop where
  allBinding : captureEnvironment.lookup "METHOD_NAME_ALL" = some (.string SearchEntry.allKey)
  helper : ∃ reference helperEnvironment,
    captureEnvironment.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, helperEnvironment⟩ ∧
    StandardObjectBinding {before with environment := helperEnvironment}
  collectorFound : before.heap[collector]? = some initial
  capacity : initial.length + rows.length ≤ 4294967295
  closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length
  protectedParents : ∀ reference, Protected before records reference →
    ∀ object, before.objects[reference]? = some object →
    ∀ parent, object.prototype = some parent → Protected before records parent
  recordsFound : ∀ record ∈ records, TwoSourceRecordFacts before collector keyBound record
  handlerParents : ∀ record ∈ records, ∀ parent,
    record.object.prototype = some parent → Protected before records parent
  rowChoices : ∀ count, count < rows.length → ∃ row chosen,
    rows[count]? = some (.object row) ∧ Protected before records row ∧
    SearchEntry.Choice (capturedView before captureEnvironment) row method chosen ∧
    (NodeParamAssignment.Truthy chosen → ∃ record ∈ records, chosen = .object record.reference)

/-- BOTH source maps are explicit. The fourth argument is nodeParams; the
optional fifth is parameterReceiver. Pure ordinary own/inherited Get contracts
include falsy values, constructor and the standard legacy __proto__ getter.
Only the current state is read; there is no future capture/run/Layout premise. -/
structure TwoSourceReads (before : State) (records : List Record) (nodeParams : Nat)
    (parameterReceiver : Value) : Prop where
  nodeProtected : Protected before records nodeParams
  parameterProtected : ∀ reference, parameterReceiver = .object reference → Protected before records reference
  reads : ∀ record ∈ records, ∀ key ∈ record.snapshot.keys,
    NodeParamAssignment.ParameterRead before key parameterReceiver (record.snapshot.parameter key) ∧
    getProperty propertyFuel before.objects nodeParams key = .ok (record.snapshot.node key)

structure TwoSource (before : State) (captureEnvironment : List (String × Value))
    (rows : List Value) (method : JSString) (collector keyBound : Nat) (records : List Record)
    (nodeParams : Nat) (parameterReceiver : Value) (initial : List Value) : Prop where
  frame : TwoSourceFrame before captureEnvironment rows method collector keyBound records initial
  sources : TwoSourceReads before records nodeParams parameterReceiver

theorem parameterRead_same_objects (before after : State) (key : JSString) (receiver value : Value)
    (objects : after.objects = before.objects)
    (read : NodeParamAssignment.ParameterRead before key receiver value) :
    NodeParamAssignment.ParameterRead after key receiver value := by
  cases read with
  | object reference value read => exact .object reference value (by simpa [objects] using read)
  | nullish receiver missing => exact .nullish receiver missing

/-- The actual call introduces the five formal bindings. Initial facts do not
need to pretend those bindings already exist in the caller. Positional sources
are retained: parent nodeParams is fourth, optional local q is fifth. -/
theorem body_layout_from_twoSource (before : State) (captureEnvironment : List (String × Value))
    (rows : List Value) (method : JSString) (collector keyBound : Nat) (records : List Record)
    (nodeParams : Nat) (parameterReceiver : Value) (initial : List Value)
    (closure : PrivateMethodClosure) (receiver : Value) (target : Nat)
    (facts : TwoSource before captureEnvironment rows method collector keyBound records nodeParams parameterReceiver initial)
    (captured : closure.environment = captureEnvironment) :
    Layout (NodePrivateCall.bodyState before closure receiver collector target method nodeParams parameterReceiver)
      rows method collector keyBound records parameterReceiver nodeParams initial := by
  let origin := NodePrivateCall.bodyState before closure receiver collector target method nodeParams parameterReceiver
  change Layout origin rows method collector keyBound records parameterReceiver nodeParams initial
  refine {
    collectorBinding := rfl
    parameterBinding := rfl
    nodeBinding := rfl
    allBinding := ?_
    helper := ?_
    collectorFound := facts.frame.collectorFound
    capacity := facts.frame.capacity
    closed := facts.frame.closed
    protectedParents := facts.frame.protectedParents
    nodeProtected := facts.sources.nodeProtected
    parameterProtected := facts.sources.parameterProtected
    recordsFound := ?_
    handlerParents := facts.frame.handlerParents
    rowChoices := ?_ }
  · simpa [SearchEntry.AllImportBinding, origin, NodePrivateCall.bodyState, captured, List.lookup_cons] using facts.frame.allBinding
  · obtain ⟨reference, helperEnvironment, binding, found, standard⟩ := facts.frame.helper
    refine ⟨reference, helperEnvironment, ?_, found, ?_⟩
    · simpa [origin, NodePrivateCall.bodyState, captured, List.lookup_cons] using binding
    · simpa [StandardObjectBinding] using standard
  · intro record member
    have shape := facts.frame.recordsFound record member
    refine ⟨shape.found, shape.possibleKeys, shape.keysFound, shape.separate, shape.resettable,
      shape.unique, shape.legalKeys, shape.keyBound, ?_⟩
    intro key used
    obtain ⟨parameter, node⟩ := facts.sources.reads record member key used
    constructor
    · exact parameterRead_same_objects before origin key parameterReceiver _ rfl parameter
    · exact node
  · intro count inside
    obtain ⟨row, chosen, atRow, safeRow, choice, admitted⟩ := facts.frame.rowChoices count inside
    refine ⟨row, chosen, atRow, safeRow, ?_, admitted⟩
    simpa [SearchEntry.Choice, capturedView, origin, NodePrivateCall.bodyState, captured, List.lookup_cons] using choice

/-- The actual stored #methods array is kept separate from ordinary read
layout. This ties the same rows to the target's private slot, rather than
allowing a caller to supply an unrelated abstract row list. -/
theorem body_inputs_layout_from_twoSource (before : State) (captureEnvironment : List (String × Value))
    (rows : List Value) (method : JSString) (collector keyBound : Nat) (records : List Record)
    (nodeParams : Nat) (parameterReceiver : Value) (initial : List Value)
    (closure : PrivateMethodClosure) (receiver : Value) (target stamp methods : Nat)
    (facts : TwoSource before captureEnvironment rows method collector keyBound records nodeParams parameterReceiver initial)
    (captured : closure.environment = captureEnvironment)
    (storage : NodePrivateCall.Storage before closure target stamp methods collector rows) :
    MethodsLoop.Inputs (NodePrivateCall.bodyState before closure receiver collector target method nodeParams parameterReceiver)
      target stamp methods collector rows method ∧
    Layout (NodePrivateCall.bodyState before closure receiver collector target method nodeParams parameterReceiver)
      rows method collector keyBound records parameterReceiver nodeParams initial :=
  ⟨NodePrivateCall.body_inputs before closure receiver target stamp methods collector rows method nodeParams parameterReceiver storage,
    body_layout_from_twoSource before captureEnvironment rows method collector keyBound records nodeParams parameterReceiver initial
      closure receiver target facts captured⟩

/-- An allocated new parameter object cannot be any old mutable handler. No
caller-supplied guessed q/reference-separation premise is needed. -/
theorem fresh_parameter_protected {before after : State} {captureEnvironment : List (String × Value)}
    {rows : List Value} {method : JSString} {collector keyBound : Nat} {records : List Record} {initial : List Value}
    (frame : TwoSourceFrame before captureEnvironment rows method collector keyBound records initial)
    (growth : before.objects.length < after.objects.length) : Protected after records before.objects.length := by
  refine ⟨growth, ?_⟩
  intro record member
  have old := (List.getElem?_eq_some_iff.mp (frame.recordsFound record member).found).1
  omega

/-- Source123 and the ordinary guard allocate/change only the fresh q. This
transport accepts their proved current object/array/function frames. The new
object is explicit in the endpoint equality; no read matrix or body Layout is
presupposed. Any parent of that fresh object must be an old protected root. -/
theorem frame_after_fresh_object (before after : State) (captureEnvironment : List (String × Value))
    (rows : List Value) (method : JSString) (collector keyBound : Nat) (records : List Record) (initial : List Value)
    (freshObject : OrdinaryObject)
    (frame : TwoSourceFrame before captureEnvironment rows method collector keyBound records initial)
    (objects : after.objects = before.objects ++ [freshObject])
    (arrays : after.heap = before.heap) (functions : after.functions = before.functions)
    (parents : ∀ parent, freshObject.prototype = some parent → Protected before records parent) :
    TwoSourceFrame after captureEnvironment rows method collector keyBound records initial := by
  have length : after.objects.length = before.objects.length + 1 := by simp [objects]
  have oldFrame : ∀ reference, reference < before.objects.length → after.objects[reference]? = before.objects[reference]? := by
    intro reference inside
    rw [objects, List.getElem?_append_left inside]
  have safe : ∀ reference, Protected before records reference → Protected after records reference := by
    intro reference prior
    have bound := prior.1
    exact ⟨by omega, prior.2⟩
  have newFound : after.objects[before.objects.length]? = some freshObject := by simp [objects]
  have closed : NodeParamLoop.PrototypeClosed after.objects after.objects.length := by
    intro reference inside object found parent prototype
    change reference < after.objects.length at inside
    by_cases earlier : reference < before.objects.length
    · have oldFound : before.objects[reference]? = some object := (oldFrame reference earlier).symm.trans found
      have prior := frame.closed reference earlier object oldFound parent prototype
      change parent < before.objects.length at prior
      change parent < after.objects.length
      exact Nat.lt_of_lt_of_le prior (by omega)
    · have same : reference = before.objects.length := by omega
      subst reference
      cases Option.some.inj (newFound.symm.trans found)
      exact (safe parent (parents parent prototype)).1
  refine {
    allBinding := frame.allBinding
    helper := ?_
    collectorFound := by simpa [arrays] using frame.collectorFound
    capacity := frame.capacity
    closed := closed
    protectedParents := ?_
    recordsFound := ?_
    handlerParents := fun record member parent prototype => safe parent (frame.handlerParents record member parent prototype)
    rowChoices := ?_ }
  · obtain ⟨reference, helperEnvironment, binding, found, standard⟩ := frame.helper
    exact ⟨reference, helperEnvironment, binding, by simpa [functions] using found, by simpa [StandardObjectBinding] using standard⟩
  · intro reference protectedReference object found parent prototype
    by_cases earlier : reference < before.objects.length
    · have oldProtected : Protected before records reference := ⟨earlier, protectedReference.2⟩
      have oldFound : before.objects[reference]? = some object := (oldFrame reference earlier).symm.trans found
      exact safe parent (frame.protectedParents reference oldProtected object oldFound parent prototype)
    · have same : reference = before.objects.length := by have := protectedReference.1; omega
      subst reference
      cases Option.some.inj (newFound.symm.trans found)
      exact safe parent (parents parent prototype)
  · intro record member
    have shape := frame.recordsFound record member
    have inside := (List.getElem?_eq_some_iff.mp shape.found).1
    have lookup := NodeParamLoop.lookupProperty_frame propertyFuel before.objects after.objects before.objects.length
      (fun reference bound => (oldFrame reference bound).symm) frame.closed record.reference inside NodeParamAssignment.paramsKey
    refine ⟨(oldFrame record.reference inside).trans shape.found, shape.possibleKeys,
      by simpa [arrays] using shape.keysFound, shape.separate, ?_, shape.unique, shape.legalKeys, shape.keyBound⟩
    exact ⟨by simpa [← lookup] using shape.resettable.1, shape.resettable.2⟩
  · intro count inside
    obtain ⟨row, chosen, atRow, safeRow, choice, admitted⟩ := frame.rowChoices count inside
    refine ⟨row, chosen, atRow, safe row safeRow, ?_, admitted⟩
    have get := NodeParamLoop.getProperty_frame propertyFuel before.objects after.objects before.objects.length
      (fun reference bound => (oldFrame reference bound).symm) frame.closed row safeRow.1
    simpa only [SearchEntry.Choice, capturedView, ← get] using choice

/-- Initial parent reads survive allocation/guard writes to a new q. This
supports deriving the two-source matrix from actual source-copy/guard facts. -/
theorem lookup_after_fresh_object (fuel : Nat) (before after : State) (reference : Nat) (key : JSString)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (inside : reference < before.objects.length)
    (oldObjects : ∀ current, current < before.objects.length → after.objects[current]? = before.objects[current]?) :
    lookupProperty fuel after.objects reference key = lookupProperty fuel before.objects reference key :=
  (NodeParamLoop.lookupProperty_frame fuel before.objects after.objects before.objects.length
    (fun current bound => (oldObjects current bound).symm) closed reference inside key).symm

/-- For inherited accessors, this transports an OLD receiver's Get. Constructing
a fresh q's Get instead uses the descriptor lookup above and q as receiver. -/
theorem get_after_fresh_object (fuel : Nat) (before after : State) (reference : Nat) (key : JSString)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (inside : reference < before.objects.length)
    (oldObjects : ∀ current, current < before.objects.length → after.objects[current]? = before.objects[current]?) :
    getProperty fuel after.objects reference key = getProperty fuel before.objects reference key :=
  (NodeParamLoop.getProperty_frame fuel before.objects after.objects before.objects.length
    (fun current bound => (oldObjects current bound).symm) closed reference inside key).symm

/-- Read functions are observations supplied only after actual map creation
and capture have determined them. Replacing them does not change any record,
key snapshot, row, collector or protected-reference condition. -/
def withReadValues (record : Record) (parameter node : JSString → Value) : Record :=
  {record with snapshot := ⟨record.snapshot.keys, parameter, node⟩}

def revalueRecords (records : List Record) (parameter node : Record → JSString → Value) : List Record :=
  records.map (fun record => withReadValues record (parameter record) (node record))

theorem protected_revalueRecords (before : State) (records : List Record)
    (parameter node : Record → JSString → Value) (reference : Nat) :
    Protected before (revalueRecords records parameter node) reference ↔ Protected before records reference := by
  constructor
  · intro safe
    refine ⟨safe.1, ?_⟩
    intro record member
    exact safe.2 (withReadValues record (parameter record) (node record)) (List.mem_map.mpr ⟨record, member, rfl⟩)
  · intro safe
    refine ⟨safe.1, ?_⟩
    intro record member
    obtain ⟨original, used, rfl⟩ := List.mem_map.mp member
    exact safe.2 original used

theorem recordFacts_withReadValues (before : State) (collector keyBound : Nat) (record : Record)
    (parameter node : JSString → Value) (facts : TwoSourceRecordFacts before collector keyBound record) :
    TwoSourceRecordFacts before collector keyBound (withReadValues record parameter node) :=
  ⟨facts.found, facts.possibleKeys, facts.keysFound, facts.separate, facts.resettable,
    facts.unique, facts.legalKeys, facts.keyBound⟩

theorem frame_withReadValues (before : State) (captureEnvironment : List (String × Value))
    (rows : List Value) (method : JSString) (collector keyBound : Nat) (records : List Record) (initial : List Value)
    (parameter node : Record → JSString → Value)
    (frame : TwoSourceFrame before captureEnvironment rows method collector keyBound records initial) :
    TwoSourceFrame before captureEnvironment rows method collector keyBound (revalueRecords records parameter node) initial := by
  have safe := protected_revalueRecords before records parameter node
  refine {
    allBinding := frame.allBinding
    helper := frame.helper
    collectorFound := frame.collectorFound
    capacity := frame.capacity
    closed := frame.closed
    protectedParents := ?_
    recordsFound := ?_
    handlerParents := ?_
    rowChoices := ?_ }
  · intro reference protectedReference object found parent prototype
    exact (safe parent).mpr (frame.protectedParents reference ((safe reference).mp protectedReference) object found parent prototype)
  · intro record member
    obtain ⟨original, used, rfl⟩ := List.mem_map.mp member
    exact recordFacts_withReadValues before collector keyBound original _ _ (frame.recordsFound original used)
  · intro record member parent prototype
    obtain ⟨original, used, rfl⟩ := List.mem_map.mp member
    exact (safe parent).mpr (frame.handlerParents original used parent prototype)
  · intro count inside
    obtain ⟨row, chosen, atRow, safeRow, choice, admitted⟩ := frame.rowChoices count inside
    refine ⟨row, chosen, atRow, (safe row).mpr safeRow, choice, ?_⟩
    intro truth
    obtain ⟨record, member, selected⟩ := admitted truth
    exact ⟨withReadValues record (parameter record) (node record), List.mem_map.mpr ⟨record, member, rfl⟩, selected⟩

end HonoLean.Upstream.MethodsLoopInitial
