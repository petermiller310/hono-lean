import HonoLean.Upstream.MethodsLoop.Correctness

namespace HonoLean.Upstream.MethodsLoopInitial

open SourceSubset ECMA2025

/-- A handler's initial cell and immutable key snapshot. Repeated method rows
may refer to the same descriptor/reference. -/
structure Record where
  reference : ObjectRef
  object : OrdinaryObject
  keysArray : Nat
  snapshot : NodeParamLoop.Snapshot

/-- A protected cell is already allocated and is distinct from every mutable
handler cell. Returned values may still be aliases; this constrains read cells,
not the identities stored as their values. -/
def Protected (origin : State) (records : List Record) (reference : Nat) : Prop :=
  reference < origin.objects.length ∧ ∀ record ∈ records, reference ≠ record.reference

structure RecordFacts (origin : State) (collector keyBound : Nat)
    (parameterReceiver : Value) (nodeParams : Nat) (record : Record) : Prop where
  found : origin.objects[record.reference]? = some record.object
  possibleKeys : record.object.own.lookup NodeParamLoop.possibleKeysKey =
    some (.data (.array record.keysArray) true true true)
  keysFound : origin.heap[record.keysArray]? = some (record.snapshot.keys.map Value.string)
  separate : collector ≠ record.keysArray
  resettable : NodeParamLoop.Resettable origin.objects record.reference record.object
  unique : record.snapshot.keys.Nodup
  legalKeys : record.snapshot.keys.length ≤ 4294967295
  keyBound : record.snapshot.keys.length ≤ keyBound
  reads : ∀ key ∈ record.snapshot.keys,
    NodeParamAssignment.ParameterRead origin key parameterReceiver (record.snapshot.parameter key) ∧
    getProperty propertyFuel origin.objects nodeParams key = .ok (record.snapshot.node key)

/-- One-state structural domain. Every field concerns initial bindings, cells,
descriptors, lookup chains, list sizes or initial property reads. No Processed,
NormalPrefixes, later Entry or evaluator-success premise occurs here. -/
structure Layout (origin : State) (rows : List Value) (method : JSString)
    (collector keyBound : Nat) (records : List Record) (parameterReceiver : Value)
    (nodeParams : Nat) (initial : List Value) : Prop where
  collectorBinding : origin.environment.lookup "handlerSets" = some (.array collector)
  parameterBinding : origin.environment.lookup "params" = some parameterReceiver
  nodeBinding : origin.environment.lookup "nodeParams" = some (.object nodeParams)
  allBinding : SearchEntry.AllImportBinding origin
  helper : ∃ reference environment,
    origin.environment.lookup "createNullObject" = some (.function reference) ∧
    origin.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩ ∧
    StandardObjectBinding {origin with environment}
  collectorFound : origin.heap[collector]? = some initial
  capacity : initial.length + rows.length ≤ 4294967295
  closed : NodeParamLoop.PrototypeClosed origin.objects origin.objects.length
  protectedParents : ∀ reference, Protected origin records reference →
    ∀ object, origin.objects[reference]? = some object →
    ∀ parent, object.prototype = some parent → Protected origin records parent
  nodeProtected : Protected origin records nodeParams
  parameterProtected : ∀ reference, parameterReceiver = .object reference → Protected origin records reference
  recordsFound : ∀ record ∈ records, RecordFacts origin collector keyBound parameterReceiver nodeParams record
  handlerParents : ∀ record ∈ records, ∀ parent,
    record.object.prototype = some parent → Protected origin records parent
  rowChoices : ∀ count, count < rows.length → ∃ row chosen,
    rows[count]? = some (.object row) ∧ Protected origin records row ∧
    SearchEntry.Choice origin row method chosen ∧
    (NodeParamAssignment.Truthy chosen → ∃ record ∈ records, chosen = .object record.reference)

/-- Mutable handler shape after zero or more captures. The ordinary fields
needed by capture and the prototype are stable; params is initially unchanged
or a newly installed writable/enumerable/configurable own data field. -/
def Shape (record : Record) (object : OrdinaryObject) : Prop :=
  object.prototype = record.object.prototype ∧ object.extensible = record.object.extensible ∧
  object.own.lookup NodeParamLoop.possibleKeysKey = record.object.own.lookup NodeParamLoop.possibleKeysKey ∧
  (object = record.object ∨ ∃ value,
    object.own.lookup NodeParamAssignment.paramsKey = some (.data value true true true))

structure Invariant (origin before : State) (collector : Nat) (records : List Record) : Prop where
  oldBound : origin.objects.length ≤ before.objects.length
  protectedFrame : ∀ reference, Protected origin records reference →
    before.objects[reference]? = origin.objects[reference]?
  arrays : ∀ reference, reference ≠ collector → before.heap[reference]? = origin.heap[reference]?
  functions : before.functions = origin.functions
  closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length
  handlers : ∀ record ∈ records, ∃ object,
    before.objects[record.reference]? = some object ∧ Shape record object

end HonoLean.Upstream.MethodsLoopInitial
