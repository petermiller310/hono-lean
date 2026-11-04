import HonoLean.Upstream.NodeCaptureCollect.Source
import HonoLean.Upstream.NodeParamsInit.Composition
import HonoLean.Upstream.MethodsLoopInitial.TwoSource
import HonoLean.Upstream.NodeLiteralBranch.Frames

set_option autoImplicit false
namespace HonoLean.Upstream.NodeCaptureCollect
open SourceSubset ECMA2025 MethodsLoopInitial

/-- Source-installed METHOD kind, closure body and current known-table handle.
No successful callee read/run or function-valued DATA heuristic is supplied. -/
structure Installed (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure) (receiver handle : Nat) where
  identity : Nat
  scope : before.privates.names.lookup "pushHandlerSets" = some identity
  receiverFound : ∃ object, before.objects[receiver]? = some object
  method : ∃ fields, before.privates.elements.lookup receiver = some fields ∧ fields.lookup identity = some (.method (.function handle))
  source : closure.program = NodePrivateCall.methodProgram
  separate : before.functions.length ≤ table.base
  handleBound : table.base ≤ handle
  closureFound : table.entries[handle - table.base]? = some closure

/-- Rows are the actual target #methods DATA-array contents. They cannot be
replaced by arbitrary existential empty rows in the independent result. -/
structure Storage (before : State) (closure : PrivateMethodClosure) (child slot methods collector : Nat) (rows : List Value) : Prop where
  childFound : ∃ object, before.objects[child]? = some object
  scope : closure.privateNames.lookup "methods" = some slot
  data : ∃ fields, before.privates.elements.lookup child = some fields ∧ fields.lookup slot = some (.data (.array methods))
  rowsFound : before.heap[methods]? = some rows
  separate : collector ≠ methods
  legal : rows.length ≤ 4294967295

structure CallReads (before : State) (receiver node parentIdentity child collector parent q : Nat) (query : JSString) : Prop where
  thisValue : before.thisValue = .object receiver
  collectorBinding : before.environment.lookup "handlerSets" = some (.array collector)
  childBinding : before.environment.lookup "child" = some (.object child)
  methodBinding : before.environment.lookup "method" = some (.string query)
  nodeBinding : before.environment.lookup "node" = some (.object node)
  parentData : NodePrivateWrite.Writable before node parentIdentity (.object parent)
  paramsBinding : before.environment.lookup "params" = some (.object q)

/-- Observable helper behavior is the existing ordered reset/push/capture
trace, now rooted at the actual161 positional sources. Collector entries remain
live record refs; this relation does not freeze prior capture snapshots. -/
structure Contract (before after : State) (closure : PrivateMethodClosure) (receiver child slot methods collector parent q : Nat)
    (rows initial : List Value) (query : JSString) : Prop where
  storage : NodePrivateCall.Storage before closure child slot methods collector rows
  called : NodePrivateCall.CallContract before (NodePrivateCall.bodyState before closure (.object receiver) collector child query parent (.object q))
    rows query collector .undefined after
  environment : after.environment = before.environment
  thisValue : after.thisValue = before.thisValue
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  allocation : before.objects.length ≤ after.objects.length
  arrays : ∀ reference, reference ≠ collector → after.heap[reference]? = before.heap[reference]?
  collector : ∃ selected : List Nat, after.heap[collector]? = some (initial ++ selected.map Value.object)

/-- Inherited lookup is specified with the ORIGINAL fresh receiver q. The
legacy getter therefore returns q's prototype0, not root0's prototype null. -/
inductive FreshInherited : Option PropertyDescriptor → Value → Prop where
  | absent : FreshInherited none .undefined
  | data (value : Value) (writable enumerable configurable : Bool) : FreshInherited (some (.data value writable enumerable configurable)) value
  | missing (setter : Setter) (enumerable configurable : Bool) : FreshInherited (some (.accessor .missing setter enumerable configurable)) .undefined
  | prototype (setter : Setter) (enumerable configurable : Bool) : FreshInherited (some (.accessor .prototype setter enumerable configurable)) (.object 0)

def mapValue (object : OrdinaryObject) (root : JSString → Value) (key : JSString) : Value :=
  match object.own.lookup key with | some (.data value _ _ _) => value | _ => root key

def RootReads (before : State) (records : List Record) (root : JSString → Value) : Prop :=
  ∀ record ∈ records, ∀ key ∈ record.snapshot.keys, ∃ descriptor depth,
    NodeCaptureGuard.DescriptorPath before.objects key 0 descriptor depth ∧ depth + 1 ≤ propertyFuel ∧ FreshInherited descriptor (root key)

def ParentReads (before : State) (records : List Record) (parent : Nat) : Prop :=
  ∀ record ∈ records, ∀ key ∈ record.snapshot.keys, getProperty propertyFuel before.objects parent key = .ok (record.snapshot.node key)

def readRecords (records : List Record) (object : OrdinaryObject) (root : JSString → Value) : List Record :=
  revalueRecords records (fun _ => mapValue object root) (fun record => record.snapshot.node)

end HonoLean.Upstream.NodeCaptureCollect
