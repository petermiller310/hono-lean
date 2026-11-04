import HonoLean.Upstream.NodePrivateCall.Program
import HonoLean.Upstream.SourceSubset.PrivateCall
import HonoLean.Upstream.MethodsLoopInitial.Correctness

namespace HonoLean.Upstream.NodePrivateCall

open SourceSubset ECMA2025

def fourValues (collector target : Nat) (method : JSString) (nodeParams : Nat) : List Value :=
  [.array collector, .object target, .string method, .object nodeParams]

def fiveValues (collector target : Nat) (method : JSString) (nodeParams : Nat)
    (parameterReceiver : Value) : List Value :=
  [.array collector, .object target, .string method, .object nodeParams, parameterReceiver]

/-- The independent parameter environment follows the five source formal names
in order. The last value is undefined for the actual four-argument call. -/
def bodyState (before : State) (closure : PrivateMethodClosure) (receiver : Value) (collector target : Nat)
    (method : JSString) (nodeParams : Nat) (parameterReceiver : Value) : State :=
  {before with
    thisValue := receiver
    environment := [("handlerSets", .array collector), ("node", .object target),
      ("method", .string method), ("nodeParams", .object nodeParams), ("params", parameterReceiver)] ++ closure.environment
    privates := {before.privates with names := closure.privateNames}}

/-- Initial heap/private storage, independent of method-body execution and of
the body-local variable bindings which the source call will establish. -/
structure Storage (before : State) (closure : PrivateMethodClosure)
    (target stamp methods collector : Nat) (rows : List Value) : Prop where
  targetFound : ∃ object, before.objects[target]? = some object
  privateName : closure.privateNames.lookup "methods" = some stamp
  privateSlot : ∃ fields, before.privates.slots.lookup target = some fields ∧
    fields.lookup stamp = some (.array methods)
  methodsFound : before.heap[methods]? = some rows
  separate : collector ≠ methods
  legalLength : rows.length ≤ 4294967295

/-- Explicit source-bound read handle. Full native private-method creation,
installation/read-only enforcement and class/module linking remain open.
The function-ID partition is a model representation condition, not a Hono
behavior assumption. No successful body execution or final result is supplied. -/
structure Callable (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle : Nat) : Prop where
  sourceProgram : closure.program = methodProgram
  tableSeparate : before.functions.length ≤ table.base
  handleBound : table.base ≤ handle
  closureFound : table.entries[handle - table.base]? = some closure
  privateRead : privateGet (.object receiver) "pushHandlerSets" before = .ok (.function handle)

structure FourReads (before : State) (collector target : Nat) (method : JSString)
    (nodeParams : Nat) : Prop where
  collectorBinding : before.environment.lookup "handlerSets" = some (.array collector)
  targetBinding : before.environment.lookup "nextNode" = some (.object target)
  methodBinding : before.environment.lookup "method" = some (.string method)
  callerNode : ∃ value, before.environment.lookup "node" = some value ∧
    privateGet value "params" before = .ok (.object nodeParams)

structure FiveReads (before : State) (collector target : Nat) (method : JSString)
    (nodeParams : Nat) (parameterReceiver : Value) : Prop where
  collectorBinding : before.environment.lookup "handlerSets" = some (.array collector)
  targetBinding : before.environment.lookup "child" = some (.object target)
  methodBinding : before.environment.lookup "method" = some (.string method)
  parameterBinding : before.environment.lookup "params" = some (.object nodeParams)
  callerNode : ∃ value, before.environment.lookup "node" = some value ∧
    privateGet value "params" before = .ok parameterReceiver

/-- Independent ordered loop contract plus normal method return and exact
caller lexical/private-scope restoration. Heap effects belong to the body.
The contract does not identify success with the call evaluator's output. -/
def CallContract (before origin : State) (rows : List Value) (method : JSString)
    (collector : Nat) (returned : Value) (after : State) : Prop :=
  returned = .undefined ∧ ∃ bodyAfter,
    MethodsLoop.LoopContract origin bodyAfter rows method collector ∧
    after = restoreMethodCaller before bodyAfter

end HonoLean.Upstream.NodePrivateCall
