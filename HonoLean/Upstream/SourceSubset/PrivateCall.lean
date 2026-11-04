import HonoLean.Upstream.SourceSubset.MethodParser
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset

/-- Immutable value/private-name capture for the admitted method body subset.
Live lexical cells, home objects/super and full native closure creation remain
separate obligations. The actual method declaration supplies program. -/
structure PrivateMethodClosure where
  program : PrivateMethod
  environment : List (String × Value) := []
  privateNames : List (String × Nat) := []
  deriving Repr

/-- Function reference IDs base+i identify block-method closures. The runner
requires base >= State.functions.length, explicitly separating these identities
from the old zero-argument expression-function table. This is a call-entry
extension, not a proof of arbitrary nested or native function invocation. -/
structure PrivateMethodTable where
  base : Nat
  entries : List PrivateMethodClosure
  deriving Repr

structure PrivateCallContext where
  thisValue : Value
  deriving Repr

structure MethodActivation where
  state : State
  thisValue : Value
  deriving Repr

def parameterBindings (program : PrivateMethod) (arguments : List Value) : List (String × Value) :=
  program.parameters.zipIdx.map (fun (parameter, index) => (parameter.name, arguments[index]?.getD .undefined))

def methodActivation (closure : PrivateMethodClosure) (receiver : Value)
    (arguments : List Value) (before : State) : MethodActivation :=
  ⟨{before with
      environment := parameterBindings closure.program arguments ++ closure.environment
      thisValue := receiver
      privates := {before.privates with names := closure.privateNames}}, receiver⟩

def restoreMethodCaller (before after : State) : State :=
  {after with
    environment := before.environment
    thisValue := before.thisValue
    privates := {after.privates with names := before.privates.names}}

/-- Completion does not obey the TypeScript result annotation: a normal body
returns undefined, while an explicit return retains its actual value. Caller
bindings/private scope are restored after body effects; error-state traces are
not represented by Except. Supported method-body this reads use the dynamic
receiver installed in the activation state. -/
def invokePrivateClosure (fuel limit : Nat) (closure : PrivateMethodClosure)
    (receiver : Value) (arguments : List Value) (before : State) : Except EvalError (Value × State) := do
  let activation := methodActivation closure receiver arguments before
  match ← runBlock fuel closure.program.body activation.state limit with
  | .normal after => pure (.undefined, restoreMethodCaller before after)
  | .returned value after => pure (value, restoreMethodCaller before after)

def resolvePrivateMethod (table : PrivateMethodTable) (callee : Value) : Except EvalError PrivateMethodClosure :=
  match callee with
  | .function reference =>
    if reference < table.base then .error .unsupported else
    match table.entries[reference - table.base]? with
    | some closure => .ok closure
    | none => .error .invalidReference
  | _ => .error .unsupported

def evalMethodReceiver (fuel limit : Nat) (context : PrivateCallContext) :
    MethodReceiver → State → Except EvalError (Value × State)
  | .this, before => .ok (context.thisValue, before)
  | .expression value, before => evalExpression fuel limit value before

/-- Added top-level private-method call rule. Receiver/private Get precede
left-to-right argument effects. Callable/table resolution occurs afterward,
using the captured callee and receiver. The old expression evaluator is not
silently broadened to nested block-method calls. -/
def runPrivateMethodCall (fuel limit : Nat) (table : PrivateMethodTable)
    (context : PrivateCallContext) (call : PrivateMethodCall) (before : State) :
    Except EvalError (Value × State) := do
  if table.base < before.functions.length then .error .unsupported else do
  let (receiver, state) ← evalMethodReceiver fuel limit context call.receiver before
  let callee ← privateGet receiver call.spelling state
  let (arguments, state) ← evalArguments fuel limit call.arguments state
  let closure ← resolvePrivateMethod table callee
  invokePrivateClosure fuel limit closure receiver arguments state

theorem activation_this (closure : PrivateMethodClosure) (receiver : Value)
    (arguments : List Value) (before : State) :
    (methodActivation closure receiver arguments before).thisValue = receiver := rfl

theorem activation_state_this (closure : PrivateMethodClosure) (receiver : Value)
    (arguments : List Value) (before : State) :
    (methodActivation closure receiver arguments before).state.thisValue = receiver := rfl

theorem activation_private_names (closure : PrivateMethodClosure) (receiver : Value)
    (arguments : List Value) (before : State) :
    (methodActivation closure receiver arguments before).state.privates.names = closure.privateNames := rfl

theorem parameterBindings_length (program : PrivateMethod) (arguments : List Value) :
    (parameterBindings program arguments).length = program.parameters.length := by
  simp [parameterBindings]

theorem parameterBindings_at (program : PrivateMethod) (arguments : List Value) (index : Nat)
    (inside : index < program.parameters.length) :
    (parameterBindings program arguments)[index]? =
      some ((program.parameters[index]).name, arguments[index]?.getD .undefined) := by
  simp [parameterBindings, List.getElem?_eq_getElem inside]

theorem restoreMethodCaller_environment (before after : State) :
    (restoreMethodCaller before after).environment = before.environment := rfl

theorem restoreMethodCaller_this (before after : State) :
    (restoreMethodCaller before after).thisValue = before.thisValue := rfl

theorem restoreMethodCaller_private_names (before after : State) :
    (restoreMethodCaller before after).privates.names = before.privates.names := rfl

theorem restoreMethodCaller_heap (before after : State) :
    (restoreMethodCaller before after).heap = after.heap := rfl

theorem invokePrivateClosure_normal (fuel limit : Nat) (closure : PrivateMethodClosure)
    (receiver : Value) (arguments : List Value) (before after : State)
    (body : runBlock fuel closure.program.body (methodActivation closure receiver arguments before).state limit =
      .ok (.normal after)) :
    invokePrivateClosure fuel limit closure receiver arguments before =
      .ok (.undefined, restoreMethodCaller before after) := by
  simp [invokePrivateClosure, body, bind, Except.bind, pure, Except.pure]

theorem invokePrivateClosure_returned (fuel limit : Nat) (closure : PrivateMethodClosure)
    (receiver value : Value) (arguments : List Value) (before after : State)
    (body : runBlock fuel closure.program.body (methodActivation closure receiver arguments before).state limit =
      .ok (.returned value after)) :
    invokePrivateClosure fuel limit closure receiver arguments before =
      .ok (value, restoreMethodCaller before after) := by
  simp [invokePrivateClosure, body, bind, Except.bind, pure, Except.pure]

theorem runPrivateMethodCall_this (fuel limit : Nat) (table : PrivateMethodTable)
    (receiver : Value) (spelling : String) (expressions : List Expr)
    (before argumentsState : State) (arguments : List Value)
    (reference : Nat) (closure : PrivateMethodClosure)
    (separated : before.functions.length ≤ table.base)
    (captured : privateGet receiver spelling before = .ok (.function reference))
    (evaluated : evalArguments fuel limit expressions before = .ok (arguments, argumentsState))
    (referenceBound : table.base ≤ reference)
    (found : table.entries[reference - table.base]? = some closure) :
    runPrivateMethodCall fuel limit table ⟨receiver⟩ ⟨.this, spelling, expressions⟩ before =
      invokePrivateClosure fuel limit closure receiver arguments argumentsState := by
  simp [runPrivateMethodCall, Nat.not_lt.mpr separated, evalMethodReceiver, captured, evaluated,
    resolvePrivateMethod, Nat.not_lt.mpr referenceBound, found, bind, Except.bind]

end HonoLean.Upstream.SourceSubset
