import HonoLean.Upstream.NodeMethodsPush.Correctness
import HonoLean.Upstream.ECMA2025.StringSet

namespace HonoLean.Upstream.RegistrationHistory

open SourceSubset ECMA2025

/-- Caller-supplied registration data. The insertion traversal producing these
primitive string events is separate from the source push proved here. -/
structure Request where
  method : JSString
  handler : Value
  events : List JSString
  deriving Repr

def Request.keys (request : Request) : List JSString := StringSet.fromTrace request.events

/-- Separate caller activation and one supplied fresh Set cell. This transports
the current order binding rather than installing a desired next score. The Set
is an explicit supplied-event input, not a proof of insertion branch production. -/
def stage (before : State) (owner : Nat) (request : Request) : State :=
  {before with
    environment := [("curNode", .object owner), ("method", .string request.method),
      ("handler", request.handler), ("possibleKeys", .set before.sets.length)] ++
        withoutBindings before.environment ["curNode", "method", "handler", "possibleKeys"]
    sets := before.sets ++ [request.keys]}

structure Seed (before : State) (owner stamp methods : Nat) (order : Int) (prior : List Value) : Prop where
  orderBinding : before.environment.lookup "order" = some (.number order)
  rootFound : ∃ root, before.objects[0]? = some root
  ownerFound : ∃ object, before.objects[owner]? = some object
  privateName : before.privates.names.lookup "methods" = some stamp
  privateSlot : ∃ fields, before.privates.slots.lookup owner = some fields ∧ fields.lookup stamp = some (.array methods)
  methodsFound : before.heap[methods]? = some prior

def step (before : State) (owner methods : Nat) (order : Int) (prior : List Value) (request : Request) : State :=
  NodeMethodsPush.pushedState (stage before owner request) request.method request.handler request.keys order methods prior

/-- Independent storage construction, without invoking the source evaluator. -/
def endState : State → Nat → Nat → Int → List Value → List Request → State
  | before, _, _, _, _, [] => before
  | before, owner, methods, order, prior, request :: rest =>
    endState (step before owner methods order prior request) owner methods (order + 1)
      (prior ++ [.object before.objects.length]) rest

def storedRows : Nat → List Request → List Value
  | _, [] => []
  | objectBase, _ :: rest => .object objectBase :: storedRows (objectBase + 2) rest

def storedObjects : Nat → Nat → Int → List Request → List OrdinaryObject
  | _, _, _, [] => []
  | objectBase, arrayBase, order, request :: rest =>
    HandlerRecord.outerRecord request.method (objectBase + 1) ::
    HandlerRecord.innerRecord request.handler arrayBase (order + 1) ::
    storedObjects (objectBase + 2) (arrayBase + 1) (order + 1) rest

def keySnapshots (requests : List Request) : List (List Value) := requests.map (fun request => request.keys.map Value.string)

/-- Actual evaluation of the same exact pinned source push at each separate
caller activation. No desired storage result is an argument to this runner. -/
def runSourceHistory (source : Expr) (owner : Nat) : List Request → State → Except EvalError State
  | [], before => .ok before
  | request :: rest, before => do
    let (_, next) ← evalExpression 34 defaultSplitLimit source (stage before owner request)
    runSourceHistory source owner rest next

/-- Exact storage, reference-order, score and frame observations. The caller
activation environment is outside this endpoint except for its carried order.
Neither evaluator execution nor a future-entry predicate defines this contract. -/
structure HistoryContract (before after : State) (methods : Nat) (order : Int)
    (prior : List Value) (requests : List Request) : Prop where
  objects : after.objects = before.objects ++ storedObjects before.objects.length before.heap.length order requests
  heap : after.heap = (before.heap.set methods (prior ++ storedRows before.objects.length requests)) ++ keySnapshots requests
  sets : after.sets = before.sets ++ requests.map Request.keys
  functions : after.functions = before.functions
  privates : after.privates = before.privates
  orderBinding : after.environment.lookup "order" = some (.number (order + requests.length))

/-- Additional mathematical restrictions needed before interpreting the model
as successful native dense arrays/exact integer scores. Standard realm/iterator,
mutable-cell and resource adequacy remain separate interpretation obligations. -/
def NativeHistoryBounds (before : State) (order : Int) (prior : List Value) (requests : List Request) : Prop :=
  -9007199254740991 ≤ order ∧ order + requests.length ≤ 9007199254740991 ∧
  prior.length + requests.length ≤ 4294967295 ∧
  ∀ request ∈ requests, HandlerRecord.NativeBounds before request.method request.keys order

end HonoLean.Upstream.RegistrationHistory
