import HonoLean.Upstream.NodeExecCall.Source
import HonoLean.Upstream.NodeCaptureGuard.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.NodeExecCall
open SourceSubset ECMA2025

def execKey : JSString := [101, 120, 101, 99]

/-- Initial current property descriptors and known closure tables. The data
callee can be own or inherited and may differ at each activation. No match,
callee Get result, completed call or future body success is supplied. These
ordinary source closures are not builtin RegExp implementations. -/
structure Inputs (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (closure : MemberClosure) (matcher handle : Nat) (input : JSString) : Prop where
  matcherBinding : before.environment.lookup "matcher" = some (.object matcher)
  inputBinding : before.environment.lookup "restPathString" = some (.string input)
  current : ∃ writable enumerable configurable depth,
    NodeCaptureGuard.DescriptorPath before.objects execKey matcher (some (.data (.function handle) writable enumerable configurable)) depth ∧ depth ≤ propertyFuel
  noArgBefore : before.functions.length ≤ members.base
  privateBefore : methods.base + methods.entries.length ≤ members.base
  functionsBefore : functions.base + functions.entries.length ≤ members.base
  handleBound : members.base ≤ handle
  closureFound : members.entries[handle - members.base]? = some closure

/-- Small, actual source-defined computations used to prove useful outputs.
This is a body AST classification, not an exec-spelling builtin or a regex
oracle. The parameter, null, receiver and two allocated-array returns remain
native-distinct values; normal completion returns undefined. -/
inductive BodyShape where
  | argument | nullResult | receiverResult | singleton | emptyArray | fallthrough
  deriving Repr, DecidableEq

def shapeBody (shape : BodyShape) (parameter : String) : List Stmt :=
  match shape with
  | .argument => [.ret (.variable parameter)]
  | .nullResult => [.ret .null]
  | .receiverResult => [.ret .this]
  | .singleton => [.ret (.arrayLiteral [(false, .variable parameter)])]
  | .emptyArray => [.ret (.arrayLiteral [])]
  | .fallthrough => []

def returnedValue (shape : BodyShape) (before : State) (matcher : Nat) (input : JSString) : Value :=
  match shape with
  | .argument => .string input
  | .nullResult => .null
  | .receiverResult => .object matcher
  | .singleton | .emptyArray => .array before.heap.length
  | .fallthrough => .undefined

def returnedHeap (shape : BodyShape) (before : State) (input : JSString) : List (List Value) :=
  match shape with
  | .singleton => before.heap ++ [[.string input]]
  | .emptyArray => before.heap ++ [[]]
  | _ => before.heap

def callState (shape : BodyShape) (before : State) (input : JSString) : State :=
  {before with heap := returnedHeap shape before input}

def resultState (shape : BodyShape) (before : State) (matcher : Nat) (input : JSString) : State :=
  {callState shape before input with environment := ("m", returnedValue shape before matcher input) :: before.environment}

/-- Primitive phase relation, independent of the source-declaration runner.
The SAME original matcher and saved current callee precede the argument, then
activate the actually selected body with dynamic this and the argument value.
BodyExecution is operational evidence of that body, not a regex specification. -/
structure CallPhases (fuel : Nat) (before after : State) (closure : MemberClosure) (matcher handle : Nat)
    (input : JSString) (returned : Value) : Prop where
  receiverFirst : evalExpression fuel defaultSplitLimit receiver before = .ok (.object matcher, before)
  calleeBeforeArgument : prepareMethod (.object matcher) "exec" before = .ok (.member (.object matcher) (.function handle))
  argumentNext : evalArguments fuel defaultSplitLimit arguments before = .ok ([.string input], before)
  bodyExecuted : MemberBodyExecution fuel defaultSplitLimit closure (.object matcher) [.string input] before returned after

/-- Independent observable output facts accompany the operational phases.
The result retains the actual Value, a fresh singleton/empty array when the
body allocates it, exact old cells and the caller's scope/private/this frame. -/
structure Contract (fuel : Nat) (before after : State) (closure : MemberClosure) (matcher handle : Nat)
    (input : JSString) (shape : BodyShape) : Prop where
  program : closure.program.body = shapeBody shape closure.program.parameter
  phases : CallPhases fuel before (callState shape before input) closure matcher handle input (returnedValue shape before matcher input)
  mBinding : after.environment.lookup "m" = some (returnedValue shape before matcher input)
  environment : after.environment = ("m", returnedValue shape before matcher input) :: before.environment
  heap : after.heap = returnedHeap shape before input
  oldArrays : ∀ reference, reference < before.heap.length → after.heap[reference]? = before.heap[reference]?
  objects : after.objects = before.objects
  functions : after.functions = before.functions
  privates : after.privates = before.privates
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

def resultTruthy (shape : BodyShape) (input : JSString) : Bool :=
  match shape with
  | .argument => !input.isEmpty
  | .nullResult | .fallthrough => false
  | .receiverResult | .singleton | .emptyArray => true

end HonoLean.Upstream.NodeExecCall
