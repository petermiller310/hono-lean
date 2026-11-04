import HonoLean.Upstream.NodeCaptureGuard.Source
import HonoLean.Upstream.ECMA2025.DenseArray

set_option autoImplicit false

namespace HonoLean.Upstream.NodeCaptureGuard
open SourceSubset ECMA2025

/-- A finite before-state descriptor path. Every step records actual object,
own lookup and prototype facts; this is not a successful evaluator premise.
The explicit depth bound supplies the model's prototype traversal budget. -/
inductive DescriptorPath (heap : ObjectHeap) (key : JSString) : Nat → Option PropertyDescriptor → Nat → Prop where
  | own {reference object descriptor} (found : heap[reference]? = some object)
      (property : object.own.lookup key = some descriptor) : DescriptorPath heap key reference (some descriptor) 1
  | absent {reference object} (found : heap[reference]? = some object)
      (property : object.own.lookup key = none) (prototype : object.prototype = none) : DescriptorPath heap key reference none 1
  | parent {reference object parent descriptor depth} (found : heap[reference]? = some object)
      (property : object.own.lookup key = none) (prototype : object.prototype = some parent)
      (rest : DescriptorPath heap key parent descriptor depth) : DescriptorPath heap key reference descriptor (depth + 1)

structure HeaderInputs (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString) : Prop where
  standardObject : StandardObjectBinding before
  paramsBinding : before.environment.lookup "params" = some (.object params)
  nameBinding : before.environment.lookup "name" = some (.string name)
  found : before.objects[params]? = some object
  wellFormed : WellFormedObject object

/-- Any own descriptor suppresses capture, including undefined/falsy values,
nonenumerable/readonly data and accessors. No m or writable-field input. -/
structure OwnInputs (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (descriptor : PropertyDescriptor) : Prop extends HeaderInputs before params object name where
  own : object.own.lookup name = some descriptor

/-- Match production remains an explicit input boundary. These are actual
initial array/index facts, never a desired future match or successful Set. -/
structure AbsentInputs (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    : Prop extends HeaderInputs before params object name where
  absent : object.own.lookup name = none
  matchedBinding : before.environment.lookup "m" = some (.array matched)
  matchedFound : before.heap[matched]? = some values
  captured : values[0]? = some (.string captured)
  lengthBound : values.length ≤ maximumArrayLength
  path : DescriptorPath before.objects name params descriptor depth
  pathBound : depth ≤ propertyFuel

inductive Action where
  | create | ignore | reject (error : ObjectError) | unsupported
  deriving Repr, DecidableEq

/-- Independent descriptor classification. Unsupported custom setters are a
model boundary, not a theorem of native rejection. A primitive string invokes the
standard legacy prototype setter without changing prototypes or own data. -/
def action (descriptor : Option PropertyDescriptor) (extensible : Bool) : Action :=
  match descriptor with
  | none | some (.data _ true _ _) => if extensible then .create else .reject .notExtensible
  | some (.data _ false _ _) => .reject .notWritable
  | some (.accessor _ .prototype _ _) => .ignore
  | some (.accessor _ .missing _ _) => .reject .notWritable
  | some (.accessor _ .unsupported _ _) => .unsupported

def writtenState (before : State) (params : Nat) (object : OrdinaryObject) (name captured : JSString) : State :=
  {before with objects := before.objects.set params (newDataObject object name (.string captured))}

/-- Exact one-cell own-data outcome and separate observable/frame facts. It
never calls source execute, Object.hasOwn, descriptor lookup or Set. -/
structure CreatedContract (before after : State) (params : Nat) (object : OrdinaryObject) (name captured : JSString) : Prop where
  heap : after.objects = before.objects.set params (newDataObject object name (.string captured))
  own : ∃ updated, after.objects[params]? = some updated ∧
    updated.own.lookup name = some (.data (.string captured) true true true) ∧ updated.prototype = object.prototype
  otherObjects : ∀ reference, reference ≠ params → after.objects[reference]? = before.objects[reference]?
  environment : after.environment = before.environment
  arrays : after.heap = before.heap
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

/-- The final relation retains the actual initial descriptor/match provenance;
its outcome cases are independent structural observations, not evaluator calls. -/
inductive GuardContract (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString) :
    Except EvalError Completion → Prop where
  | skipped (descriptor : PropertyDescriptor) (initial : OwnInputs before params object name descriptor) :
      GuardContract before params object name (.ok (.normal before))
  | created (matched values captured descriptor depth)
      (initial : AbsentInputs before params object name matched values captured descriptor depth)
      (classified : action descriptor object.extensible = .create) (after : State)
      (result : CreatedContract before after params object name captured) : GuardContract before params object name (.ok (.normal after))
  | ignored (matched values captured descriptor depth)
      (initial : AbsentInputs before params object name matched values captured descriptor depth)
      (classified : action descriptor object.extensible = .ignore) : GuardContract before params object name (.ok (.normal before))
  | rejected (matched values captured descriptor depth)
      (initial : AbsentInputs before params object name matched values captured descriptor depth)
      (error : ObjectError) (classified : action descriptor object.extensible = .reject error) :
      GuardContract before params object name (.error (.objectError error))
  | unsupported (matched values captured descriptor depth)
      (initial : AbsentInputs before params object name matched values captured descriptor depth)
      (classified : action descriptor object.extensible = .unsupported) :
      GuardContract before params object name (.error (.objectError .unsupported))

end HonoLean.Upstream.NodeCaptureGuard
