import HonoLean.Upstream.NodePatternBinding.Source
import HonoLean.Upstream.NodeCaptureGuard.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.NodePatternBinding
open SourceSubset ECMA2025

/-- OLD realm objects and current protocol identities, before the selected
binding. Finite descriptor paths include the complete inherited return lookup.
Only default DATA array iteration and a nullish Close are admitted here. -/
structure Realm (before : ArrayBindingState) (context : ArrayIteratorContext)
    (valuesHandle nextHandle : Nat) (returned : Value) : Prop where
  closed : IteratorPrototypeClosed before.regexp.ambient.objects
  arrayPrototypeFound : ∃ object, before.regexp.ambient.objects[context.arrayPrototype]? = some object
  iteratorPrototypeFound : ∃ object, before.regexp.ambient.objects[context.iteratorPrototype]? = some object
  resultPrototypeFound : ∃ object, before.regexp.ambient.objects[context.resultPrototype]? = some object
  symbol : symbolOwn before (.object context.arrayPrototype) = some (.data (.function valuesHandle) true false true)
  noArgBefore : before.regexp.ambient.functions.length ≤ context.builtins.base
  methodsBefore : context.constructors.methods.base + context.constructors.methods.entries.length ≤ context.builtins.base
  functionsBefore : context.constructors.functions.base + context.constructors.functions.entries.length ≤ context.builtins.base
  membersBefore : context.constructors.members.base + context.constructors.members.entries.length ≤ context.builtins.base
  regexpBefore : context.constructors.builtins.base + context.constructors.builtins.entries.length ≤ context.builtins.base
  constructorsBefore : context.constructors.constructors.base + context.constructors.constructors.entries.length ≤ context.builtins.base
  valuesBound : context.builtins.base ≤ valuesHandle
  valuesIdentity : context.builtins.entries[valuesHandle - context.builtins.base]? = some .arrayValues
  nextBound : context.builtins.base ≤ nextHandle
  nextIdentity : context.builtins.entries[nextHandle - context.builtins.base]? = some .arrayNext
  nextPath : ∃ depth, NodeCaptureGuard.DescriptorPath before.regexp.ambient.objects iteratorNextKey
    context.iteratorPrototype (some (.data (.function nextHandle) true false true)) depth ∧ depth ≤ propertyFuel - 1
  returnPath : ∃ descriptor depth, NodeCaptureGuard.DescriptorPath before.regexp.ambient.objects iteratorReturnKey
    context.iteratorPrototype descriptor depth ∧ depth ≤ propertyFuel - 1 ∧ IteratorPureRead descriptor returned
  nullish : returned = .undefined ∨ returned = .null

structure Inputs (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value) : Prop
    extends Realm before context valuesHandle nextHandle returned where
  binding : before.regexp.ambient.environment.lookup "pattern" = some (.array pattern)
  found : before.regexp.ambient.heap[pattern]? = some values
  three : 3 ≤ values.length
  lengthBound : values.length ≤ maximumArrayLength
  noOwnIterator : symbolOwn before (.array pattern) = none

def record (before : ArrayBindingState) (nextHandle : Nat) : ArrayIteratorRecord :=
  ⟨before.regexp.ambient.objects.length, .function nextHandle, false⟩
def acquired (before : ArrayBindingState) (context : ArrayIteratorContext) (pattern valuesHandle nextHandle : Nat) : ArrayBindingState :=
  arrayIteratorAcquiredState context pattern (.function valuesHandle) (.function nextHandle) before

def stepState (context : ArrayIteratorContext) (iterator pattern index : Nat) (values : List Value)
    (before : ArrayBindingState) (readValue : Bool) : ArrayBindingState :=
  let yielded := iteratorYieldState context iterator pattern index values before
  {yielded with trace := yielded.trace ++ [.doneGet before.regexp.ambient.objects.length (.boolean false)] ++
    (if readValue then [.valueGet before.regexp.ambient.objects.length (values[index]?.getD .undefined)] else [])}

def initialized (before : ArrayBindingState) (name : String) (value : Value) : ArrayBindingState :=
  {before with
    regexp := {before.regexp with ambient := {before.regexp.ambient with environment := (name, value) :: before.regexp.ambient.environment}}
    trace := before.trace ++ [.initialized name value]}

def firstState (before : ArrayBindingState) (context : ArrayIteratorContext) (pattern valuesHandle nextHandle : Nat) (values : List Value) : ArrayBindingState :=
  stepState context before.regexp.ambient.objects.length pattern 0 values (acquired before context pattern valuesHandle nextHandle) false

def secondState (before : ArrayBindingState) (context : ArrayIteratorContext) (pattern valuesHandle nextHandle : Nat) (values : List Value) : ArrayBindingState :=
  initialized (stepState context before.regexp.ambient.objects.length pattern 1 values
    (firstState before context pattern valuesHandle nextHandle values) true) "name" (values[1]?.getD .undefined)

def beforeClose (before : ArrayBindingState) (context : ArrayIteratorContext) (pattern valuesHandle nextHandle : Nat) (values : List Value) : ArrayBindingState :=
  initialized (stepState context before.regexp.ambient.objects.length pattern 2 values
    (secondState before context pattern valuesHandle nextHandle values) true) "matcher" (values[2]?.getD .undefined)

def resultState (before : ArrayBindingState) (context : ArrayIteratorContext) (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value) : ArrayBindingState :=
  let after := beforeClose before context pattern valuesHandle nextHandle values
  {after with trace := after.trace ++ [.returnGet before.regexp.ambient.objects.length returned]}

def addedObjects (_before : ArrayBindingState) (context : ArrayIteratorContext) (values : List Value) : ObjectHeap :=
  [arrayIteratorObject context.iteratorPrototype,
   iteratorResultObject context.resultPrototype (values[0]?.getD .undefined) false,
   iteratorResultObject context.resultPrototype (values[1]?.getD .undefined) false,
   iteratorResultObject context.resultPrototype (values[2]?.getD .undefined) false]


/-- One GetIterator, three resumes, an elision without value Get, two real
StepValue reads and CURRENT return Get. No fourth resume is hidden in Close. -/
def protocolEvents (before : ArrayBindingState) (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value) : List ArrayIteratorEvent :=
  let iterator := before.regexp.ambient.objects.length
  [.symbolGet pattern (.function valuesHandle), .iteratorAllocated iterator pattern, .nextGet iterator (.function nextHandle),
   .lengthGet pattern values.length, .elementGet pattern 0 (values[0]?.getD .undefined),
   .resultAllocated (iterator + 1) (values[0]?.getD .undefined) false, .doneGet (iterator + 1) (.boolean false),
   .lengthGet pattern values.length, .elementGet pattern 1 (values[1]?.getD .undefined),
   .resultAllocated (iterator + 2) (values[1]?.getD .undefined) false, .doneGet (iterator + 2) (.boolean false),
   .valueGet (iterator + 2) (values[1]?.getD .undefined), .initialized "name" (values[1]?.getD .undefined),
   .lengthGet pattern values.length, .elementGet pattern 2 (values[2]?.getD .undefined),
   .resultAllocated (iterator + 3) (values[2]?.getD .undefined) false, .doneGet (iterator + 3) (.boolean false),
   .valueGet (iterator + 3) (values[2]?.getD .undefined), .initialized "matcher" (values[2]?.getD .undefined),
   .returnGet iterator returned]

/-- Independent bindings, actual protocol cursor and full old-component frames.
Three yields leave Done=false; Close is not an exhaustion test. Object cells
are a projection of iterator/result allocation, not total native allocation. -/
structure Contract (before after : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern nextHandle : Nat) (values : List Value) (completed : ArrayIteratorRecord) : Prop where
  bindings : after.regexp.ambient.environment = ("matcher", values[2]?.getD .undefined) :: ("name", values[1]?.getD .undefined) :: before.regexp.ambient.environment
  savedRecord : completed = record before nextHandle
  notDone : completed.done = false
  cursor : after.iterators.lookup before.regexp.ambient.objects.length = some ⟨some pattern, 3⟩
  objects : after.regexp.ambient.objects = before.regexp.ambient.objects ++ addedObjects before context values
  oldObjects : ∀ reference, reference < before.regexp.ambient.objects.length → after.regexp.ambient.objects[reference]? = before.regexp.ambient.objects[reference]?
  arrays : after.regexp.ambient.heap = before.regexp.ambient.heap
  brands : after.regexp.brands = before.regexp.brands
  results : after.regexp.results = before.regexp.results
  privates : after.regexp.ambient.privates = before.regexp.ambient.privates
  functions : after.regexp.ambient.functions = before.regexp.ambient.functions
  sets : after.regexp.ambient.sets = before.regexp.ambient.sets
  thisValue : after.regexp.ambient.thisValue = before.regexp.ambient.thisValue
  symbols : after.symbols = before.symbols
  oldIterators : ∀ reference, reference < before.regexp.ambient.objects.length → after.iterators.lookup reference = before.iterators.lookup reference

end HonoLean.Upstream.NodePatternBinding
