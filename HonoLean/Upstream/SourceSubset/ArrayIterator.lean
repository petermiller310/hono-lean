import HonoLean.Upstream.SourceSubset.ArrayBindingSyntax
import HonoLean.Upstream.SourceSubset.RegExpConstructRules

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

/-- A typed well-known symbol, never the string '@@iterator' or Symbol.iterator. -/
inductive ArraySymbol where
  | iterator
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq
inductive ArraySymbolOwner where
  | array (reference : Nat)
  | object (reference : Nat)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq
inductive ArrayIteratorBuiltin where
  | arrayValues | arrayNext
  deriving Repr, DecidableEq
structure ArrayIteratorTable where
  base : Nat
  entries : List ArrayIteratorBuiltin
  deriving Repr, DecidableEq
structure ArrayIteratorContext where
  constructors : RegExpConstructContext
  builtins : ArrayIteratorTable
  arrayPrototype : Nat
  iteratorPrototype : Nat
  resultPrototype : Nat := 0
  deriving Repr

/-- Next-position projection, not the generator's literal suspended local
index: native index++ happens on resumption after yield. none is persistently
completed and cannot revive if the original array later grows. -/
structure ArrayIteratorCursor where
  array : Option Nat
  nextIndex : Nat := 0
  deriving Repr, DecidableEq
structure ArrayIteratorRecord where
  iterator : Nat
  nextMethod : Value
  done : Bool := false
  deriving Repr, DecidableEq
inductive ArrayIteratorEvent where
  | symbolGet (array : Nat) (value : Value)
  | iteratorAllocated (reference array : Nat)
  | nextGet (reference : Nat) (value : Value)
  | lengthGet (array length : Nat)
  | elementGet (array index : Nat) (value : Value)
  | resultAllocated (reference : Nat) (value : Value) (done : Bool)
  | doneGet (result : Nat) (value : Value)
  | valueGet (result : Nat) (value : Value)
  | returnGet (iterator : Nat) (value : Value)
  | initialized (name : String) (value : Value)
  deriving Repr, DecidableEq

/-- The ordinary object heap is authoritative for next/return/result
properties; typed symbol descriptors supplement its absent Symbol key sort.
Iterator and result objects really append to that projected ordinary heap.
This is not total native physical/internal allocation or exotic-array adequacy. -/
structure ArrayBindingState where
  regexp : RegExpCallState
  symbols : List (ArraySymbolOwner × List (ArraySymbol × PropertyDescriptor)) := []
  iterators : List (Nat × ArrayIteratorCursor) := []
  trace : List ArrayIteratorEvent := []
  deriving Repr
inductive ArrayBindingError where
  | evaluation (error : EvalError)
  | iteratorDomain | returnDomain | symbolDomain | representation | exhausted
  deriving Repr, DecidableEq

def iteratorNextKey : JSString := [110, 101, 120, 116]
def iteratorReturnKey : JSString := [114, 101, 116, 117, 114, 110]
def iteratorValueKey : JSString := [118, 97, 108, 117, 101]
def iteratorDoneKey : JSString := [100, 111, 110, 101]

def iteratorBuiltinAt (table : ArrayIteratorTable) : Value → Option ArrayIteratorBuiltin
  | .function reference => if table.base ≤ reference then table.entries[reference - table.base]? else none
  | _ => none

def iteratorTablesSeparated (context : ArrayIteratorContext) (state : State) : Bool :=
  let table := context.builtins
  let old := context.constructors
  let apart := fun (base length : Nat) => length == 0 || table.entries.isEmpty ||
    decide (table.base + table.entries.length ≤ base) || decide (base + length ≤ table.base)
  (table.entries.isEmpty || decide (state.functions.length ≤ table.base)) &&
    apart old.methods.base old.methods.entries.length && apart old.functions.base old.functions.entries.length &&
    apart old.members.base old.members.entries.length && apart old.builtins.base old.builtins.entries.length &&
    apart old.constructors.base old.constructors.entries.length

def symbolOwn (before : ArrayBindingState) (owner : ArraySymbolOwner) : Option PropertyDescriptor :=
  (before.symbols.lookup owner).bind (fun own => own.lookup .iterator)

/-- Full ordinary prototype traversal for the typed symbol. Only DATA or
missing getter values are supported; proxy/coercive/custom accessors stay open. -/
def lookupIteratorSymbol : Nat → ArrayBindingState → Nat → Except ArrayBindingError Value
  | 0, _, _ => .error .exhausted
  | fuel + 1, before, holder =>
    match before.regexp.ambient.objects[holder]? with
    | none => .error (.evaluation .invalidReference)
    | some object =>
      match symbolOwn before (.object holder) with
      | some (.data value _ _ _) => .ok value
      | some (.accessor .missing _ _ _) => .ok .undefined
      | some (.accessor _ _ _ _) => .error .symbolDomain
      | none => match object.prototype with
        | none => .ok .undefined
        | some parent => lookupIteratorSymbol fuel before parent

def getArrayIteratorMethod (context : ArrayIteratorContext) (reference : Nat) (before : ArrayBindingState) :
    Except ArrayBindingError Value :=
  match before.regexp.ambient.heap[reference]? with
  | none => .error (.evaluation .invalidReference)
  | some _ => match symbolOwn before (.array reference) with
    | some (.data value _ _ _) => .ok value
    | some (.accessor .missing _ _ _) => .ok .undefined
    | some (.accessor _ _ _ _) => .error .symbolDomain
    | none => lookupIteratorSymbol propertyFuel before context.arrayPrototype

def arrayIteratorObject (prototype : Nat) : OrdinaryObject := ⟨[], some prototype, true⟩
def iteratorResultObject (prototype : Nat) (value : Value) (done : Bool) : OrdinaryObject :=
  ⟨[(iteratorValueKey, .data value true true true), (iteratorDoneKey, .data (.boolean done) true true true)], some prototype, true⟩

def allocateArrayIterator (context : ArrayIteratorContext) (array : Nat) (before : ArrayBindingState) : ArrayBindingState :=
  {before with
    regexp := {before.regexp with ambient := {before.regexp.ambient with
      objects := before.regexp.ambient.objects ++ [arrayIteratorObject context.iteratorPrototype]}}
    iterators := (before.regexp.ambient.objects.length, ⟨some array, 0⟩) :: before.iterators
    trace := before.trace ++ [.iteratorAllocated before.regexp.ambient.objects.length array]}

def getArrayIterator (context : ArrayIteratorContext) (value : Value) (before : ArrayBindingState) :
    Except ArrayBindingError (ArrayIteratorRecord × ArrayBindingState) := do
  let array ← match value with | .array reference => .ok reference | _ => .error .iteratorDomain
  let method ← getArrayIteratorMethod context array before
  let before := {before with trace := before.trace ++ [.symbolGet array method]}
  if !iteratorTablesSeparated context before.regexp.ambient then throw .representation else do
  if iteratorBuiltinAt context.builtins method != some .arrayValues then throw .iteratorDomain else do
  let _ ← match before.regexp.ambient.objects[context.iteratorPrototype]? with
    | some object => .ok object | none => .error (.evaluation .invalidReference)
  let reference := before.regexp.ambient.objects.length
  let after := allocateArrayIterator context array before
  let next ← (getProperty propertyFuel after.regexp.ambient.objects reference iteratorNextKey).mapError
    (ArrayBindingError.evaluation ∘ EvalError.objectError)
  -- GetIteratorDirect saves next WITHOUT checking callability yet.
  pure (⟨reference, next, false⟩, {after with trace := after.trace ++ [.nextGet reference next]})

def setArrayIteratorCursor (reference : Nat) (cursor : ArrayIteratorCursor) (before : ArrayBindingState) : ArrayBindingState :=
  {before with iterators := (reference, cursor) :: before.iterators.filter (fun entry => entry.1 != reference)}

def allocateIteratorResult (context : ArrayIteratorContext) (value : Value) (done : Bool) (before : ArrayBindingState) :
    Except ArrayBindingError (Nat × ArrayBindingState) := do
  let _ ← match before.regexp.ambient.objects[context.resultPrototype]? with
    | some object => .ok object | none => .error (.evaluation .invalidReference)
  let reference := before.regexp.ambient.objects.length
  pure (reference, {before with
    regexp := {before.regexp with ambient := {before.regexp.ambient with
      objects := before.regexp.ambient.objects ++ [iteratorResultObject context.resultPrototype value done]}}
    trace := before.trace ++ [.resultAllocated reference value done]})

/-- Current length and indexedGet at every resume. DATA dense reads exclude
holes/prototype overrides/getters; result.value remains a real separate Get. -/
def arrayIteratorNext (context : ArrayIteratorContext) (reference : Nat) (before : ArrayBindingState) :
    Except ArrayBindingError (Nat × ArrayBindingState) := do
  let cursor ← match before.iterators.lookup reference with | some cursor => .ok cursor | none => .error .iteratorDomain
  match cursor.array with
  | none => allocateIteratorResult context .undefined true before
  | some array =>
    let values ← match before.regexp.ambient.heap[array]? with
      | some values => .ok values | none => .error (.evaluation .invalidReference)
    let before := {before with trace := before.trace ++ [.lengthGet array values.length]}
    if cursor.nextIndex < values.length then do
      let value ← (readProperty (.array array) (.number cursor.nextIndex) before.regexp.ambient).mapError .evaluation
      let after := setArrayIteratorCursor reference ⟨some array, cursor.nextIndex + 1⟩ before
      allocateIteratorResult context value false {after with trace := after.trace ++ [.elementGet array cursor.nextIndex value]}
    else
      allocateIteratorResult context .undefined true (setArrayIteratorCursor reference ⟨none, cursor.nextIndex⟩ before)

def invokeArrayIteratorNext (context : ArrayIteratorContext) (record : ArrayIteratorRecord) (before : ArrayBindingState) :
    Except ArrayBindingError (Nat × ArrayBindingState) :=
  if !iteratorTablesSeparated context before.regexp.ambient then .error .representation else
  if iteratorBuiltinAt context.builtins record.nextMethod == some .arrayNext then
    arrayIteratorNext context record.iterator before
  else .error .iteratorDomain

/-- Binding-level guarded IteratorStep performs done Get without value Get.
The binding algorithm guards an already-done record; this wrapper includes
that guard and is not a claim that abstract IteratorStep itself has it.
Except exposes no partial error state, rollback or recordDone-on-error trace. -/
def iteratorStep (context : ArrayIteratorContext) (record : ArrayIteratorRecord) (before : ArrayBindingState) :
    Except ArrayBindingError (Option Nat × ArrayIteratorRecord × ArrayBindingState) := do
  if record.done then pure (none, record, before) else do
  let (result, after) ← invokeArrayIteratorNext context record before
  let done ← (getProperty propertyFuel after.regexp.ambient.objects result iteratorDoneKey).mapError
    (ArrayBindingError.evaluation ∘ EvalError.objectError)
  let after := {after with trace := after.trace ++ [.doneGet result done]}
  if truthy done then pure (none, {record with done := true}, after)
  else pure (some result, record, after)

def iteratorValue (result : Nat) (before : ArrayBindingState) : Except ArrayBindingError (Value × ArrayBindingState) := do
  let value ← (getProperty propertyFuel before.regexp.ambient.objects result iteratorValueKey).mapError
    (ArrayBindingError.evaluation ∘ EvalError.objectError)
  pure (value, {before with trace := before.trace ++ [.valueGet result value]})

/-- SingleNameBinding specialization of StepValue: exhaustion maps to JS
undefined for the binding. The abstract operation's separate done sentinel
is retained by iteratorStep's Option and record.done, not conflated there. -/
def iteratorStepValue (context : ArrayIteratorContext) (record : ArrayIteratorRecord) (before : ArrayBindingState) :
    Except ArrayBindingError (Value × ArrayIteratorRecord × ArrayBindingState) := do
  let (result, record, after) ← iteratorStep context record before
  match result with
  | none => pure (.undefined, record, after)
  | some result =>
    let (value, after) ← iteratorValue result after
    pure (value, record, after)

/-- CURRENT full-chain GetMethod(return); default undefined/null performs no
call, does not mark recordDone, and does not alter cursor/completion. General
custom return calls/abrupt completion and their error precedence remain open. -/
def closeArrayIterator (record : ArrayIteratorRecord) (before : ArrayBindingState) :
    Except ArrayBindingError ArrayBindingState := do
  if record.done then pure before else do
  let value ← (getProperty propertyFuel before.regexp.ambient.objects record.iterator iteratorReturnKey).mapError
    (ArrayBindingError.evaluation ∘ EvalError.objectError)
  if value == .undefined || value == .null then
    pure {before with trace := before.trace ++ [.returnGet record.iterator value]}
  else .error .returnDomain

def bindArrayElements : Nat → ArrayIteratorContext → List ArrayBindingElement → ArrayIteratorRecord → ArrayBindingState →
    Except ArrayBindingError (ArrayIteratorRecord × ArrayBindingState)
  | 0, _, _, _, _ => .error .exhausted
  | _ + 1, _, [], record, before => .ok (record, before)
  | fuel + 1, context, element :: tail, record, before => do
    match element with
    | .elision =>
      let (_, record, after) ← iteratorStep context record before
      bindArrayElements fuel context tail record after
    | .binding name =>
      let (value, record, after) ← iteratorStepValue context record before
      let after := {after with
        regexp := {after.regexp with ambient := {after.regexp.ambient with
          environment := (name, value) :: after.regexp.ambient.environment}}
        trace := after.trace ++ [.initialized name value]}
      bindArrayElements fuel context tail record after

def runArrayBinding (fuel limit : Nat) (context : ArrayIteratorContext) (declaration : ArrayBindingDecl) (before : ArrayBindingState) :
    Except ArrayBindingError (ArrayIteratorRecord × ArrayBindingState) := do
  let (value, ambient) ← (evalExpression fuel limit declaration.initializer before.regexp.ambient).mapError .evaluation
  let (record, after) ← getArrayIterator context value {before with regexp := {before.regexp with ambient}}
  let (record, after) ← bindArrayElements fuel context declaration.elements record after
  let after ← closeArrayIterator record after
  pure (record, after)

def executeArrayBinding (fuel limit : Nat) (context : ArrayIteratorContext) (declaration : ArrayBindingDecl) (before : ArrayBindingState) :
    Except ArrayBindingError ArrayBindingState := (runArrayBinding fuel limit context declaration before).map Prod.snd

end HonoLean.Upstream.SourceSubset
