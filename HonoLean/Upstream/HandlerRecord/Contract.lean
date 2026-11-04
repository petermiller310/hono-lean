import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.HandlerRecord

open SourceSubset ECMA2025

def handlerKey : JSString := [104, 97, 110, 100, 108, 101, 114]
def possibleKeysKey : JSString := [112, 111, 115, 115, 105, 98, 108, 101, 75, 101, 121, 115]
def scoreKey : JSString := [115, 99, 111, 114, 101]
def paramsKey : JSString := [112, 97, 114, 97, 109, 115]

/-- First lexical binding replacement; later shadowed bindings remain intact.
The independent expected state does not call the source evaluator. -/
def replaceOrder : List (String × Value) → Int → List (String × Value)
  | [], _ => []
  | (name, value) :: rest, nextScore =>
    if name = "order" then (name, .number nextScore) :: rest
    else (name, value) :: replaceOrder rest nextScore

/-- Descriptor stores, not native enumeration-order claims. All own fields are
ordinary writable/enumerable/configurable data; params is absent. -/
def innerRecord (handler : Value) (keysArray : Nat) (score : Int) : OrdinaryObject :=
  ⟨[(scoreKey, .data (.number score) true true true),
    (possibleKeysKey, .data (.array keysArray) true true true),
    (handlerKey, .data handler true true true)], some 0, true⟩

def outerRecord (method : JSString) (inner : Nat) : OrdinaryObject :=
  ⟨[(method, .data (.object inner) true true true)], some 0, true⟩

def constructedState (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) : State :=
  {before with
    environment := replaceOrder before.environment (order + 1)
    heap := before.heap ++ [keys.map Value.string]
    objects := before.objects ++ [outerRecord method (before.objects.length + 1),
      innerRecord handler before.heap.length (order + 1)]}

/-- Independent complete successful endpoint: outer cell first, inner second,
one fresh keys array, exact lexical increment/score and all remaining frames.
This is the object argument alone, excluding #methods.push and later selection. -/
def RecordContract (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (returned : Value) (after : State) : Prop :=
  returned = .object before.objects.length ∧
    after = constructedState before method handler keys order

/-- Input bindings/read facts, never an assumed construction or result. -/
structure Inputs (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) : Prop where
  methodBinding : before.environment.lookup "method" = some (.string method)
  handlerBinding : before.environment.lookup "handler" = some handler
  setBinding : before.environment.lookup "possibleKeys" = some (.set reference)
  setFound : before.sets[reference]? = some keys
  orderBinding : before.environment.lookup "order" = some (.number order)
  rootFound : ∃ root, before.objects[0]? = some root

/-- Mathematical integer model interpretation requires native exact integers
for both the old counter and incremented score. Other Number cases are outside. -/
def SafeOrder (order : Int) : Prop := -9007199254740991 ≤ order ∧ order < 9007199254740991

/-- Necessary size/root restrictions, not a theorem of native realm adequacy.
Native interpretation also requires standard stable iterator/realm lookup,
valid identities/descriptors, and enough physical resources. -/
def NativeBounds (before : State) (method : JSString) (keys : List JSString) (order : Int) : Prop :=
  SafeOrder order ∧ method.length ≤ 9007199254740991 ∧
    (∀ key ∈ keys, key.length ≤ 9007199254740991) ∧
    keys.length ≤ 4294967295 ∧ 0 < before.objects.length

theorem inner_fields (handler : Value) (keysArray : Nat) (score : Int) :
    (innerRecord handler keysArray score).own.lookup handlerKey = some (.data handler true true true) ∧
    (innerRecord handler keysArray score).own.lookup possibleKeysKey = some (.data (.array keysArray) true true true) ∧
    (innerRecord handler keysArray score).own.lookup scoreKey = some (.data (.number score) true true true) ∧
    (innerRecord handler keysArray score).own.lookup paramsKey = none := by cbv

/-- Computed __proto__ and constructor names use the same own-data rule as
every other method string. This does not invoke the legacy prototype setter. -/
theorem outer_method (method : JSString) (inner : Nat) :
    (outerRecord method inner).own.lookup method = some (.data (.object inner) true true true) ∧
    (outerRecord method inner).prototype = some 0 := by
  simp [outerRecord]

end HonoLean.Upstream.HandlerRecord
