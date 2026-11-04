import HonoLean.Upstream.NodeParamsInit.Source
import HonoLean.Upstream.ECMA2025.ForIn
import HonoLean.Upstream.ECMA2025.ObjectSpread

set_option autoImplicit false
namespace HonoLean.Upstream.NodeParamsInit
open SourceSubset ECMA2025

/-- Before-state lexical/private DATA facts. The identity test needs no source
copy readiness: the shared object can even contain enumerable accessors. -/
structure HeaderInputs (before : State) (owner identity source empty : Nat) : Prop where
  nodeBinding : before.environment.lookup "node" = some (.object owner)
  emptyBinding : before.environment.lookup "emptyParams" = some (.object empty)
  emptyFound : ∃ object, before.objects[empty]? = some object
  writable : NodePrivateWrite.Writable before owner identity (.object source)
  rootFound : ∃ root, before.objects[0]? = some root

/-- Independent own-data eligibility. Inherited properties and nonenumerable
accessors need not be readable. Symbols/proxies and effectful enumerable getters
are outside the normal source-copy interpretation domain. -/
def EnumerableData (object : OrdinaryObject) : Prop :=
  WellFormedObject object ∧ ∀ key descriptor, object.own.lookup key = some descriptor →
    descriptorEnumerable descriptor = true → ∃ value writable configurable, descriptor = .data value writable true configurable

def OwnEnumerableValue (object : OrdinaryObject) (key : JSString) (value : Value) : Prop :=
  ∃ writable configurable, object.own.lookup key = some (.data value writable true configurable)

structure CopyInputs (before : State) (owner identity source empty : Nat) (object : OrdinaryObject) : Prop
    extends HeaderInputs before owner identity source empty where
  different : source ≠ empty
  sourceFound : before.objects[source]? = some object
  eligible : EnumerableData object

/-- Fresh output descriptors are own W/E/C DATA. Their Values are retained
shallowly, including object/array/function aliases and self-reference to source. -/
def CopiedFields (source target : OrdinaryObject) : Prop :=
  ∀ key descriptor, target.own.lookup key = some descriptor ↔
    ∃ value, OwnEnumerableValue source key value ∧ descriptor = .data value true true true

def EmptyFields (object : OrdinaryObject) : Prop := object.own = []

/-- Independent source observations. The only new public cell is one ordinary
object; the original private params pointer and every old cell are preserved.
Property order is not identified with native OwnPropertyKeys ordering. -/
structure InitContract (before after : State) (owner identity source empty : Nat) : Prop where
  initial : HeaderInputs before owner identity source empty
  environment : after.environment = ("params", .object before.objects.length) :: before.environment
  fresh : before.objects[before.objects.length]? = none
  count : after.objects.length = before.objects.length + 1
  object : ∃ target, after.objects[before.objects.length]? = some target ∧ target.prototype = some 0 ∧ target.extensible = true ∧
    WellFormedObject target ∧
    ((source = empty ∧ EmptyFields target) ∨
      (source ≠ empty ∧ ∃ prior, before.objects[source]? = some prior ∧ EnumerableData prior ∧ CopiedFields prior target))
  oldObjects : ∀ reference, reference < before.objects.length → after.objects[reference]? = before.objects[reference]?
  arrays : after.heap = before.heap
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue
  privateRead : privateGet (.object owner) "params" after = .ok (.object source)

end HonoLean.Upstream.NodeParamsInit
