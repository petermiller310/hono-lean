import HonoLean.Upstream.SourceSubset.RegExpConstruct

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

/-- Independent source/body relation: no parser, compiled result or interpreter
output is supplied by this predicate. -/
def RangeBody (body : JSString) (lower upper : UInt16) : Prop :=
  body = [91, lower, 45, upper, 93, 43] ∧
  RangeRegExp.SafeEndpoint lower ∧ RangeRegExp.SafeEndpoint upper ∧ lower.toNat ≤ upper.toNat

def constructedRangeRecord (lower upper : UInt16) : RangeRegExpRecord :=
  ⟨[94, 91, lower, 45, upper, 93, 43, 36], [], RangeRegExp.code lower upper⟩

theorem initializeRangeRecord_safe (lower upper : UInt16)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) :
    initializeRangeRecord [94, 91, lower, 45, upper, 93, 43, 36] [] = some (constructedRangeRecord lower upper) := by
  have parsed := RangeRegExp.parse_complete _ _ (.anchored lower upper safeLower safeUpper ordered)
  simp only [initializeRangeRecord, List.isEmpty_nil, Bool.not_true]
  rw [parsed]
  rfl

/-- The actual intermediate ordinary allocation, including undefined rather
than an invented early0. The prototype cell must already exist for native
interpretation; all unrelated context components are retained. -/
theorem regExpAllocate_descriptor (before : RegExpCallState) (prototype : Nat) :
    (regExpAllocatedState before prototype).ambient.objects[before.ambient.objects.length]? =
      some (uninitializedRegExpObject prototype) ∧
    (regExpAllocatedState before prototype).ambient.heap = before.ambient.heap ∧
    (regExpAllocatedState before prototype).brands = before.brands ∧
    (regExpAllocatedState before prototype).results = before.results := by
  simp [regExpAllocatedState]

/-- Real initialization performs shared ordinary Set preserving W/E/C. The
parser/compiler equation is derived independently for all safe endpoints. -/
theorem initializeAllocatedRegExp_range (before : RegExpCallState) (prototype : Nat) (lower upper : UInt16)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) :
    initializeAllocatedRegExp before.ambient.objects.length [94, 91, lower, 45, upper, 93, 43, 36]
      (regExpAllocatedState before prototype) =
      .ok (.object before.ambient.objects.length, regExpConstructedState before prototype (constructedRangeRecord lower upper)) := by
  have found : (before.ambient.objects ++ [uninitializedRegExpObject prototype])[before.ambient.objects.length]? =
      some (uninitializedRegExpObject prototype) := by simp
  have assigned := writable_data_preserves_attributes
    (before.ambient.objects ++ [uninitializedRegExpObject prototype]) before.ambient.objects.length
    (propertyFuel - 1) lastIndexKey (uninitializedRegExpObject prototype) .undefined (.number 0) false false found rfl
  have changed : {uninitializedRegExpObject prototype with own :=
      (putOwn lastIndexKey (.data (.number 0) true false false) (uninitializedRegExpObject prototype).own)} =
      initializedRegExpObject prototype := by rfl
  rw [changed] at assigned
  have replaced : (before.ambient.objects ++ [uninitializedRegExpObject prototype]).set before.ambient.objects.length
      (initializedRegExpObject prototype) = before.ambient.objects ++ [initializedRegExpObject prototype] := by simp
  rw [replaced] at assigned
  have budget : propertyFuel - 1 + 1 = propertyFuel := by decide
  rw [budget] at assigned
  simp only [initializeAllocatedRegExp, initializeRangeRecord_safe lower upper safeLower safeUpper ordered,
    regExpAllocatedState, bind, Except.bind]
  rw [assigned]
  rfl

theorem invokeRegExpConstructor_range (context : RegExpConstructContext) (callee : Value)
    (before : RegExpCallState) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (lower upper : UInt16)
    (separated : constructorTablesSeparated context before.ambient = true)
    (identity : constructorAt context.constructors callee = some constructor)
    (prototypeFound : before.ambient.objects[constructor.prototype]? = some prototypeObject)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) :
    invokeRegExpConstructor context callee (.string [94, 91, lower, 45, upper, 93, 43, 36]) before =
      .ok (.object before.ambient.objects.length,
        regExpConstructedState before constructor.prototype (constructedRangeRecord lower upper)) := by
  simp only [invokeRegExpConstructor, separated, Bool.not_true, identity, prototypeFound,
    bind, Except.bind]
  exact initializeAllocatedRegExp_range before constructor.prototype lower upper safeLower safeUpper ordered

/-- Descriptor/internal-source/old-cell and full ambient component contract.
It makes no statement about raw native function/prototype representation,
unreachable engine allocations, errors or arbitrary RegExp source grammar. -/
structure RegExpConstructionContract (before after : RegExpCallState) (returned : Value)
    (prototype : Nat) (source : JSString) (compiled : List RangeRegExp.Instruction) : Prop where
  returnedFresh : returned = .object before.ambient.objects.length
  objects : after.ambient.objects = before.ambient.objects ++ [initializedRegExpObject prototype]
  brand : after.brands = (before.ambient.objects.length, ⟨source, [], compiled⟩) :: before.brands
  heap : after.ambient.heap = before.ambient.heap
  environment : after.ambient.environment = before.ambient.environment
  thisValue : after.ambient.thisValue = before.ambient.thisValue
  functions : after.ambient.functions = before.ambient.functions
  sets : after.ambient.sets = before.ambient.sets
  privates : after.ambient.privates = before.ambient.privates
  results : after.results = before.results

theorem range_construction_contract (before : RegExpCallState) (prototype : Nat) (lower upper : UInt16) :
    RegExpConstructionContract before (regExpConstructedState before prototype (constructedRangeRecord lower upper))
      (.object before.ambient.objects.length) prototype [94, 91, lower, 45, upper, 93, 43, 36] (RangeRegExp.code lower upper) := by
  constructor <;> rfl

theorem construction_old_object (before after : RegExpCallState) (returned : Value) (prototype : Nat)
    (source : JSString) (compiled : List RangeRegExp.Instruction)
    (contract : RegExpConstructionContract before after returned prototype source compiled)
    (reference : Nat) (old : reference < before.ambient.objects.length) :
    after.ambient.objects[reference]? = before.ambient.objects[reference]? := by
  rw [contract.objects]
  exact List.getElem?_append_left old

/-- Callee is SAVED before arguments. These premises describe individual
ordinary operand evaluations, not a desired constructor execution/result. -/
theorem evalRegExpConstruct_saved (fuel limit : Nat) (context : RegExpConstructContext)
    (callee : Expr) (argument : RegExpConstructExpr) (before afterArgument : RegExpCallState)
    (saved : Value) (argumentValue : Value) (afterCallee : State)
    (calleeEval : evalExpression fuel limit callee before.ambient = .ok (saved, afterCallee))
    (argumentEval : evalRegExpConstruct fuel limit context argument {before with ambient := afterCallee} =
      .ok (argumentValue, afterArgument)) :
    evalRegExpConstruct (fuel + 1) limit context (.construct callee argument) before =
      invokeRegExpConstructor context saved argumentValue afterArgument := by
  simp only [evalRegExpConstruct, calleeEval, Except.mapError, bind, Except.bind, argumentEval]

theorem evalRegExpConstruct_template (fuel limit : Nat) (context : RegExpConstructContext)
    (head tail body : JSString) (operand : Expr) (before : RegExpCallState) (after : State)
    (evaluated : evalExpression fuel limit operand before.ambient = .ok (.string body, after)) :
    evalRegExpConstruct (fuel + 1) limit context (.template head operand tail) before =
      .ok (.string (head ++ body ++ tail), {before with ambient := after}) := by
  simp [evalRegExpConstruct, evaluated, constructTemplateValue, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Actual CreateDataProperty-style dense own-element creation, not mutable
Array.prototype.push. Replaces exactly the allocated/current literal cell. -/
theorem appendConstructElement_found (before : RegExpCallState) (reference : Nat) (prior : List Value) (value : Value)
    (found : before.ambient.heap[reference]? = some prior) :
    appendConstructElement reference value before =
      .ok {before with ambient := {before.ambient with heap := before.ambient.heap.set reference (prior ++ [value])}} := by
  simp [appendConstructElement, appendLiteralElements, found, Except.mapError, Except.map]

/-- A literal allocation always starts as[] before even its first operand. -/
theorem evalRegExpConstruct_array (fuel limit : Nat) (context : RegExpConstructContext)
    (elements : List RegExpConstructExpr) (before : RegExpCallState) :
    evalRegExpConstruct (fuel + 1) limit context (.arrayLiteral elements) before =
      (evalRegExpConstructElements fuel limit context before.ambient.heap.length elements (constructArrayState before)).map
        (fun after => (.array before.ambient.heap.length, after)) := by
  simp [evalRegExpConstruct, bind, Except.bind, Except.map, pure, Except.pure]

end HonoLean.Upstream.SourceSubset
