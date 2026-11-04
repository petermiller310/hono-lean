import HonoLean.Upstream.SourceSubset.OffsetSequence

namespace HonoLean.Upstream.SourceSubset

open ECMA2025

theorem evalOffset_add_numbers (fuel limit : Nat) (left right : OffsetExpr) (before middle after : State) (a b : Int)
    (first : evalOffsetExpression fuel limit left before = .ok (.number a, middle))
    (second : evalOffsetExpression fuel limit right middle = .ok (.number b, after)) :
    evalOffsetExpression (fuel + 1) limit (.add left right) before = .ok (.number (a + b), after) := by
  simp [evalOffsetExpression, first, second, bind, Except.bind, pure, Except.pure]

theorem evalOffset_add_right_error (fuel limit : Nat) (left right : OffsetExpr) (before middle : State) (value : Value) (error : EvalError)
    (first : evalOffsetExpression fuel limit left before = .ok (value, middle))
    (second : evalOffsetExpression fuel limit right middle = .error error) :
    evalOffsetExpression (fuel + 1) limit (.add left right) before = .error error := by
  simp [evalOffsetExpression, first, second, bind, Except.bind]

theorem putOffsetReference_append (before : State) (reference : Nat) (values : List Value) (value : Value)
    (found : before.heap[reference]? = some values) (legal : values.length < maximumArrayLength) :
    putOffsetReference (.property ⟨.array reference, .number values.length⟩) value before =
      .ok {before with heap := before.heap.set reference (values ++ [value])} := by
  simp [putOffsetReference, found, legal]

theorem putOffsetReference_update (before : State) (reference index : Nat) (values : List Value) (value : Value)
    (found : before.heap[reference]? = some values) (inside : index < values.length) :
    putOffsetReference (.property ⟨.array reference, .number index⟩) value before =
      .ok {before with heap := before.heap.set reference (values.set index value)} := by
  simp [putOffsetReference, found, inside]

theorem executeOffsetAssign_first (fuel limit : Nat) (mutableBindings : List String) (name : String) (rhs : OffsetExpr)
    (before evaluated : State) (old value : Value) (front back : List (String × Value))
    (allowed : mutableBindings.contains name = true) (environment : before.environment = front ++ (name, old) :: back)
    (absent : front.lookup name = none) (right : evalOffsetExpression fuel limit rhs before = .ok (value, evaluated)) :
    executeOffsetAssign fuel limit mutableBindings (.ordinary (.variable name)) rhs before =
      .ok (writeMutableBinding evaluated front.length name value) := by
  have member : name ∈ mutableBindings := by simpa using allowed
  have captured : mutableBindingIndex name before.environment = some front.length := by
    rw [environment]
    exact mutableBindingIndex_first front back name old absent
  simp [executeOffsetAssign, captureOffsetReference, member, captured, right, putOffsetReference,
    writeMutableBinding, bind, Except.bind, pure, Except.pure]

theorem executeOffsetAddAssign_first (fuel limit : Nat) (mutableBindings : List String) (name : String) (rhs : OffsetExpr)
    (before evaluated : State) (old value : Int) (front back : List (String × Value))
    (allowed : mutableBindings.contains name = true) (environment : before.environment = front ++ (name, .number old) :: back)
    (absent : front.lookup name = none) (right : evalOffsetExpression fuel limit rhs before = .ok (.number value, evaluated)) :
    executeOffsetAddAssign fuel limit mutableBindings name rhs before =
      .ok (writeMutableBinding evaluated front.length name (.number (old + value))) := by
  have member : name ∈ mutableBindings := by simpa using allowed
  have captured : mutableBindingIndex name before.environment = some front.length := by
    rw [environment]
    exact mutableBindingIndex_first front back name (.number old) absent
  have read : before.environment[front.length]? = some (name, .number old) := by
    rw [environment, List.getElem?_append_right (Nat.le_refl _)]
    simp
  simp [executeOffsetAddAssign, member, captured, read, right, putOffsetReference,
    writeMutableBinding, bind, Except.bind]

theorem evalOffset_slice_undefined (fuel limit : Nat) (receiver argument : OffsetExpr) (before middle after : State)
    (input : JSString)
    (base : evalOffsetExpression fuel limit receiver before = .ok (.string input, middle))
    (args : evalOffsetArguments fuel limit [argument] middle = .ok ([.undefined], after)) :
    evalOffsetExpression (fuel + 1) limit (.call receiver "slice" [argument]) before = .ok (.string input, after) := by
  simp [evalOffsetExpression, base, args, prepareMethod, invokePrepared, intrinsic,
    stringSlice, normalizeSliceIndex, bind, Except.bind]

theorem evalOffset_part_length (extra limit : Nat) (before : State) (partsName counterName : String)
    (reference counter : Nat) (parts : List JSString) (part : JSString)
    (partsBinding : before.environment.lookup partsName = some (.array reference))
    (counterBinding : before.environment.lookup counterName = some (.number counter))
    (found : before.heap[reference]? = some (parts.map Value.string)) (atPart : parts[counter]? = some part) :
    evalOffsetExpression (extra + 6) limit
      (.property (.index (.ordinary (.variable partsName)) (.ordinary (.variable counterName))) [108, 101, 110, 103, 116, 104]) before =
      .ok (.number part.length, before) := by
  simp [evalOffsetExpression, evalExpression, lookupVariable, partsBinding, counterBinding,
    readOffsetProperty, readProperty, found, List.getElem?_map, atPart, bind, Except.bind, pure, Except.pure]

theorem executeOffsetSequence_branch_false (fuel limit : Nat) (mutableBindings : List String)
    (condition : OffsetExpr) (body tail : List OffsetStmt) (before afterGuard : State) (value : Value)
    (guard : evalOffsetExpression fuel limit condition before = .ok (value, afterGuard)) (falsy : truthy value = false) :
    executeOffsetSequence (fuel + 1) limit mutableBindings (.branch condition body :: tail) before =
      executeOffsetSequence fuel limit mutableBindings tail afterGuard := by
  simp only [executeOffsetSequence, guard, falsy, bind, Except.bind, Bool.false_eq_true, ite_false]

namespace OffsetArithmetic

theorem uint32_addition_safe (left right : Nat) (bound : left + right ≤ 4294967295) :
    ExactAdditionDomain (left : Int) (right : Int) := by
  unfold ExactAdditionDomain Arithmetic.SafeInteger Arithmetic.maximumSafeInteger
  omega

end OffsetArithmetic
end HonoLean.Upstream.SourceSubset
