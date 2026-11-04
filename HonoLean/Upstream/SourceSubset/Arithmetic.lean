import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset

namespace Arithmetic

def maximumSafeInteger : Int := 9007199254740991

/-- A boundary predicate for interpreting canonical mathematical integers as
native finite integral Numbers. The model has no signed-zero distinction. -/
def SafeInteger (value : Int) : Prop :=
  -maximumSafeInteger ≤ value ∧ value ≤ maximumSafeInteger

/-- Both operands AND the exact difference must fit. This is an interpretation
domain, not a theorem about native IEEE arithmetic/ToNumeric/coercion. NaN,
infinities, fractions, BigInt and negative-zero identity are unrepresented.
The interpreter itself continues to calculate mathematical Ints outside it. -/
def ExactSubtractionDomain (left right : Int) : Prop :=
  SafeInteger left ∧ SafeInteger right ∧ SafeInteger (left - right)

/-- Independent arithmetic specification: adding back the subtrahend recovers
the minuend. No expression evaluator occurs in this relation. -/
def Difference (left right result : Int) : Prop := result + right = left

theorem subtraction_difference (left right : Int) : Difference left right (left - right) :=
  Int.sub_add_cancel left right

theorem difference_unique (left right first second : Int)
    (one : Difference left right first) (two : Difference left right second) : first = second := by
  unfold Difference at one two
  omega

/-- Native dense-array lengths in the declared UInt32 domain are far inside
the exact-integer boundary, including len=0 whose difference is -1. -/
theorem denseLength_subtract_one (length : Nat) (bound : length ≤ 4294967295) :
    ExactSubtractionDomain (Int.ofNat length) 1 := by
  unfold ExactSubtractionDomain SafeInteger maximumSafeInteger
  simp only [Int.ofNat_eq_natCast]
  omega

theorem denseIndex_safe (index length : Nat) (inside : index < length) (bound : length ≤ 4294967295) :
    SafeInteger (Int.ofNat index) := by
  unfold SafeInteger maximumSafeInteger
  simp only [Int.ofNat_eq_natCast]
  omega

theorem currentIndex_last_iff (index length : Nat) :
    (Int.ofNat index = Int.ofNat length - 1) ↔ index + 1 = length := by
  simp only [Int.ofNat_eq_natCast]
  omega

end Arithmetic

/-- Operand effects are sequenced before specializing their values to the
modeled mathematical Int domain. No early left-value type rejection occurs. -/
theorem eval_subtract_numbers (fuel limit : Nat) (left right : Expr)
    (before middle after : State) (a b : Int)
    (first : evalExpression fuel limit left before = .ok (.number a, middle))
    (second : evalExpression fuel limit right middle = .ok (.number b, after)) :
    evalExpression (fuel + 1) limit (.subtract left right) before = .ok (.number (a - b), after) := by
  simp [evalExpression, first, second, bind, pure, Except.bind, Except.pure]

theorem eval_subtract_right_error (fuel limit : Nat) (left right : Expr)
    (before middle : State) (value : Value) (error : EvalError)
    (first : evalExpression fuel limit left before = .ok (value, middle))
    (second : evalExpression fuel limit right middle = .error error) :
    evalExpression (fuel + 1) limit (.subtract left right) before = .error error := by
  simp [evalExpression, first, second, bind, Except.bind]

theorem eval_subtract_left_error (fuel limit : Nat) (left right : Expr)
    (before : State) (error : EvalError)
    (first : evalExpression fuel limit left before = .error error) :
    evalExpression (fuel + 1) limit (.subtract left right) before = .error error := by
  simp [evalExpression, first, bind, Except.bind]

theorem eval_subtract_satisfies (fuel limit : Nat) (left right : Expr)
    (before middle after : State) (a b : Int)
    (first : evalExpression fuel limit left before = .ok (.number a, middle))
    (second : evalExpression fuel limit right middle = .ok (.number b, after)) :
    ∃ result, evalExpression (fuel + 1) limit (.subtract left right) before = .ok (.number result, after) ∧
      Arithmetic.Difference a b result :=
  ⟨a - b, eval_subtract_numbers fuel limit left right before middle after a b first second,
    Arithmetic.subtraction_difference a b⟩

/-- This adds the explicit exact-integer boundary to the model contract. It
does not supply an unproved native Number/ToNumeric adequacy theorem. -/
theorem eval_subtract_safe_satisfies (fuel limit : Nat) (left right : Expr)
    (before middle after : State) (a b : Int)
    (first : evalExpression fuel limit left before = .ok (.number a, middle))
    (second : evalExpression fuel limit right middle = .ok (.number b, after))
    (domain : Arithmetic.ExactSubtractionDomain a b) :
    ∃ result, evalExpression (fuel + 1) limit (.subtract left right) before = .ok (.number result, after) ∧
      Arithmetic.Difference a b result ∧ Arithmetic.SafeInteger result :=
  ⟨a - b, eval_subtract_numbers fuel limit left right before middle after a b first second,
    Arithmetic.subtraction_difference a b, domain.2.2⟩

end HonoLean.Upstream.SourceSubset
