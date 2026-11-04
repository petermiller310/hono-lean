import HonoLean.Upstream.SourceSubset.ForHeader
import HonoLean.Upstream.SourceSubset.MutableSequence

namespace HonoLean.Upstream.SourceSubset

/-- Dedicated extension retaining + syntax without changing the old Expr ABI. -/
inductive OffsetExpr where
  | ordinary (value : Expr)
  | add (left right : OffsetExpr)
  | index (receiver key : OffsetExpr)
  | property (receiver : OffsetExpr) (key : JSString)
  | call (receiver : OffsetExpr) (method : String) (arguments : List OffsetExpr)
  | logicalNot (value : OffsetExpr)
  | strictEqual (left right : OffsetExpr)
  | compare (operation : NumericComparison) (left right : OffsetExpr)
  | conditional (condition yes no : OffsetExpr)
  deriving Repr

inductive OffsetStmt where
  | declare (mutableBinding : Bool) (name : String) (value : OffsetExpr)
  | assign (target value : OffsetExpr)
  | addAssign (name : String) (value : OffsetExpr)
  | branch (condition : OffsetExpr) (body : List OffsetStmt)
  | countedFor (header : ForHeader) (body : List OffsetStmt)
  deriving Repr

def offsetDeclaredNames (body : List OffsetStmt) : List String :=
  body.filterMap (fun statement => match statement with | .declare _ name _ => some name | _ => none)

/-- Restore only scoped names at their saved positions. Every nonlocal entry
comes from the current environment, retaining its updated value and duplicates.
Admitted scopes preserve that nonlocal name/order skeleton; no closure cells or
arbitrary environment restructuring is claimed. -/
def weaveScoped (names : List String) : List (String × Value) → List (String × Value) → List (String × Value)
  | [], current => current
  | old :: rest, current =>
    if names.contains old.1 then old :: weaveScoped names rest current
    else match current with
      | [] => []
      | now :: tail => now :: weaveScoped names rest tail

def restoreOffsetScope (outer : List (String × Value)) (names : List String) (after : State) : State :=
  {after with environment := weaveScoped names outer (withoutBindings after.environment names)}

inductive OffsetReference where
  | binding (name : String) (index : Option Nat)
  | property (reference : PropertyReference)
  deriving Repr

namespace OffsetArithmetic

def ExactAdditionDomain (left right : Int) : Prop :=
  Arithmetic.SafeInteger left ∧ Arithmetic.SafeInteger right ∧ Arithmetic.SafeInteger (left + right)
def Sum (left right result : Int) : Prop := result - left = right

theorem add_sum (left right : Int) : Sum left right (left + right) := by unfold Sum; omega

end OffsetArithmetic
theorem weaveScoped_empty (outer current : List (String × Value)) : weaveScoped [] outer current = current := by
  induction outer generalizing current with
  | nil => rfl
  | cons head tail ih => cases current <;> simp [weaveScoped, ih]

theorem weaveScoped_self (names : List String) (outer : List (String × Value)) :
    weaveScoped names outer (withoutBindings outer names) = outer := by
  induction outer with
  | nil => rfl
  | cons head tail ih =>
    by_cases removed : head.1 ∈ names <;>
      simpa [weaveScoped, withoutBindings, removed] using congrArg (List.cons head) ih

theorem withoutBindings_nil (environment : List (String × Value)) : withoutBindings environment [] = environment := by
  apply List.filter_eq_self.mpr
  intro entry _
  rfl

theorem restoreOffsetScope_empty (outer : List (String × Value)) (state : State) : restoreOffsetScope outer [] state = state := by
  simp only [restoreOffsetScope, withoutBindings_nil, weaveScoped_empty]

/-- Exact first-slot replacement survives restoring different scoped names;
all earlier/later entries, including duplicate target names, retain position. -/
theorem weaveScoped_rebind (names : List String) (front back : List (String × Value))
    (name : String) (old value : Value) (outside : names.contains name = false) :
    weaveScoped names (front ++ (name, old) :: back)
      (withoutBindings (front ++ (name, value) :: back) names) = front ++ (name, value) :: back := by
  have nonMember : name ∉ names := by simpa using outside
  induction front with
  | nil => simpa [weaveScoped, withoutBindings, nonMember] using congrArg (List.cons (name, value)) (weaveScoped_self names back)
  | cons head tail ih =>
    by_cases removed : head.1 ∈ names <;>
      simpa [weaveScoped, withoutBindings, removed] using congrArg (List.cons head) ih

theorem withoutBindings_idempotent (environment : List (String × Value)) (names : List String) :
    withoutBindings (withoutBindings environment names) names = withoutBindings environment names := by
  simp [withoutBindings, List.filter_filter]

theorem withoutBindings_commute (environment : List (String × Value)) (left right : List String) :
    withoutBindings (withoutBindings environment left) right = withoutBindings (withoutBindings environment right) left := by
  simp [withoutBindings, List.filter_filter, Bool.and_comm]

theorem withoutBindings_append (environment : List (String × Value)) (left right : List String) :
    withoutBindings environment (left ++ right) = withoutBindings (withoutBindings environment left) right := by
  simp [withoutBindings, List.filter_filter, Bool.not_or, Bool.and_comm]

end HonoLean.Upstream.SourceSubset
