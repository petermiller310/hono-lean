import HonoLean.Upstream.SourceSubset.PrivateControlParser
import HonoLean.Upstream.ECMA2025.DenseConcat

namespace HonoLean.Upstream.SourceSubset

/-- Admission-only projection: a single concat argument is checked by the
existing variadic push syntax rule, recursively. The original raw AST is
returned and executed unchanged; this is neither a runtime lowering nor an
extension of the older expression/block admission entries. -/
private def concatAdmissionView : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, expression => do
    match expression with
    | .variable _ | .this | .string _ | .number _ | .null | .boolean _ | .preIncrement _ => some expression
    | .property receiver key => return .property (← concatAdmissionView fuel receiver) key
    | .privateProperty receiver key => return .privateProperty (← concatAdmissionView fuel receiver) key
    | .logicalNot value => return .logicalNot (← concatAdmissionView fuel value)
    | .typeAssertion value annotation => return .typeAssertion (← concatAdmissionView fuel value) annotation
    | .index left right => return .index (← concatAdmissionView fuel left) (← concatAdmissionView fuel right)
    | .optionalIndex left right => return .optionalIndex (← concatAdmissionView fuel left) (← concatAdmissionView fuel right)
    | .strictEqual left right => return .strictEqual (← concatAdmissionView fuel left) (← concatAdmissionView fuel right)
    | .compare operation left right => return .compare operation (← concatAdmissionView fuel left) (← concatAdmissionView fuel right)
    | .subtract left right => return .subtract (← concatAdmissionView fuel left) (← concatAdmissionView fuel right)
    | .logicalAnd left right => return .logicalAnd (← concatAdmissionView fuel left) (← concatAdmissionView fuel right)
    | .logicalOr left right => return .logicalOr (← concatAdmissionView fuel left) (← concatAdmissionView fuel right)
    | .nullish left right => return .nullish (← concatAdmissionView fuel left) (← concatAdmissionView fuel right)
    | .conditional test yes no => return .conditional (← concatAdmissionView fuel test) (← concatAdmissionView fuel yes) (← concatAdmissionView fuel no)
    | .call receiver method arguments =>
      if method == "concat" && arguments.length != 1 then none else do
        return .call (← concatAdmissionView fuel receiver) (if method == "concat" then "push" else method) (← arguments.mapM (concatAdmissionView fuel))
    | .invoke callee arguments => return .invoke (← concatAdmissionView fuel callee) (← arguments.mapM (concatAdmissionView fuel))
    | .construct callee annotation arguments => return .construct (← concatAdmissionView fuel callee) annotation (← arguments.mapM (concatAdmissionView fuel))
    | .arrayLiteral entries => return .arrayLiteral (← entries.mapM (fun (spread, value) => do
        return (spread, ← concatAdmissionView fuel value)))
    | .objectLiteral fields => return .objectLiteral (← fields.mapM (fun (key, value) => do
        return (← concatAdmissionView fuel key, ← concatAdmissionView fuel value)))

def mutableSequenceExpressionAdmitted (expression : Expr) (bindings privateNames : List String) : Bool :=
  match concatAdmissionView 65536 expression with
  | none => false
  | some view => expressionAdmitted view bindings privateNames true &&
      privateControlExpressionAllowed 65536 expression

private def sequenceDeclaration : Stmt → Option (String × Expr)
  | .declare name value | .typedDeclare name _ value | .mutableDeclare name _ value => some (name, value)
  | _ => none

private def mutableStatements : Nat → List String → List String → List String → List Token → Option (List Stmt)
  | 0, _, _, _, _ => none
  | fuel + 1, bindings, mutableBindings, privateNames, tokens => do
    let tokens := skipTokenLines tokens
    if tokens.isEmpty then some [] else do
    let (head, rest) ← parseRawStatementTokens tokens
    match sequenceDeclaration head with
    | some (name, value) =>
      if !bindingNameAllowed name || name == "Object" || name == "Set" || bindings.contains name ||
          !mutableSequenceExpressionAdmitted value bindings privateNames then none else
      return head :: (← mutableStatements fuel (name :: bindings) (mutableBindings.filter (· != name)) privateNames rest)
    | none =>
      match head with
      | .assign ⟨.variable name, value⟩ =>
        if !mutableBindings.contains name || !bindings.contains name ||
            !mutableSequenceExpressionAdmitted value bindings privateNames then none else
        return head :: (← mutableStatements fuel bindings mutableBindings privateNames rest)
      | .evaluate value =>
        if !mutableSequenceExpressionAdmitted value bindings privateNames then none else
        return head :: (← mutableStatements fuel bindings mutableBindings privateNames rest)
      | _ => none

/-- Separate linear fragment entry. Fresh declarations are read-only for this
entry, including let declarations; only explicitly supplied existing names may
be rebound. Full const/TDZ/module live-cell semantics are not claimed. Raw
statement boundaries and complete token consumption are retained. -/
def parseMutableSequence (text : String) (allowedBindings mutableBindings : List String)
    (allowedPrivateNames : List String := []) : Option (List Stmt) := do
  if !allowedBindings.all bindingNameAllowed || !mutableBindings.all bindingNameAllowed then none else
  let tokens ← tokenizePrivateControl text
  -- The shared simple-statement grammar needs an explicit boundary. EOF is
  -- an ASI boundary; supplying a final line token adds no executable syntax.
  mutableStatements (tokens.length + 2) allowedBindings mutableBindings allowedPrivateNames (tokens ++ [.lineBreak])

/-- First lexical slot, captured before RHS evaluation. This deliberately does
not reuse or widen ordinary/public/private AssignmentReference. -/
def mutableBindingIndex (name : String) : List (String × Value) → Option Nat
  | [] => none
  | (key, _) :: rest => if name == key then some 0 else (mutableBindingIndex name rest).map Nat.succ

def writeMutableBinding (state : State) (index : Nat) (name : String) (value : Value) : State :=
  {state with environment := state.environment.set index (name, value)}

def executeMutableRebind (fuel limit : Nat) (mutableBindings : List String)
    (name : String) (rhs : Expr) (state : State) : Except EvalError State := do
  -- Authority rejection is a fail-closed boundary outside source admission;
  -- it is not a model of native const-assignment exception ordering.
  if !mutableBindings.contains name then .error .unsupported else
  let index := mutableBindingIndex name state.environment
  let (value, state) ← evalExpression fuel limit rhs state
  match index with
  | none => .error .missingVariable
  | some index => return writeMutableBinding state index name value

/-- Retained-state execution, with no blanket caller-environment restoration.
The runtime allowlist is also checked for manually supplied ASTs. Source
admission rejects increments/captured lexical writes; arbitrary manually built
expressions remain only the explicit model, not a native scope adequacy claim. -/
def executeMutableSequence : Nat → Nat → List String → List Stmt → State → Except EvalError Completion
  | 0, _, _, _, _ => .error .exhausted
  | _ + 1, _, _, [], state => .ok (.normal state)
  | fuel + 1, limit, mutableBindings, head :: tail, state => do
    match head with
    | .declare name value | .typedDeclare name _ value | .mutableDeclare name _ value =>
      let (value, state) ← evalExpression fuel limit value state
      executeMutableSequence fuel limit (mutableBindings.filter (· != name)) tail
        {state with environment := (name, value) :: state.environment}
    | .evaluate value =>
      let (_, state) ← evalExpression fuel limit value state
      executeMutableSequence fuel limit mutableBindings tail state
    | .assign ⟨.variable name, rhs⟩ =>
      let state ← executeMutableRebind fuel limit mutableBindings name rhs state
      executeMutableSequence fuel limit mutableBindings tail state
    | _ => .error .unsupported

theorem mutableBindingIndex_first (front back : List (String × Value)) (name : String) (old : Value)
    (absent : front.lookup name = none) :
    mutableBindingIndex name (front ++ (name, old) :: back) = some front.length := by
  induction front with
  | nil => simp [mutableBindingIndex]
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    by_cases equal : name = key
    · subst key; simp [List.lookup] at absent
    · have unequal : (name == key) = false := beq_eq_false_iff_ne.mpr equal
      simp only [List.lookup, unequal] at absent
      simp [mutableBindingIndex, unequal, ih absent]

/-- Independent saved-slot contract. Non-environment effects are exactly the
RHS state. The prefix determines the ORIGINAL first lexical reference. -/
structure MutableRebindContract (before evaluated after : State) (name : String) (value : Value) : Prop where
  reference : ∃ front old back,
    before.environment = front ++ (name, old) :: back ∧ front.lookup name = none ∧
    after.environment = evaluated.environment.set front.length (name, value)
  heap : after.heap = evaluated.heap
  objects : after.objects = evaluated.objects
  functions : after.functions = evaluated.functions
  sets : after.sets = evaluated.sets
  privates : after.privates = evaluated.privates
  thisValue : after.thisValue = evaluated.thisValue

theorem executeMutableRebind_first (fuel limit : Nat) (mutableBindings : List String)
    (name : String) (rhs : Expr) (before evaluated : State) (value old : Value)
    (front back : List (String × Value))
    (allowed : mutableBindings.contains name = true)
    (environment : before.environment = front ++ (name, old) :: back)
    (absent : front.lookup name = none)
    (right : evalExpression fuel limit rhs before = .ok (value, evaluated)) :
    executeMutableRebind fuel limit mutableBindings name rhs before =
      .ok (writeMutableBinding evaluated front.length name value) := by
  have member : name ∈ mutableBindings := by simpa using allowed
  simp [executeMutableRebind, member, environment,
    mutableBindingIndex_first front back name old absent, right, bind, Except.bind, pure, Except.pure]

/-- Save an unresolved reference before RHS, but reject only after the RHS
has completed. No new lexical binding is inserted. Errors carry no state, so
this equation makes no rollback or native exception-state observation claim. -/
theorem executeMutableRebind_missing_after_rhs (fuel limit : Nat) (mutableBindings : List String)
    (name : String) (rhs : Expr) (before evaluated : State) (value : Value)
    (allowed : mutableBindings.contains name = true)
    (missing : mutableBindingIndex name before.environment = none)
    (right : evalExpression fuel limit rhs before = .ok (value, evaluated)) :
    executeMutableRebind fuel limit mutableBindings name rhs before = .error .missingVariable := by
  have member : name ∈ mutableBindings := by simpa using allowed
  simp [executeMutableRebind, member, missing, right, bind, Except.bind]

theorem executeMutableRebind_rhs_error (fuel limit : Nat) (mutableBindings : List String)
    (name : String) (rhs : Expr) (before : State) (error : EvalError)
    (allowed : mutableBindings.contains name = true)
    (right : evalExpression fuel limit rhs before = .error error) :
    executeMutableRebind fuel limit mutableBindings name rhs before = .error error := by
  have member : name ∈ mutableBindings := by simpa using allowed
  simp [executeMutableRebind, member, right, bind, Except.bind]

theorem writeMutableBinding_satisfies (before evaluated : State) (name : String) (value old : Value)
    (front back : List (String × Value))
    (environment : before.environment = front ++ (name, old) :: back) (absent : front.lookup name = none) :
    MutableRebindContract before evaluated (writeMutableBinding evaluated front.length name value) name value :=
  ⟨⟨front, old, back, environment, absent, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem writeMutableBinding_same_environment (state : State) (front back : List (String × Value))
    (name : String) (old value : Value) (environment : state.environment = front ++ (name, old) :: back) :
    (writeMutableBinding state front.length name value).environment = front ++ (name, value) :: back := by
  simp [writeMutableBinding, environment, List.set_append_right]

end HonoLean.Upstream.SourceSubset
