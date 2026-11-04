import HonoLean.Upstream.SourceSubset.MutableSequence
import HonoLean.Upstream.ECMA2025.SparseArray

namespace HonoLean.Upstream.SourceSubset

open ECMA2025

/-- Separate logical-assignment syntax, retaining the original operator. No
old Expr/Stmt/reference type or older parser entry is widened. -/
inductive SparseInitializer where
  | ordinary (value : Expr)
  | logicalOrAssign (base index rhs : Expr)
  deriving Repr

inductive SparseStmt where
  | declare (name : String) (initializer : SparseInitializer)
  | evaluate (value : Expr)
  | rebind (name : String) (rhs : Expr)
  deriving Repr

private def sparseBoundary : List Token → Option (List Token)
  | .punctuation ";" :: rest => some rest
  | .lineBreak :: rest =>
    match skipTokenLines rest with
    | .punctuation "-" :: _ | .punctuation "(" :: _ | .punctuation "[" :: _
    | .punctuation "." :: _ | .punctuation "?." :: _ => none
    | _ => some rest
  | _ => none

private def sparseExpressionAllowed (value : Expr) (bindings : List String) : Bool :=
  mutableSequenceExpressionAdmitted value bindings []

private def parseLogicalDeclaration (tokens : List Token) (bindings : List String) :
    Option (String × SparseInitializer × List Token) := do
  let (name, rest) ← match tokens with
    | .name "const" :: .name name :: .punctuation "=" :: rest => some (name, skipTokenLines rest)
    | _ => none
  if !bindingNameAllowed name || name == "Object" || name == "Set" || bindings.contains name then none else do
  let (wrapped, rest) := match rest with
    | .punctuation "(" :: rest => (true, rest)
    | _ => (false, rest)
  let (left, rest) ← parseRawExpressionTokens rest
  let rest ← match skipTokenLines rest with
    | .punctuation "||=" :: rest => some rest
    | _ => none
  let (rhs, rest) ← parseRawExpressionTokens rest
  let rest ← if wrapped then
      match skipTokenLines rest with
      | .punctuation ")" :: rest => some rest
      | _ => none
    else some rest
  let rest ← sparseBoundary rest
  match left with
  | .index base index =>
    if sparseExpressionAllowed base bindings && sparseExpressionAllowed index bindings &&
        sparseExpressionAllowed rhs bindings then some (name, .logicalOrAssign base index rhs, rest) else none
  | _ => none

/-- Token-level forwarding for mixed explicit extensions. It preserves the
existing logical initializer grammar/admission and does not widen old entries. -/
def parseSparseLogicalDeclarationTokens (tokens : List Token) (bindings : List String) :
    Option (String × SparseInitializer × List Token) := parseLogicalDeclaration tokens bindings

private def sparseStatements : Nat → List String → List String → List Token → Option (List SparseStmt)
  | 0, _, _, _ => none
  | fuel + 1, bindings, mutableBindings, tokens => do
    let tokens := skipTokenLines tokens
    if tokens.isEmpty then some [] else
    match parseLogicalDeclaration tokens bindings with
    | some (name, value, rest) =>
      return .declare name value :: (← sparseStatements fuel (name :: bindings)
        (mutableBindings.filter (· != name)) rest)
    | none => do
      let (head, rest) ← parseRawStatementTokens tokens
      match head with
      | .declare name value | .typedDeclare name _ value | .mutableDeclare name _ value =>
        if !bindingNameAllowed name || name == "Object" || name == "Set" || bindings.contains name ||
            !sparseExpressionAllowed value bindings then none else
        return .declare name (.ordinary value) :: (← sparseStatements fuel (name :: bindings)
          (mutableBindings.filter (· != name)) rest)
      | .assign ⟨.variable name, value⟩ =>
        if !mutableBindings.contains name || !bindings.contains name || !sparseExpressionAllowed value bindings then none else
        return .rebind name value :: (← sparseStatements fuel bindings mutableBindings rest)
      | .evaluate value =>
        if !sparseExpressionAllowed value bindings then none else
        return .evaluate value :: (← sparseStatements fuel bindings mutableBindings rest)
      | _ => none

/-- Explicit sparse-array fragment entry with fresh read-only declarations.
EOF is an ASI boundary. General scope/TDZ/live-cells, coercion, private reads,
object calls and callbacks are not supplied by this indexed-only runtime. -/
def parseSparseSequence (text : String) (allowedBindings : List String) (mutableBindings : List String := []) :
    Option (List SparseStmt) := do
  if !allowedBindings.all bindingNameAllowed || !mutableBindings.all bindingNameAllowed then none else
  let tokens ← tokenizePrivateControl text
  sparseStatements (tokens.length + 2) allowedBindings mutableBindings (tokens ++ [.lineBreak])

/-- Saved base and primitive natural numeric index. This models neither generic
ToPropertyKey nor its potentially repeated object-coercion effects. -/
structure SparseReference where
  array : Nat
  index : Nat
  deriving Repr, DecidableEq

def sparseRead (receiver key : Value) (state : IndexedState) : Except EvalError Value :=
  match receiver, key with
  | .array reference, .number (.ofNat index) =>
    if index < maximumArrayLength then
      match state.heap[reference]? with
      | none => .error .invalidReference
      | some array => .ok (numericGet array index)
    else .error .unsupported
  | .array reference, .string [108, 101, 110, 103, 116, 104] =>
    match state.heap[reference]? with
    | none => .error .invalidReference
    | some array => .ok (.number array.length)
  | _, _ => .error .unsupported

def sparseIntrinsic (receiver : Nat) (method : String) (arguments : List Value)
    (state : IndexedState) : Except EvalError (Value × IndexedState) :=
  match method, arguments with
  | "shift", [] => shiftAtDirect receiver state
  | "push", [value] => do
    let next ← pushAt receiver value state
    match next.heap[receiver]? with
    | some array => return (.number array.length, next)
    | none => .error .invalidReference
  | "concat", [argument] => concatAt receiver argument state
  | _, _ => .error .unsupported

mutual
  /-- Indexed heap is authoritative. Only these explicit value/array operations
  execute; no fallback consults an erased dense heap or ordinary callback model. -/
  def evalSparseExpression : Nat → Expr → IndexedState → Except EvalError (Value × IndexedState)
    | 0, _, _ => .error .exhausted
    | fuel + 1, expression, state => do
      match expression with
      | .variable name =>
        match state.environment.lookup name with
        | some value => return (value, state)
        | none => .error .missingVariable
      | .number value => return (.number value, state)
      | .string value => return (.string value, state)
      | .boolean value => return (.boolean value, state)
      | .null => return (.null, state)
      | .arrayLiteral [] => return allocateFresh [] state
      | .index base key =>
        let (base, state) ← evalSparseExpression fuel base state
        let (key, state) ← evalSparseExpression fuel key state
        let value ← sparseRead base key state
        return (value, state)
      | .property base key =>
        let (base, state) ← evalSparseExpression fuel base state
        let value ← sparseRead base (.string key) state
        return (value, state)
      | .typeAssertion value _ => evalSparseExpression fuel value state
      | .conditional condition yes no =>
        let (value, state) ← evalSparseExpression fuel condition state
        evalSparseExpression fuel (if truthy value then yes else no) state
      | .logicalNot expression =>
        let (value, state) ← evalSparseExpression fuel expression state
        return (.boolean (!truthy value), state)
      | .logicalOr left right =>
        let (value, state) ← evalSparseExpression fuel left state
        if truthy value then return (value, state) else evalSparseExpression fuel right state
      | .logicalAnd left right =>
        let (value, state) ← evalSparseExpression fuel left state
        if truthy value then evalSparseExpression fuel right state else return (value, state)
      | .nullish left right =>
        let (value, state) ← evalSparseExpression fuel left state
        if isNullish value then evalSparseExpression fuel right state else return (value, state)
      | .call base method arguments =>
        let (base, state) ← evalSparseExpression fuel base state
        match base with
        | .array reference =>
          match state.heap[reference]? with
          | none => .error .invalidReference
          | some _ =>
            if method == "shift" || method == "push" || method == "concat" then
              let (arguments, state) ← evalSparseArguments fuel arguments state
              sparseIntrinsic reference method arguments state
            else .error .unsupported
        | _ => .error .unsupported
      | _ => .error .unsupported

  def evalSparseArguments : Nat → List Expr → IndexedState → Except EvalError (List Value × IndexedState)
    | 0, _, _ => .error .exhausted
    | _ + 1, [], state => .ok ([], state)
    | fuel + 1, value :: rest, state => do
      let (value, state) ← evalSparseExpression fuel value state
      let (values, state) ← evalSparseArguments fuel rest state
      return (value :: values, state)
end

/-- Get the selected own-index value once. On the truthy path no RHS or Put
runs. On the falsy path RHS allocation precedes Put to the saved reference. -/
def evalSparseInitializer (fuel : Nat) (initializer : SparseInitializer) (state : IndexedState) :
    Except EvalError (Value × IndexedState) := do
  match initializer with
  | .ordinary value => evalSparseExpression fuel value state
  | .logicalOrAssign base index rhs =>
    let (base, state) ← evalSparseExpression fuel base state
    let (key, state) ← evalSparseExpression fuel index state
    match base, key with
    | .array reference, .number (.ofNat index) =>
      if index < maximumArrayLength then
        let array ← match state.heap[reference]? with
          | none => .error .invalidReference
          | some array => .ok array
        let selected := numericGet array index
        if truthy selected then return (selected, state) else
          let (value, state) ← evalSparseExpression fuel rhs state
          let state ← setAt reference index value state
          return (value, state)
      else .error .unsupported
    | _, _ => .error .unsupported

def executeSparseRebind (fuel : Nat) (mutableBindings : List String) (name : String) (rhs : Expr)
    (state : IndexedState) : Except EvalError IndexedState := do
  if !mutableBindings.contains name then .error .unsupported else
  let index := mutableBindingIndex name state.environment
  let (value, state) ← evalSparseExpression fuel rhs state
  match index with
  | none => .error .missingVariable
  | some index => return {state with environment := state.environment.set index (name, value)}

/-- Explicit retained linear execution. Fresh declarations are not made mutable
by the supplied authority list. No generic block/function/iteration scopes. -/
def executeSparseSequence : Nat → List String → List SparseStmt → IndexedState → Except EvalError IndexedState
  | 0, _, _, _ => .error .exhausted
  | _ + 1, _, [], state => .ok state
  | fuel + 1, mutableBindings, head :: tail, state => do
    match head with
    | .declare name initializer =>
      let (value, state) ← evalSparseInitializer fuel initializer state
      executeSparseSequence fuel (mutableBindings.filter (· != name)) tail
        {state with environment := (name, value) :: state.environment}
    | .evaluate value =>
      let (_, state) ← evalSparseExpression fuel value state
      executeSparseSequence fuel mutableBindings tail state
    | .rebind name rhs =>
      let state ← executeSparseRebind fuel mutableBindings name rhs state
      executeSparseSequence fuel mutableBindings tail state

/-- The truthy path returns the one fetched value with no RHS/Put effects. -/
theorem evalSparseInitializer_truthy (fuel : Nat) (base index rhs : Expr)
    (before baseState keyState : IndexedState) (reference position : Nat) (array : IndexedArray)
    (baseEval : evalSparseExpression fuel base before = .ok (.array reference, baseState))
    (keyEval : evalSparseExpression fuel index baseState = .ok (.number position, keyState))
    (legal : LegalArrayIndex position) (found : keyState.heap[reference]? = some array)
    (selected : truthy (numericGet array position) = true) :
    evalSparseInitializer fuel (.logicalOrAssign base index rhs) before =
      .ok (numericGet array position, keyState) := by
  change position < maximumArrayLength at legal
  simp only [evalSparseInitializer, baseEval, keyEval, legal, found, selected, bind, Except.bind,
    pure, Except.pure, ite_true]

/-- Falsy selection evaluates RHS before Put to the saved reference; both
array contents and heap length used by later operations are the current state. -/
theorem evalSparseInitializer_falsy (fuel : Nat) (base index rhs : Expr)
    (before baseState keyState rhsState written : IndexedState) (reference position : Nat)
    (array : IndexedArray) (value : Value)
    (baseEval : evalSparseExpression fuel base before = .ok (.array reference, baseState))
    (keyEval : evalSparseExpression fuel index baseState = .ok (.number position, keyState))
    (legal : LegalArrayIndex position) (found : keyState.heap[reference]? = some array)
    (selected : truthy (numericGet array position) = false)
    (right : evalSparseExpression fuel rhs keyState = .ok (value, rhsState))
    (write : setAt reference position value rhsState = .ok written) :
    evalSparseInitializer fuel (.logicalOrAssign base index rhs) before = .ok (value, written) := by
  change position < maximumArrayLength at legal
  simp only [evalSparseInitializer, baseEval, keyEval, legal, found, selected, right, write, bind, Except.bind,
    pure, Except.pure, Bool.false_eq_true, ite_true, ite_false]

end HonoLean.Upstream.SourceSubset
