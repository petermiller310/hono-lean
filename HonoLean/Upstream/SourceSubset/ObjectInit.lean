import HonoLean.Upstream.SourceSubset.PrivateControlParser
import HonoLean.Upstream.ECMA2025.ObjectSpread

set_option autoImplicit false

namespace HonoLean.Upstream.SourceSubset

open ECMA2025

inductive ObjectInitItem where
  /-- Computed property definition, including data '__proto__', never the
  special uncomputed object-literal prototype-setter production. -/
  | property (key value : Expr)
  | spread (source : Expr)
  deriving Repr

inductive ObjectInitExpr where
  | ordinary (value : Expr)
  | conditional (condition : Expr) (yes no : ObjectInitExpr)
  | objectLiteral (items : List ObjectInitItem)
  deriving Repr

structure ObjectInitDecl where
  name : String
  initializer : ObjectInitExpr
  deriving Repr

def evalObjectInitItems : Nat → Nat → Nat → List ObjectInitItem → State → Except EvalError State
  | 0, _, _, _, _ => .error .exhausted
  | _ + 1, _, _, [], state => .ok state
  | fuel + 1, limit, target, head :: tail, state => do
    match head with
    | .property key value =>
      let (key, state) ← evalExpression fuel limit key state
      let key ← literalPropertyName key
      let (value, state) ← evalExpression fuel limit value state
      let state ← defineLiteralProperty target key value state
      evalObjectInitItems fuel limit target tail state
    | .spread source =>
      let (source, state) ← evalExpression fuel limit source state
      let state ← match source with
        | .null | .undefined => .ok state
        | .object reference => copyDataProperties fuel target reference state
        | _ => .error .unsupported
      evalObjectInitItems fuel limit target tail state

/-- Target allocation precedes every property/spread-source evaluation, in
particular the second private read in the actual conditional false arm. -/
def evalObjectInitExpression : Nat → Nat → ObjectInitExpr → State → Except EvalError (Value × State)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, limit, expression, state => do
    match expression with
    | .ordinary value => evalExpression fuel limit value state
    | .conditional condition yes no =>
      let (value, state) ← evalExpression fuel limit condition state
      evalObjectInitExpression fuel limit (if truthy value then yes else no) state
    | .objectLiteral items =>
      let (value, state) ← createLiteralObject state
      match value with
      | .object target =>
        let state ← evalObjectInitItems fuel limit target items state
        return (.object target, state)
      | _ => .error .unsupported

def executeObjectInit (fuel limit : Nat) (declaration : ObjectInitDecl) (state : State) : Except EvalError State := do
  let (value, state) ← evalObjectInitExpression fuel limit declaration.initializer state
  return {state with environment := (declaration.name, value) :: state.environment}

private def objectInitClosed : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
    match expression with
    | .invoke _ _ | .construct _ _ _ | .preIncrement _ => false
    | .variable _ | .this | .number _ | .string _ | .boolean _ | .null => true
    | .index left right | .optionalIndex left right | .strictEqual left right | .compare _ left right
    | .subtract left right | .logicalAnd left right | .logicalOr left right | .nullish left right =>
      objectInitClosed fuel left && objectInitClosed fuel right
    | .property value _ | .privateProperty value _ | .logicalNot value | .typeAssertion value _ => objectInitClosed fuel value
    | .conditional condition yes no => objectInitClosed fuel condition && objectInitClosed fuel yes && objectInitClosed fuel no
    | .call (.variable "Object") "create" [.null] => true
    | .call _ _ _ => false
    | .arrayLiteral entries => entries.all (fun entry => objectInitClosed fuel entry.2)
    | .objectLiteral entries => entries.all (fun entry => objectInitClosed fuel entry.1 && objectInitClosed fuel entry.2)

private def objectInitOrdinaryAdmitted (value : Expr) (bindings privateNames : List String) : Bool :=
  expressionAdmitted value bindings privateNames true && objectInitClosed 65536 value

/-- Find an outer conditional delimiter without inspecting quoted contents
(the shared lexer already produced string tokens). Nested grouping delimiters
are retained and validated by the ordinary expression grammar. -/
private def objectInitConditionalCut : Nat → Nat → List Token → List Token × List Token
  | 0, _, tokens => ([], tokens)
  | _ + 1, _, [] => ([], [])
  | fuel + 1, depth, token :: rest =>
    match token with
    | .punctuation "?" | .punctuation ":" =>
      if depth = 0 then ([], token :: rest) else
        let tail := objectInitConditionalCut fuel depth rest
        (token :: tail.1, tail.2)
    | .punctuation "(" | .punctuation "[" | .punctuation "{" =>
      let tail := objectInitConditionalCut fuel (depth + 1) rest
      (token :: tail.1, tail.2)
    | .punctuation ")" | .punctuation "]" | .punctuation "}" =>
      if depth = 0 then ([], token :: rest) else
        let tail := objectInitConditionalCut fuel (depth - 1) rest
        (token :: tail.1, tail.2)
    | _ =>
      let tail := objectInitConditionalCut fuel depth rest
      (token :: tail.1, tail.2)

mutual
  private def objectInitExpression : Nat → List String → List String → List Token → Option (ObjectInitExpr × List Token)
    | 0, _, _, _ => none
    | fuel + 1, bindings, privateNames, tokens => do
      let tokens := skipTokenLines tokens
      match tokens with
      | .punctuation "{" :: rest =>
        let (items, rest) ← objectInitItems fuel bindings privateNames rest
        some (.objectLiteral items, rest)
      | _ =>
        let (front, suffix) := objectInitConditionalCut (tokens.length + 1) 0 tokens
        match suffix with
        | .punctuation "?" :: rest =>
          let (condition, remaining) ← parseRawExpressionTokens front
          if !remaining.isEmpty || !objectInitOrdinaryAdmitted condition bindings privateNames then none else
          let (yes, rest) ← objectInitExpression fuel bindings privateNames rest
          let rest ← match skipTokenLines rest with | .punctuation ":" :: rest => some rest | _ => none
          let (no, rest) ← objectInitExpression fuel bindings privateNames rest
          some (.conditional condition yes no, rest)
        | _ =>
          let (value, rest) ← parseRawExpressionTokens tokens
          if objectInitOrdinaryAdmitted value bindings privateNames then some (.ordinary value, rest) else none

  private def objectInitItems : Nat → List String → List String → List Token → Option (List ObjectInitItem × List Token)
    | 0, _, _, _ => none
    | fuel + 1, bindings, privateNames, tokens => do
      match skipTokenLines tokens with
      | .punctuation "}" :: rest => some ([], rest)
      | tokens =>
        let (item, rest) ← match tokens with
          | .punctuation "..." :: rest => do
            let (value, rest) ← parseRawExpressionTokens rest
            if objectInitOrdinaryAdmitted value bindings privateNames then some (.spread value, rest) else none
          | .punctuation "[" :: rest => do
            let (key, rest) ← parseRawExpressionTokens rest
            let rest ← match skipTokenLines rest with | .punctuation "]" :: rest => some rest | _ => none
            let rest ← match skipTokenLines rest with | .punctuation ":" :: rest => some rest | _ => none
            let (value, rest) ← parseRawExpressionTokens rest
            if objectInitOrdinaryAdmitted key bindings privateNames && objectInitOrdinaryAdmitted value bindings privateNames then
              some (.property key value, rest) else none
          | _ => none
        match skipTokenLines rest with
        | .punctuation "}" :: rest => some ([item], rest)
        | .punctuation "," :: rest =>
          let (tail, rest) ← objectInitItems fuel bindings privateNames rest
          some (item :: tail, rest)
        | _ => none
end

/-- Source-preserving selected declaration. Uncomputed named properties,
including special '__proto__' syntax, are intentionally outside this grammar;
computed properties and copied names use CreateDataProperty. -/
def parseObjectInit (text : String) (allowedBindings : List String) (allowedPrivateNames : List String := []) : Option ObjectInitDecl := do
  if !allowedBindings.all bindingNameAllowed then none else
  let tokens ← tokenizePrivateControl text
  let (name, rest) ← match skipTokenLines tokens with
    | .name "const" :: .name name :: .punctuation "=" :: rest => some (name, rest)
    | _ => none
  if !bindingNameAllowed name || name == "Object" || name == "Set" || allowedBindings.contains name then none else
  let (value, rest) ← objectInitExpression (tokens.length + 1) allowedBindings allowedPrivateNames rest
  let rest := skipTokenLines rest
  let rest := match rest with | .punctuation ";" :: rest => skipTokenLines rest | _ => rest
  if rest.isEmpty then some ⟨name, value⟩ else none

/-- Compatibility spellings for proof clients; the canonical Driver API is
parseObjectInit / executeObjectInit. -/
def parseObjectInitDeclaration (text : String) (allowedBindings : List String) (allowedPrivateNames : List String := []) : Option ObjectInitDecl :=
  parseObjectInit text allowedBindings allowedPrivateNames

def executeObjectInitDeclaration (fuel limit : Nat) (declaration : ObjectInitDecl) (state : State) : Except EvalError State :=
  executeObjectInit fuel limit declaration state

def emptyLiteralState (before : State) : State := {before with objects := before.objects ++ [emptyLiteralObject]}

theorem evalObjectInit_empty (extra limit : Nat) (before : State) (root : OrdinaryObject)
    (allocated : before.objects[ordinaryObjectPrototype]? = some root) :
    evalObjectInitExpression (extra + 2) limit (.objectLiteral []) before =
      .ok (.object before.objects.length, emptyLiteralState before) := by
  simp [evalObjectInitExpression, createLiteralObject, allocated, evalObjectInitItems, emptyLiteralState,
    bind, Except.bind, pure, Except.pure]

/-- Pure source reads occur in the explicitly allocated state. The concrete
Node theorem derives this equation from initial private DATA facts; it is not
an assumed later layout or a copy-output premise. -/
theorem evalObjectInit_spread_fresh (extra limit : Nat) (before : State) (sourceExpression : Expr)
    (source : Nat) (sourceObject root : OrdinaryObject)
    (rootFound : before.objects[ordinaryObjectPrototype]? = some root)
    (sourceFound : before.objects[source]? = some sourceObject)
    (copyReady : CopyReady sourceObject) (wellFormed : WellFormedObject sourceObject)
    (sourceEval : evalExpression (extra + (ownStringKeys sourceObject).length + 2) limit sourceExpression (emptyLiteralState before) =
      .ok (.object source, emptyLiteralState before)) :
    evalObjectInitExpression (extra + (ownStringKeys sourceObject).length + 4) limit
      (.objectLiteral [.spread sourceExpression]) before =
        .ok (.object before.objects.length, spreadFreshState before sourceObject (ownStringKeys sourceObject)) ∧
    FreshObjectSpreadContract before (spreadFreshState before sourceObject (ownStringKeys sourceObject))
      source sourceObject (.object before.objects.length) := by
  have sourceBound := (List.getElem?_eq_some_iff.mp sourceFound).1
  have sourceAfter : (emptyLiteralState before).objects[source]? = some sourceObject :=
    (List.getElem?_append_left sourceBound).trans sourceFound
  have actual := copyDataPropertiesInOrder_fresh (extra + 1) before source sourceObject (ownStringKeys sourceObject)
    sourceFound copyReady (ownStringKeys_order sourceObject wellFormed)
  have copied : copyDataProperties (extra + (ownStringKeys sourceObject).length + 2) before.objects.length source (emptyLiteralState before) =
      .ok (spreadFreshState before sourceObject (ownStringKeys sourceObject)) := by
    simp only [copyDataProperties, sourceAfter, bind, Except.bind]
    have actualCopy := actual.1
    have budget : extra + 1 + (ownStringKeys sourceObject).length + 1 = extra + (ownStringKeys sourceObject).length + 2 := by omega
    rw [budget] at actualCopy
    exact actualCopy
  simp only [Nat.add_assoc, emptyLiteralState] at sourceEval copied
  constructor
  · simp [evalObjectInitExpression, createLiteralObject, rootFound, evalObjectInitItems, sourceEval, copied,
      Nat.add_assoc, bind, Except.bind, pure, Except.pure]
  · exact actual.2

theorem evalObjectInit_conditional (fuel limit : Nat) (condition : Expr) (yes no : ObjectInitExpr)
    (before after : State) (value : Value)
    (evaluated : evalExpression fuel limit condition before = .ok (value, after)) :
    evalObjectInitExpression (fuel + 1) limit (.conditional condition yes no) before =
      evalObjectInitExpression fuel limit (if truthy value then yes else no) after := by
  simp [evalObjectInitExpression, evaluated, bind, Except.bind]

end HonoLean.Upstream.SourceSubset
