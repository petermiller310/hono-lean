import HonoLean.Upstream.SourceSubset.RegExpSequence
import HonoLean.Upstream.SourceSubset.PrivateWrite
import HonoLean.Upstream.ECMA2025.ForIn

namespace HonoLean.Upstream.SourceSubset

open ECMA2025

structure ForInState where
  /-- Only nonarray fields are authoritative here. The view always takes
  environment and arrays from regexp.arrays, preserving this ambient frame. -/
  ambient : State := {}
  regexp : RegExpState := {}

def forInStateView (state : ForInState) : State := embedIndexedState state.ambient state.regexp.arrays

inductive ForInStmt where
  | forIn (binder : String) (collection : Expr) (body : List ForInStmt)
  | privateWrite (assignment : Assignment)
  | regexp (statement : RegExpStmt)
  | breakLoop
  deriving Repr

inductive ForInCompletion where
  | normal (state : ForInState)
  | breakLoop (state : ForInState)

/-- Pure admitted private-variable reference and variable RHS use the actual
shared assignment evaluator. Other shapes reject: no array/environment effects
are silently discarded. The source-domain theorem below connects its whole
computed result state to the retained private frame. -/
def executeForInPrivateWrite (fuel : Nat) (assignment : Assignment) (state : ForInState) :
    Except EvalError ForInState := do
  match assignment.target, assignment.value with
  | .privateProperty (.variable _) _, .variable _ =>
    let (_, after) ← executeAssignment fuel defaultSplitLimit assignment (forInStateView state)
    return {state with ambient := {state.ambient with privates := after.privates}}
  | _, _ => .error .unsupported

/-- The exact null-prototype own-string specialization. Head bound names are
uninitialized while its RHS is read, so an outer same-named binding cannot leak
through. The supported RHS is a pure private read; its enclosing env restores.
No body or body-input lookup occurs for an empty enumeration. -/
def forInChildren (fuel : Nat) (binder : String) (collection : Expr) (state : ForInState) : Except EvalError (List JSString) := do
  match collection with
  | .privateProperty (.variable _) _ =>
    let view := {forInStateView state with environment := withoutBindings state.regexp.arrays.environment [binder]}
    let (value, _) ← evalExpression fuel defaultSplitLimit collection view
    match value with
    | .object reference =>
      match state.ambient.objects[reference]? with
      | none => .error .invalidReference
      | some object =>
        if object.prototype.isNone then .ok (enumerableOwn object) else .error .unsupported
    | _ => .error .unsupported
  | _ => .error .unsupported

def restoreForInEnvironment (outer : List (String × Value)) (state : ForInState) : ForInState :=
  {state with regexp := {state.regexp with arrays := {state.regexp.arrays with environment := outer}}}

def bindForInKey (binder : String) (key : JSString) (state : ForInState) : ForInState :=
  {state with regexp := {state.regexp with arrays := {state.regexp.arrays with
    environment := (binder, .string key) :: state.regexp.arrays.environment}}}

mutual
  /-- Genuine bounded loop/completion execution, including no-break bodies.
  Admission allows no outer lexical writes/callbacks or ordinary-object changes;
  permitted private/array/regex effects survive scope restoration. -/
  def executeForInSequence : Nat → List ForInStmt → ForInState → Except EvalError ForInCompletion
    | 0, _, _ => .error .exhausted
    | _ + 1, [], state => .ok (.normal state)
    | fuel + 1, head :: tail, state => do
      match head with
      | .breakLoop => .ok (.breakLoop state)
      | .privateWrite assignment =>
        let state ← executeForInPrivateWrite fuel assignment state
        executeForInSequence fuel tail state
      | .regexp statement =>
        let regexp ← executeRegExpSequence (fuel + 1) [statement] state.regexp
        executeForInSequence fuel tail {state with regexp}
      | .forIn binder collection body =>
        let keys ← forInChildren fuel binder collection state
        let state ← executeForInKeys fuel binder body keys state
        executeForInSequence fuel tail state

  def executeForInKeys : Nat → String → List ForInStmt → List JSString → ForInState → Except EvalError ForInState
    | 0, _, _, _, _ => .error .exhausted
    | _ + 1, _, _, [], state => .ok state
    | fuel + 1, binder, body, key :: rest, state => do
      let outer := state.regexp.arrays.environment
      match ← executeForInSequence fuel body (bindForInKey binder key state) with
      | .breakLoop after => return restoreForInEnvironment outer after
      | .normal after => executeForInKeys fuel binder body rest (restoreForInEnvironment outer after)
end

/-- No callback/function/constructor dispatch or direct lexical effects can
hide a read/write of the unused loop binder in this selected body entry. -/
def forInExpressionClosed : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
    match expression with
    | .invoke _ _ | .construct _ _ _ | .preIncrement _ | .this => false
    | .variable _ | .string _ | .number _ | .boolean _ | .null => true
    | .property receiver _ | .privateProperty receiver _ | .typeAssertion receiver _ | .logicalNot receiver =>
      forInExpressionClosed fuel receiver
    | .index left right | .optionalIndex left right | .strictEqual left right | .compare _ left right
    | .subtract left right | .logicalAnd left right | .logicalOr left right | .nullish left right =>
      forInExpressionClosed fuel left && forInExpressionClosed fuel right
    | .conditional condition yes no => forInExpressionClosed fuel condition &&
      forInExpressionClosed fuel yes && forInExpressionClosed fuel no
    | .call receiver _ arguments => forInExpressionClosed fuel receiver && arguments.all (forInExpressionClosed fuel)
    | .arrayLiteral entries => entries.all (fun entry => forInExpressionClosed fuel entry.2)
    | .objectLiteral entries => entries.all (fun entry => forInExpressionClosed fuel entry.1 && forInExpressionClosed fuel entry.2)

def forInRegExpClosed : RegExpExpr → Bool
  | .ordinary value => forInExpressionClosed 65536 value
  | .literal _ => true
  | .stringMatch receiver argument => forInExpressionClosed 65536 receiver && forInRegExpClosed argument
  | .optionalLength value => forInRegExpClosed value
  | .nullish value fallback => forInRegExpClosed value && forInExpressionClosed 65536 fallback

private def sparseBodyClosed : SparseStmt → Bool
  | .declare _ (.ordinary value) | .evaluate value => forInExpressionClosed 65536 value
  | .declare _ (.logicalOrAssign base index rhs) => forInExpressionClosed 65536 base &&
      forInExpressionClosed 65536 index && forInExpressionClosed 65536 rhs
  | .rebind _ _ => false

private def forInBoundary : List RegExpToken → Option (List RegExpToken)
  | .ordinary (.punctuation ";") :: rest => some rest
  | .ordinary (.punctuation "}") :: rest => some (.ordinary (.punctuation "}") :: rest)
  | .ordinary .lineBreak :: rest =>
    match skipTokenLines (regExpOrdinaryPrefix rest).1 with
    | .punctuation "-" :: _ | .punctuation "(" :: _ | .punctuation "[" :: _
    | .punctuation "." :: _ | .punctuation "?." :: _ => none
    | _ => some rest
  | _ => none

private def forInBody : Nat → String → List String → List String → List RegExpToken →
    Option (List ForInStmt × List RegExpToken)
  | 0, _, _, _, _ => none
  | fuel + 1, binder, bindings, privateNames, tokens => do
    let tokens := skipRegExpTokenLines tokens
    let available := bindings.filter (· != binder)
    match tokens with
    | .ordinary (.punctuation "}") :: rest => some ([], rest)
    | .ordinary (.name "break") :: rest =>
      let rest ← forInBoundary rest
      let (tail, rest) ← forInBody fuel binder bindings privateNames rest
      some (.breakLoop :: tail, rest)
    | _ =>
      match parseRegExpDeclarationTokens tokens available with
      | some (name, initializer, rest) =>
        if name == binder || !forInRegExpClosed initializer then none else
        let (tail, rest) ← forInBody fuel binder (name :: bindings) privateNames rest
        some (.regexp (.declare name initializer) :: tail, rest)
      | none => do
        let (shared, suffix) := regExpOrdinaryPrefix tokens
        match parseSparseLogicalDeclarationTokens shared available with
        | some (name, initializer, rest) =>
          let statement := SparseStmt.declare name initializer
          if name == binder || !sparseBodyClosed statement then none else
          let (tail, rest) ← forInBody fuel binder (name :: bindings) privateNames (rest.map RegExpToken.ordinary ++ suffix)
          some (.regexp (.sparse statement) :: tail, rest)
        | none => do
          let (statement, rest) ← parseRawStatementTokens shared
          let (statement, nextBindings) ← match statement with
            | .assign assignment =>
              match assignment.target, assignment.value with
              | .privateProperty (.variable _) _, .variable _ =>
                if statementAdmitted statement available privateNames true then some (.privateWrite assignment, bindings) else none
              | _, _ => none
            | .declare name value | .typedDeclare name _ value | .mutableDeclare name _ value =>
              if name != binder && bindingNameAllowed name && name != "Object" && name != "Set" && !bindings.contains name &&
                  mutableSequenceExpressionAdmitted value available [] && forInExpressionClosed 65536 value then
                some (.regexp (.sparse (.declare name (.ordinary value))), name :: bindings) else none
            | .evaluate value =>
              if mutableSequenceExpressionAdmitted value available [] && forInExpressionClosed 65536 value then
                some (.regexp (.sparse (.evaluate value)), bindings) else none
            | _ => none
          let (tail, rest) ← forInBody fuel binder nextBindings privateNames (rest.map RegExpToken.ordinary ++ suffix)
          some (statement :: tail, rest)

/-- Actual for-in header/body tokens, including real break completion. The
binder is unavailable during the head RHS and unused throughout this admitted
body. No arbitrary loop lowering, object-value Get or native key-order claim. -/
def parseForInSequence (text : String) (allowedBindings : List String) (allowedPrivateNames : List String := []) :
    Option (List ForInStmt) := do
  if !allowedBindings.all bindingNameAllowed then none else
  let tokens ← tokenizeRegExpSequence text
  let (binder, rest) ← match skipRegExpTokenLines tokens with
    | .ordinary (.name "for") :: .ordinary (.punctuation "(") :: .ordinary (.name "const") ::
      .ordinary (.name binder) :: .ordinary (.name "in") :: rest => some (binder, rest)
    | _ => none
  if !bindingNameAllowed binder || binder == "Object" || binder == "Set" then none else
  let (shared, suffix) := regExpOrdinaryPrefix rest
  let (collection, rest) ← parseRawExpressionTokens shared
  match collection with
  | .privateProperty (.variable _) _ => pure ()
  | _ => none
  if !expressionAdmitted collection (allowedBindings.filter (· != binder)) allowedPrivateNames true then none else
  let rest ← match skipTokenLines rest with
    | .punctuation ")" :: rest => match skipTokenLines rest with
      | .punctuation "{" :: rest => some rest
      | _ => none
    | _ => none
  let (body, rest) ← forInBody (tokens.length + 1) binder (binder :: allowedBindings) allowedPrivateNames
    (rest.map RegExpToken.ordinary ++ suffix)
  if (skipRegExpTokenLines rest).isEmpty then some [.forIn binder collection body] else none

def forInDataState (before : ForInState) (owner identity : Nat) (value : Value) : ForInState :=
  {before with ambient := writePrivateDataState before.ambient owner identity value}

theorem forInDataState_view (before : ForInState) (owner identity : Nat) (value : Value) :
    forInStateView (forInDataState before owner identity value) =
      writePrivateDataState (forInStateView before) owner identity value := rfl

/-- Initial raw DATA/brand/ordinary-object facts determine the enumeration.
No has-children Boolean, body execution or m/params/queue input is assumed. -/
theorem forInChildren_private_data (fuel : Nat) (binder base spelling : String) (before : ForInState)
    (owner identity children : Nat) (ownerObject childrenObject : OrdinaryObject)
    (fields : List (Nat × PrivateElement))
    (different : base ≠ binder)
    (binding : before.regexp.arrays.environment.lookup base = some (.object owner))
    (lexical : before.ambient.privates.names.lookup spelling = some identity)
    (allocated : before.ambient.objects[owner]? = some ownerObject)
    (brand : before.ambient.privates.elements.lookup owner = some fields)
    (field : fields.lookup identity = some (.data (.object children)))
    (found : before.ambient.objects[children]? = some childrenObject)
    (nullPrototype : childrenObject.prototype = none) :
    forInChildren (fuel + 3) binder (.privateProperty (.variable base) spelling) before =
      .ok (enumerableOwn childrenObject) := by
  have absent : base ∉ [binder] := by simp [different]
  have headBinding : (withoutBindings before.regexp.arrays.environment [binder]).lookup base = some (.object owner) := by
    rw [lookup_withoutBindings _ _ _ absent]
    exact binding
  have brandValues : before.ambient.privates.slots.lookup owner =
      some (fields.map (fun (key, element) => (key, element.value))) := by
    rw [PrivateStore.slots_lookup, brand]
    rfl
  have fieldValue : (fields.map (fun (key, element) => (key, element.value))).lookup identity = some (.object children) := by
    rw [lookup_map_values, field]
    rfl
  simp [forInChildren, evalExpression, lookupVariable, forInStateView, embedIndexedState,
    headBinding, privateGet, lexical, allocated, brandValues, fieldValue, found, nullPrototype,
    bind, Except.bind, pure, Except.pure]

/-- The admitted variable-only private write uses actual reference capture,
RHS lookup and late DATA validation. Its full shared computed state is retained
exactly by forInDataState_view; no ordinary or array effect is lost. -/
theorem executeForInPrivateWrite_data (fuel : Nat) (base spelling rhs : String) (before : ForInState)
    (owner identity : Nat) (value old : Value) (object : OrdinaryObject) (fields : List (Nat × PrivateElement))
    (binding : before.regexp.arrays.environment.lookup base = some (.object owner))
    (right : before.regexp.arrays.environment.lookup rhs = some value)
    (lexical : before.ambient.privates.names.lookup spelling = some identity)
    (allocated : before.ambient.objects[owner]? = some object)
    (brand : before.ambient.privates.elements.lookup owner = some fields)
    (field : fields.lookup identity = some (.data old)) :
    executeForInPrivateWrite (fuel + 4) ⟨.privateProperty (.variable base) spelling, .variable rhs⟩ before =
      .ok (forInDataState before owner identity value) := by
  simp [executeForInPrivateWrite, executeAssignment, evalAssignmentReference, evalExpression, lookupVariable,
    forInStateView, embedIndexedState, binding, right, lexical, putAssignmentReference, privateSet,
    allocated, brand, field, forInDataState, writePrivateDataState, bind, Except.bind, pure, Except.pure]

theorem forInDataState_satisfies (before : ForInState) (owner identity : Nat) (value old : Value)
    (fields : List (Nat × PrivateElement))
    (brand : before.ambient.privates.elements.lookup owner = some fields)
    (field : fields.lookup identity = some (.data old)) :
    PrivateWriteContract (forInStateView before) (forInStateView (forInDataState before owner identity value)) owner identity value := by
  rw [forInDataState_view]
  exact writePrivateDataState_satisfies _ owner identity value old fields brand field

theorem executeForInKeys_break_first (fuel : Nat) (binder : String) (body : List ForInStmt)
    (key : JSString) (rest : List JSString) (before bodyAfter : ForInState)
    (bodyExec : executeForInSequence fuel body (bindForInKey binder key before) = .ok (.breakLoop bodyAfter)) :
    executeForInKeys (fuel + 1) binder body (key :: rest) before =
      .ok (restoreForInEnvironment before.regexp.arrays.environment bodyAfter) := by
  simp [executeForInKeys, bodyExec, bind, Except.bind, pure, Except.pure]

/-- Generic order abstraction, to be discharged by the actual source body
proof: every selected legal key breaks with the same scoped endpoint. The
concrete theorem derives this property from initial facts rather than adding it
to its initial domain. All legal orders are covered, not asserted native order. -/
theorem executeForInKeys_all_orders (fuel : Nat) (binder : String) (body : List ForInStmt)
    (object : OrdinaryObject) (before after : ForInState) (keys : List JSString)
    (legal : LegalForInOrder object keys)
    (hasKey : ∃ key, EnumerableName object key)
    (bodyBreak : ∀ key, EnumerableName object key → ∃ bodyAfter,
      executeForInSequence fuel body (bindForInKey binder key before) = .ok (.breakLoop bodyAfter) ∧
      restoreForInEnvironment before.regexp.arrays.environment bodyAfter = after) :
    executeForInKeys (fuel + 1) binder body keys before = .ok after := by
  cases keys with
  | nil =>
    obtain ⟨key, found⟩ := hasKey
    have impossible := (legal.complete key).mpr found
    cases impossible
  | cons key rest =>
    have found := (legal.complete key).mp (by simp)
    obtain ⟨bodyAfter, executed, restored⟩ := bodyBreak key found
    rw [executeForInKeys_break_first fuel binder body key rest before bodyAfter executed, restored]

theorem executeForInSequence_empty_loop (fuel : Nat) (binder : String) (collection : Expr)
    (body : List ForInStmt) (before : ForInState)
    (empty : forInChildren (fuel + 2) binder collection before = .ok []) :
    executeForInSequence (fuel + 3) [.forIn binder collection body] before = .ok (.normal before) := by
  simp [executeForInSequence, empty, executeForInKeys, bind, Except.bind]

theorem executeForInKeys_empty_order (fuel : Nat) (binder : String) (body : List ForInStmt)
    (object : OrdinaryObject) (before : ForInState) (keys : List JSString)
    (legal : LegalForInOrder object keys) (noneEnumerable : ¬∃ key, EnumerableName object key) :
    executeForInKeys (fuel + 1) binder body keys before = .ok before := by
  cases keys with
  | nil => rfl
  | cons key rest =>
    have found := (legal.complete key).mp (by simp)
    exact False.elim (noneEnumerable ⟨key, found⟩)

end HonoLean.Upstream.SourceSubset
