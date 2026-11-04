import HonoLean.Upstream.SourceSubset.SparseSequence
import HonoLean.Upstream.ECMA2025.UnitRegExp

namespace HonoLean.Upstream.SourceSubset

open ECMA2025

/-- An explicit literal/call/optional/nullish extension. Literal means exact
single-unit global g; no old expression, value or state ABI is widened. -/
inductive RegExpExpr where
  | ordinary (value : Expr)
  | literal (unit : UInt16)
  | stringMatch (receiver : Expr) (argument : RegExpExpr)
  | optionalLength (value : RegExpExpr)
  | nullish (value : RegExpExpr) (fallback : Expr)
  deriving Repr

inductive RegExpStmt where
  | declare (name : String) (initializer : RegExpExpr)
  | sparse (statement : SparseStmt)
  deriving Repr

structure RegExpState where
  arrays : IndexedState := {}
  regexps : List UnitRegExpCell := []
  /-- Each successful exec has an internal result array. Their allocation
  identities/properties are projected out; execution traces retain their count
  and lastIndex effects. This is not a total native heap-allocation model. -/
  executions : List UnitExecution := []

inductive RegExpValue where
  | ordinary (value : Value)
  | regexp (reference : Nat)
  deriving Repr, DecidableEq

/-- One tracked global accumulator A is allocated on EVERY call, before exec,
including null results. Internal per-success exec arrays and unrelated RegExp
properties are outside this source-array projection. Frozen standard match/
@@match/exec, primitive-string receiver, no coercion, clean array prototypes,
legal native lengths and successful resources are interpretation premises. -/
def matchUnitRegExp (input : JSString) (reference : Nat) (before : RegExpState) :
    Except EvalError (Value × RegExpState) := do
  let cell ← match before.regexps[reference]? with
    | none => .error .invalidReference
    | some cell => .ok cell
  let accumulator := before.arrays.heap.length
  let allocated := {before with arrays := (allocateFresh [] before.arrays).2}
  let run := executeUnitGlobal input cell
  let matchValues := run.positions.map (fun _ => Value.string [cell.unit])
  if matchValues.length ≤ maximumArrayLength then
    let after := {allocated with
      arrays := {allocated.arrays with heap := allocated.arrays.heap.set accumulator (ofList matchValues)}
      regexps := allocated.regexps.set reference run.cell
      executions := allocated.executions ++ [run]}
    return (if matchValues.isEmpty then .null else .array accumulator, after)
  else .error .unsupported

/-- Receiver/method preparation precedes regex argument allocation. Unsupported
receivers fail closed outside the declared primitive-string domain; this does
not claim native failure-state/callability ordering for arbitrary receivers. -/
def evalRegExpExpression : Nat → RegExpExpr → RegExpState → Except EvalError (RegExpValue × RegExpState)
  | 0, _, _ => .error .exhausted
  | fuel + 1, expression, state => do
    match expression with
    | .ordinary value =>
      let (value, arrays) ← evalSparseExpression fuel value state.arrays
      return (.ordinary value, {state with arrays})
    | .literal unit =>
      return (.regexp state.regexps.length, {state with regexps := state.regexps ++ [⟨unit, 0⟩]})
    | .stringMatch receiver argument =>
      let (receiver, arrays) ← evalSparseExpression fuel receiver state.arrays
      match receiver with
      | .string contents =>
        let (argument, state) ← evalRegExpExpression fuel argument {state with arrays}
        match argument with
        | .regexp reference =>
          let (value, state) ← matchUnitRegExp contents reference state
          return (.ordinary value, state)
        | _ => .error .unsupported
      | _ => .error .unsupported
    | .optionalLength value =>
      let (value, state) ← evalRegExpExpression fuel value state
      match value with
      | .ordinary (.null) | .ordinary (.undefined) => return (.ordinary .undefined, state)
      | .ordinary (.array reference) =>
        match state.arrays.heap[reference]? with
        | none => .error .invalidReference
        | some array => return (.ordinary (.number array.length), state)
      | _ => .error .unsupported
    | .nullish value fallback =>
      let (value, state) ← evalRegExpExpression fuel value state
      match value with
      | .ordinary value =>
        if isNullish value then
          let (value, arrays) ← evalSparseExpression fuel fallback state.arrays
          return (.ordinary value, {state with arrays})
        else return (.ordinary value, state)
      | _ => .error .unsupported

/-- Retained mixed execution. Source declarations only bind ordinary Values;
first-class regex bindings, module live cells and general statement scopes are
not modeled by this selected fragment entry. -/
def executeRegExpSequence : Nat → List RegExpStmt → RegExpState → Except EvalError RegExpState
  | 0, _, _ => .error .exhausted
  | _ + 1, [], state => .ok state
  | fuel + 1, head :: tail, state => do
    match head with
    | .declare name initializer =>
      let (value, state) ← evalRegExpExpression fuel initializer state
      match value with
      | .ordinary value => executeRegExpSequence fuel tail {state with arrays := {state.arrays with environment := (name, value) :: state.arrays.environment}}
      | _ => .error .unsupported
    | .sparse statement =>
      let arrays ← executeSparseSequence (fuel + 1) [] [statement] state.arrays
      executeRegExpSequence fuel tail {state with arrays}

inductive RegExpToken where
  | ordinary (token : Token)
  | literal (unit : UInt16)
  deriving Repr, DecidableEq

private def flagChar (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') || ('A' ≤ character && character ≤ 'Z') ||
    ('0' ≤ character && character ≤ '9') || character == '_' || character == '$'

/-- Exactly one ASCII literal atom or escaped slash, then exactly global g.
Regex metacharacters/other escapes/flags/division are outside this grammar. -/
private def literalTail (characters : List Char) : Option (UInt16 × List Char) := do
  let (atom, rest) ← match characters with
    | '\\' :: '/' :: '/' :: 'g' :: rest => some ('/', rest)
    | atom :: '/' :: 'g' :: rest =>
      if atom.val < 128 && atom != '\n' && atom != '\r' &&
          !(['\\', '/', '.', '^', '$', '*', '+', '?', '(', ')', '[', ']', '{', '}', '|'].contains atom) then some (atom, rest) else none
    | _ => none
  if rest.head?.any flagChar then none else some (UInt16.ofNat atom.toNat, rest)

private def regexpTokens : Nat → Option Char → List Char → List Char → Option (List RegExpToken)
  | 0, _, _, _ => none
  | _ + 1, none, pending, [] => (tokenizeFragment (String.ofList pending.reverse)).map (List.map RegExpToken.ordinary)
  | _ + 1, some _, _, [] => none
  | fuel + 1, quote, pending, character :: rest => do
    match quote with
    | some delimiter =>
      if character == '\\' || character == '\n' || character == '\r' then none else
      regexpTokens fuel (if character == delimiter then none else quote) (character :: pending) rest
    | none =>
      if character == '\'' || character == '"' then regexpTokens fuel (some character) (character :: pending) rest
      else if character == '/' then
        let frontTokens ← tokenizeFragment (String.ofList pending.reverse)
        let (unit, rest) ← literalTail rest
        let suffix ← regexpTokens fuel none [] rest
        return frontTokens.map RegExpToken.ordinary ++ .literal unit :: suffix
      else regexpTokens fuel none (character :: pending) rest

/-- Shared lexer for ordinary spans, with a separate real regex-literal token.
Quoted slashes remain ordinary strings. Comments/templates/escaped strings
remain unsupported rather than being removed or interpreted as regex syntax. -/
def tokenizeRegExpSequence (text : String) : Option (List RegExpToken) :=
  regexpTokens (text.toList.length + 1) none [] text.toList

private def ordinaryPrefix : List RegExpToken → List Token × List RegExpToken
  | .ordinary token :: rest =>
    let tail := ordinaryPrefix rest
    (token :: tail.1, tail.2)
  | rest => ([], rest)

private def regexBoundary : List RegExpToken → Option (List RegExpToken)
  | .ordinary (.punctuation ";") :: rest => some rest
  | .ordinary .lineBreak :: rest =>
    match (ordinaryPrefix rest).1 |> skipTokenLines with
    | .punctuation "-" :: _ | .punctuation "(" :: _ | .punctuation "[" :: _
    | .punctuation "." :: _ | .punctuation "?." :: _ => none
    | _ => some rest
  | _ => none

private def skipRegexLines (tokens : List RegExpToken) : List RegExpToken :=
  tokens.dropWhile (fun token => token == .ordinary .lineBreak)

private def parseRegexDeclaration (tokens : List RegExpToken) (bindings : List String) :
    Option (String × RegExpExpr × List RegExpToken) := do
  let (name, tokens) ← match tokens with
    | .ordinary (.name "const") :: .ordinary (.name name) :: .ordinary (.punctuation "=") :: rest => some (name, rest)
    | _ => none
  if !bindingNameAllowed name || name == "Object" || name == "Set" || bindings.contains name then none else
  let (frontTokens, literalRest) := ordinaryPrefix tokens
  let receiverTokens ← match frontTokens.reverse with
    | .punctuation "(" :: .name "match" :: .punctuation "." :: receiver => some receiver.reverse
    | _ => none
  let (receiver, rest) ← parseRawExpressionTokens receiverTokens
  if !rest.isEmpty || !mutableSequenceExpressionAdmitted receiver bindings [] then none else
  let (unit, tail) ← match literalRest with
    | .literal unit :: .ordinary (.punctuation ")") :: tail => some (unit, tail)
    | _ => none
  let expression := RegExpExpr.stringMatch receiver (.literal unit)
  let (expression, tail) := match skipRegexLines tail with
    | .ordinary (.punctuation "?.") :: .ordinary (.name "length") :: rest => (.optionalLength expression, rest)
    | _ => (expression, tail)
  match skipRegexLines tail with
  | .ordinary (.punctuation "??") :: rest =>
    let (shared, suffix) := ordinaryPrefix rest
    let (fallback, remaining) ← parseRawExpressionTokens shared
    if !mutableSequenceExpressionAdmitted fallback bindings [] then none else
    let tail ← regexBoundary (remaining.map RegExpToken.ordinary ++ suffix)
    some (name, .nullish expression fallback, tail)
  | _ =>
    let tail ← regexBoundary tail
    some (name, expression, tail)

/-- Conservative token forwarding for explicit outer statement extensions. -/
def parseRegExpDeclarationTokens (tokens : List RegExpToken) (bindings : List String) :
    Option (String × RegExpExpr × List RegExpToken) := parseRegexDeclaration tokens bindings

def regExpOrdinaryPrefix (tokens : List RegExpToken) : List Token × List RegExpToken := ordinaryPrefix tokens

def skipRegExpTokenLines (tokens : List RegExpToken) : List RegExpToken := skipRegexLines tokens

private def regexStatements : Nat → List String → List RegExpToken → Option (List RegExpStmt)
  | 0, _, _ => none
  | fuel + 1, bindings, tokens => do
    let tokens := skipRegexLines tokens
    if tokens.isEmpty then some [] else
    match parseRegexDeclaration tokens bindings with
    | some (name, initializer, rest) => return .declare name initializer :: (← regexStatements fuel (name :: bindings) rest)
    | none => do
      let (shared, suffix) := ordinaryPrefix tokens
      match parseSparseLogicalDeclarationTokens shared bindings with
      | some (name, initializer, rest) => return .sparse (.declare name initializer) ::
          (← regexStatements fuel (name :: bindings) (rest.map RegExpToken.ordinary ++ suffix))
      | none => do
        let (statement, rest) ← parseRawStatementTokens shared
        let (statement, bindings) ← match statement with
          | .declare name value | .typedDeclare name _ value | .mutableDeclare name _ value =>
            if bindingNameAllowed name && name != "Object" && name != "Set" && !bindings.contains name &&
                mutableSequenceExpressionAdmitted value bindings [] then some (.declare name (.ordinary value), name :: bindings) else none
          | .evaluate value => if mutableSequenceExpressionAdmitted value bindings [] then some (.evaluate value, bindings) else none
          | _ => none
        return .sparse statement :: (← regexStatements fuel bindings (rest.map RegExpToken.ordinary ++ suffix))

def parseRegExpSequence (text : String) (allowedBindings : List String) : Option (List RegExpStmt) := do
  if !allowedBindings.all bindingNameAllowed then none else
  let tokens ← tokenizeRegExpSequence text
  regexStatements (tokens.length + 2) allowedBindings (tokens ++ [.ordinary .lineBreak])

def unitMatchValues (unit : UInt16) (input : JSString) : List Value :=
  (matchingPositions unit input).map (fun _ => .string [unit])

def unitMatchState (before : RegExpState) (reference : Nat) (input : JSString) (cell : UnitRegExpCell) : RegExpState :=
  {arrays := {before.arrays with heap := before.arrays.heap ++ [ofList (unitMatchValues cell.unit input)]}
   regexps := before.regexps.set reference ⟨cell.unit, 0⟩
   executions := before.executions ++ [executeUnitGlobal input cell]}

theorem matchUnitRegExp_found (before : RegExpState) (reference : Nat) (input : JSString) (cell : UnitRegExpCell)
    (found : before.regexps[reference]? = some cell) (legal : input.length ≤ maximumArrayLength) :
    matchUnitRegExp input reference before =
      .ok ((if (unitMatchValues cell.unit input).isEmpty then .null else .array before.arrays.heap.length),
        unitMatchState before reference input cell) := by
  have positions := (executeUnitGlobal_satisfies input cell).positions
  have bound : (matchingPositions cell.unit input).length ≤ maximumArrayLength :=
    Nat.le_trans (matchingPositions_length_le cell.unit input) legal
  have runCell : (executeUnitGlobal input cell).cell = ⟨cell.unit, 0⟩ := by
    simp [executeUnitGlobal, scanUnit_final_zero]
  simp [matchUnitRegExp, found, bound, positions, runCell, unitMatchState, unitMatchValues,
    allocateFresh, List.set_append_right, bind, Except.bind, pure, Except.pure]

def unitLiteralMatchState (before : RegExpState) (unit : UInt16) (input : JSString) : RegExpState :=
  {arrays := {before.arrays with heap := before.arrays.heap ++ [ofList (unitMatchValues unit input)]}
   regexps := before.regexps ++ [⟨unit, 0⟩]
   executions := before.executions ++ [executeUnitGlobal input ⟨unit, 0⟩]}

def unitCountExpression (receiver : Expr) (unit : UInt16) : RegExpExpr :=
  .nullish (.optionalLength (.stringMatch receiver (.literal unit))) (.number 0)

theorem evalRegExp_count (fuel : Nat) (receiver : Expr) (before : RegExpState) (unit : UInt16) (input : JSString)
    (receiverEval : evalSparseExpression (fuel + 3) receiver before.arrays = .ok (.string input, before.arrays))
    (legal : input.length ≤ maximumArrayLength) :
    evalRegExpExpression (fuel + 6) (unitCountExpression receiver unit) before =
      .ok (.ordinary (.number (matchingPositions unit input).length), unitLiteralMatchState before unit input) := by
  let literalState : RegExpState := {before with regexps := before.regexps ++ [⟨unit, 0⟩]}
  have literalFound : literalState.regexps[before.regexps.length]? = some ⟨unit, 0⟩ := by simp [literalState]
  have called := matchUnitRegExp_found literalState before.regexps.length input ⟨unit, 0⟩ literalFound legal
  have endpoint : unitMatchState literalState before.regexps.length input ⟨unit, 0⟩ = unitLiteralMatchState before unit input := by
    simp [unitMatchState, unitLiteralMatchState, literalState, List.set_append_right]
  simp only [unitCountExpression, evalRegExpExpression, receiverEval, bind, Except.bind, pure, Except.pure]
  rw [called, endpoint]
  cases casesPositions : matchingPositions unit input with
  | nil => simp [unitMatchValues, casesPositions, unitLiteralMatchState, pure, Except.pure, evalSparseExpression]
  | cons first rest => simp [unitMatchValues, casesPositions, unitLiteralMatchState, ofList, literalState]

/-- Independent endpoint contract for the tracked accumulator/regex stores.
It intentionally does not count or identify all native internal allocations. -/
structure UnitCountContract (before after : RegExpState) (unit : UInt16) (input : JSString) (value : Value) : Prop where
  count : value = .number (matchingPositions unit input).length
  countBound : (matchingPositions unit input).length ≤ input.length
  environment : after.arrays.environment = before.arrays.environment
  arrays : after.arrays.heap = before.arrays.heap ++ [ofList (unitMatchValues unit input)]
  oldArrays : ∀ reference, reference < before.arrays.heap.length →
    after.arrays.heap[reference]? = before.arrays.heap[reference]?
  accumulator : after.arrays.heap[before.arrays.heap.length]? = some (ofList (unitMatchValues unit input))
  regexps : after.regexps = before.regexps ++ [⟨unit, 0⟩]
  oldRegexps : ∀ reference, reference < before.regexps.length → after.regexps[reference]? = before.regexps[reference]?
  executions : after.executions = before.executions ++ [executeUnitGlobal input ⟨unit, 0⟩]
  matchContract : UnitMatchContract input unit (executeUnitGlobal input ⟨unit, 0⟩)

theorem unitLiteralMatchState_satisfies (before : RegExpState) (unit : UInt16) (input : JSString) :
    UnitCountContract before (unitLiteralMatchState before unit input) unit input (.number (matchingPositions unit input).length) := by
  refine ⟨rfl, matchingPositions_length_le unit input, rfl, rfl, ?_, ?_, rfl, ?_, rfl,
    executeUnitGlobal_satisfies input ⟨unit, 0⟩⟩
  · intro reference inside
    exact List.getElem?_append_left inside
  · simp [unitLiteralMatchState]
  · intro reference inside
    exact List.getElem?_append_left inside

theorem unitCount_index_legal (input : JSString) (unit : UInt16) (legal : input.length < maximumArrayLength) :
    LegalArrayIndex (matchingPositions unit input).length := by
  have bound := matchingPositions_length_le unit input
  change (matchingPositions unit input).length < maximumArrayLength
  omega

end HonoLean.Upstream.SourceSubset
