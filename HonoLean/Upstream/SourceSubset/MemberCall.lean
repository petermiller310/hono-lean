import HonoLean.Upstream.SourceSubset.FunctionCall

set_option autoImplicit false

namespace HonoLean.Upstream.SourceSubset

/-- Genuine ordinary method syntax. This is neither an arrow nor a private
method produced by inserting a synthetic # or dummy formal. -/
structure MemberMethod where
  name : String
  parameter : String
  body : List Stmt
  deriving Repr

/-- Explicit source closure input. Native method creation, home objects/super,
module live cells, bound functions and proxy calls are outside this entry. -/
structure MemberClosure where
  program : MemberMethod
  environment : List (String × Value) := []
  privateNames : List (String × Nat) := []
  deriving Repr

structure MemberTable where
  base : Nat
  entries : List MemberClosure
  deriving Repr

/-- The NEW member range is disjoint from every older range, checked on the
post-argument state. This does not validate the older ranges against one another.
Rejection is a model-domain error, not a native noncallability theorem. -/
def memberTableSeparated (methods : PrivateMethodTable) (functions : FunctionTable)
    (members : MemberTable) (state : State) : Bool :=
  (members.entries.isEmpty || decide (state.functions.length ≤ members.base)) &&
  (members.entries.isEmpty || methods.entries.isEmpty ||
    decide (members.base + members.entries.length ≤ methods.base) ||
    decide (methods.base + methods.entries.length ≤ members.base)) &&
  (members.entries.isEmpty || functions.entries.isEmpty ||
    decide (members.base + members.entries.length ≤ functions.base) ||
    decide (functions.base + functions.entries.length ≤ members.base))

private def memberClosedExpression : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
    match expression with
    | .invoke _ _ | .construct _ _ _ | .preIncrement _ => false
    | .variable _ | .this | .string _ | .number _ | .null | .boolean _ => true
    | .property receiver _ | .privateProperty receiver _ | .logicalNot receiver | .typeAssertion receiver _ =>
      memberClosedExpression fuel receiver
    | .index left right | .optionalIndex left right | .strictEqual left right | .subtract left right
    | .compare _ left right | .logicalAnd left right | .logicalOr left right | .nullish left right =>
      memberClosedExpression fuel left && memberClosedExpression fuel right
    | .conditional condition yes no => memberClosedExpression fuel condition &&
      memberClosedExpression fuel yes && memberClosedExpression fuel no
    | .call receiver _ arguments => memberClosedExpression fuel receiver && arguments.all (memberClosedExpression fuel)
    | .arrayLiteral elements => elements.all (fun element => memberClosedExpression fuel element.2)
    | .objectLiteral fields => fields.all (fun field => memberClosedExpression fuel field.1 && memberClosedExpression fuel field.2)

private def memberBodySafe : Nat → Bool → List Stmt → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, declarations, head :: tail =>
    let safe := match head with
      | .declare _ value | .typedDeclare _ _ value | .mutableDeclare _ _ value => declarations && memberClosedExpression 65536 value
      | .evaluate value | .ret value => memberClosedExpression 65536 value
      | .assign assignment =>
        (match assignment.target with | .variable _ => false | _ => true) &&
          memberClosedExpression 65536 assignment.target && memberClosedExpression 65536 assignment.value
      | .branch condition body => memberClosedExpression 65536 condition && memberBodySafe fuel false body
      | .countedFor _ _ _ _ => false
    safe && memberBodySafe fuel declarations tail

/-- Conservative body effects: shared ordinary statements/builtins/private
DATA operations, no lexical writes/increments, callback invokes, nested block
member dispatch, loops or nested declarations. Manual AST admission alone is
not a complete native frontend or closure-creation adequacy claim. -/
def memberBodyAdmitted (closure : MemberClosure) : Bool := memberBodySafe 65536 true closure.program.body

def memberActivation (closure : MemberClosure) (receiver : Value) (arguments : List Value) (before : State) : State :=
  {before with
    environment := (closure.program.parameter, arguments.headD .undefined) :: closure.environment
    thisValue := receiver
    privates := {before.privates with names := closure.privateNames}}

def restoreMemberCaller (before after : State) : State :=
  {after with
    environment := before.environment
    thisValue := before.thisValue
    privates := {after.privates with names := before.privates.names}}

def resolveMemberClosure (table : MemberTable) (callee : Value) : Except EvalError MemberClosure :=
  match callee with
  | .function reference =>
    if reference < table.base then .error .unsupported else
    match table.entries[reference - table.base]? with
    | some closure => .ok closure
    | none => .error .invalidReference
  | _ => .error .unsupported

/-- Actual return Value and body state are retained. A normally completed body
returns undefined. Except carries no partial error state or rollback promise. -/
def invokeMemberClosure (fuel limit : Nat) (closure : MemberClosure) (receiver : Value)
    (arguments : List Value) (before : State) : Except EvalError (Value × State) := do
  if !memberBodyAdmitted closure then .error .unsupported else do
  match ← runBlock fuel closure.program.body (memberActivation closure receiver arguments before) limit with
  | .normal after => pure (.undefined, restoreMemberCaller before after)
  | .returned value after => pure (value, restoreMemberCaller before after)

/-- Receiver evaluation and CURRENT ordinary Get precede all arguments. The
prepared receiver/callee are saved; resolution uses that callee after argument
effects. No builtin is selected from the method spelling, and no RegExpExec
fallback or object/null return restriction is introduced. Old nested expression
semantics are unchanged; arguments use the existing shared evalArguments. -/
def runMemberCall (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (receiver : Expr) (method : String) (arguments : List Expr) (before : State) : Except EvalError (Value × State) := do
  let (receiver, state) ← evalExpression fuel limit receiver before
  let saved ← prepareMethod receiver method state
  let (arguments, state) ← evalArguments fuel limit arguments state
  if !memberTableSeparated methods functions members state then .error .unsupported else do
  match saved with
  | .member receiver callee =>
    let closure ← resolveMemberClosure members callee
    invokeMemberClosure fuel limit closure receiver arguments state
  | .standard _ _ => .error .unsupported

/-- Only a root const whose entire initializer is one one-argument member call
is newly dispatched. The original shared Stmt/Expr is retained. -/
def executeMemberDeclaration (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable)
    (members : MemberTable) (declaration : Stmt) (before : State) : Except EvalError State := do
  match declaration with
  | .declare name (.call receiver method [argument]) =>
    let (returned, after) ← runMemberCall fuel limit methods functions members receiver method [argument] before
    pure {after with environment := (name, returned) :: after.environment}
  | _ => .error .unsupported

/-- Parse a genuine strict ordinary method with one plain formal. Body this is
explicitly admitted; captured names may be read but never lexically written.
Private names remain an explicit lexical-scope input. Annotation, arrow,
constructor, async/generator, super and arguments syntax are not manufactured. -/
def parseMemberMethod (text : String) (capturedBindings allowedPrivateNames : List String) : Option MemberMethod := do
  if !capturedBindings.all bindingNameAllowed then none else do
  let tokens ← tokenizePrivateControl text
  let (name, parameter, rest) ← match skipTokenLines tokens with
    | .name name :: .punctuation "(" :: .name parameter :: .punctuation ")" :: .punctuation "{" :: rest =>
      if bindingNameAllowed name && name != "constructor" && bindingNameAllowed parameter && parameter != "Object" && parameter != "Set" then
        some (name, parameter, rest) else none
    | _ => none
  let captures := capturedBindings.filter (fun name => name != parameter)
  let (body, rest) ← parseBodyTokens rest (parameter :: captures) allowedPrivateNames true
  let method : MemberMethod := ⟨name, parameter, body⟩
  if (skipTokenLines rest).isEmpty && memberBodyAdmitted ⟨method, [], []⟩ then some method else none

/-- Statement/expression tokenization and admission are reused for operands;
the old parser's call whitelist is NOT bypassed inside either operand. Only
this complete root member-call form has the extra dispatch admission. -/
def parseMemberDeclaration (text : String) (allowedBindings allowedPrivateNames : List String)
    (allowThis : Bool := false) : Option Stmt := do
  if !allowedBindings.all bindingNameAllowed then none else do
  let tokens ← tokenizePrivateControl text
  let (declaration, rest) ← parseRawStatementTokens (tokens ++ [.lineBreak])
  if !(skipTokenLines rest).isEmpty then none else do
  match declaration with
  | .declare name (.call receiver _ [argument]) =>
    if bindingNameAllowed name && name != "Object" && name != "Set" && !allowedBindings.contains name &&
      expressionAdmitted receiver allowedBindings allowedPrivateNames allowThis &&
      expressionAdmitted argument allowedBindings allowedPrivateNames allowThis &&
      memberClosedExpression 65536 receiver && memberClosedExpression 65536 argument then some declaration else none
  | _ => none

/-- Operational body relation: it exposes the actual shared runBlock completion
rather than supplying a desired match/result oracle or an independent regex
specification. Public source-entry contracts can consume this execution trace. -/
def MemberBodyExecution (fuel limit : Nat) (closure : MemberClosure) (receiver : Value) (arguments : List Value)
    (before : State) (returned : Value) (after : State) : Prop :=
  memberBodyAdmitted closure = true ∧ ∃ completion,
    runBlock fuel closure.program.body (memberActivation closure receiver arguments before) limit = .ok completion ∧
    match completion with
    | .normal bodyAfter => returned = .undefined ∧ after = restoreMemberCaller before bodyAfter
    | .returned value bodyAfter => returned = value ∧ after = restoreMemberCaller before bodyAfter

theorem invokeMemberClosure_iff (fuel limit : Nat) (closure : MemberClosure) (receiver : Value) (arguments : List Value)
    (before after : State) (returned : Value) :
    invokeMemberClosure fuel limit closure receiver arguments before = .ok (returned, after) ↔
      MemberBodyExecution fuel limit closure receiver arguments before returned after := by
  cases safe : memberBodyAdmitted closure with
  | false => simp [invokeMemberClosure, MemberBodyExecution, safe]
  | true =>
    cases body : runBlock fuel closure.program.body (memberActivation closure receiver arguments before) limit with
    | error error => simp [invokeMemberClosure, MemberBodyExecution, safe, body, bind, Except.bind]
    | ok completion =>
      cases completion <;> simp [invokeMemberClosure, MemberBodyExecution, safe, body, eq_comm, bind, Except.bind, pure, Except.pure]

theorem runMemberCall_resolved (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (receiver : Expr) (method : String) (arguments : List Expr) (before receiverState argumentState : State)
    (receiverValue : Value) (reference : Nat) (values : List Value) (closure : MemberClosure)
    (evaluatedReceiver : evalExpression fuel limit receiver before = .ok (receiverValue, receiverState))
    (prepared : prepareMethod receiverValue method receiverState = .ok (.member receiverValue (.function reference)))
    (evaluatedArguments : evalArguments fuel limit arguments receiverState = .ok (values, argumentState))
    (separated : memberTableSeparated methods functions members argumentState = true)
    (bound : members.base ≤ reference) (found : members.entries[reference - members.base]? = some closure) :
    runMemberCall fuel limit methods functions members receiver method arguments before =
      invokeMemberClosure fuel limit closure receiverValue values argumentState := by
  simp only [runMemberCall, evaluatedReceiver, bind, Except.bind]
  rw [prepared]
  simp [evaluatedArguments, separated, resolveMemberClosure,
    Nat.not_lt.mpr bound, found]

theorem executeMemberDeclaration_call (fuel limit : Nat) (methods : PrivateMethodTable) (functions : FunctionTable)
    (members : MemberTable) (name method : String) (receiver argument : Expr) (before after : State) (returned : Value)
    (called : runMemberCall fuel limit methods functions members receiver method [argument] before = .ok (returned, after)) :
    executeMemberDeclaration fuel limit methods functions members (.declare name (.call receiver method [argument])) before =
      .ok {after with environment := (name, returned) :: after.environment} := by
  simp [executeMemberDeclaration, called, bind, pure, Except.bind, Except.pure]

theorem memberActivation_this (closure : MemberClosure) (receiver : Value) (arguments : List Value) (before : State) :
    (memberActivation closure receiver arguments before).thisValue = receiver := rfl

theorem memberActivation_parameter (closure : MemberClosure) (receiver : Value) (arguments : List Value) (before : State) :
    (memberActivation closure receiver arguments before).environment.lookup closure.program.parameter = some (arguments.headD .undefined) := by
  simp [memberActivation]

theorem invokeMemberClosure_caller_frames (fuel limit : Nat) (closure : MemberClosure) (receiver : Value) (arguments : List Value)
    (before after : State) (returned : Value)
    (called : invokeMemberClosure fuel limit closure receiver arguments before = .ok (returned, after)) :
    after.environment = before.environment ∧ after.thisValue = before.thisValue ∧ after.privates.names = before.privates.names := by
  obtain ⟨_, completion, _, result⟩ := (invokeMemberClosure_iff fuel limit closure receiver arguments before after returned).mp called
  cases completion <;> obtain ⟨_, rfl⟩ := result <;> exact ⟨rfl, rfl, rfl⟩

end HonoLean.Upstream.SourceSubset
