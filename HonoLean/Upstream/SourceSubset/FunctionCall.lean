import HonoLean.Upstream.SourceSubset.PrivateCall
import HonoLean.Upstream.SourceSubset.PrivateControlParser
import HonoLean.Upstream.SourceSubset.SplitPath

namespace HonoLean.Upstream.SourceSubset

/-- One-parameter source bodies with frozen value/private-name captures. This
entry specializes the module arrow used by splitPath to undefined lexical this;
it is not general arrow capture, live lexical cells, or module linking. -/
structure StringFunctionClosure where
  program : Function
  environment : List (String × Value) := []
  privateNames : List (String × Nat) := []
  deriving Repr

structure FunctionTable where
  base : Nat
  entries : List StringFunctionClosure
  deriving Repr

/-- Actual method-table context, rather than a duplicate registry, prevents
function IDs from ambiguously naming old NoArg or private block closures. -/
def functionTableSeparated (methods : PrivateMethodTable) (functions : FunctionTable) (state : State) : Bool :=
  (functions.entries.isEmpty || decide (state.functions.length ≤ functions.base)) &&
    (functions.entries.isEmpty || methods.entries.isEmpty ||
      decide (functions.base + functions.entries.length ≤ methods.base) ||
      decide (methods.base + methods.entries.length ≤ functions.base))

/-- Property/index callees retain a native receiver reference and therefore
are not bare calls. Assertions preserve that distinction; value-producing
expressions such as conditionals or a prior call result are bare values. -/
def bareFunctionCallee : Expr → Bool
  | .property _ _ | .index _ _ | .privateProperty _ _ | .optionalIndex _ _ => false
  | .typeAssertion value _ => bareFunctionCallee value
  | _ => true

private def functionBodySafe : Nat → Bool → List Stmt → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, declarations, head :: tail =>
    let allowed := match head with
      | .declare _ value | .typedDeclare _ _ value | .mutableDeclare _ _ value =>
          declarations && privateControlExpressionAllowed 65536 value
      | .evaluate value | .ret value => privateControlExpressionAllowed 65536 value
      | .assign assignment =>
          (match assignment.target with | .variable _ => false | _ => true) &&
            privateControlExpressionAllowed 65536 assignment.target &&
            privateControlExpressionAllowed 65536 assignment.value
      | .branch condition body => privateControlExpressionAllowed 65536 condition && functionBodySafe fuel false body
      | .countedFor _ _ _ _ => false
    allowed && functionBodySafe fuel declarations tail

/-- Conservative admitted body specialization: no visible lexical increments,
counted loops or nested declarations. Heap effects remain supported. This is
not a claim that every Function accepted by the old parser is supported here. -/
def stringFunctionBodyAdmitted (closure : StringFunctionClosure) : Bool :=
  functionBodySafe 65536 true closure.program.body

def functionActivation (closure : StringFunctionClosure) (arguments : List Value) (before : State) : State :=
  {before with
    environment := (closure.program.parameter, arguments.headD .undefined) :: closure.environment
    thisValue := .undefined
    privates := {before.privates with names := closure.privateNames}}

def restoreFunctionCaller (before after : State) : State :=
  {after with
    environment := before.environment
    thisValue := before.thisValue
    privates := {after.privates with names := before.privates.names}}

def resolveStringFunction (table : FunctionTable) (callee : Value) : Except EvalError StringFunctionClosure :=
  match callee with
  | .function reference =>
    if reference < table.base then .error .unsupported else
    match table.entries[reference - table.base]? with
    | some closure => .ok closure
    | none => .error .invalidReference
  | _ => .error .unsupported

def invokeStringFunction (fuel limit : Nat) (closure : StringFunctionClosure)
    (arguments : List Value) (before : State) : Except EvalError (Value × State) := do
  if !stringFunctionBodyAdmitted closure then .error .unsupported else do
  match ← runBlock fuel closure.program.body (functionActivation closure arguments before) limit with
  | .normal after => pure (.undefined, restoreFunctionCaller before after)
  | .returned value after => pure (value, restoreFunctionCaller before after)

/-- Capture the callee first, evaluate every argument in order, then perform
representation/callability resolution. No new nested invoke rule is installed
in evalExpression. The undefined-this convention is the declared module-arrow
specialization above, not a universal bare-call rule for arbitrary arrows. -/
def runFunctionCall (fuel limit : Nat) (methods : PrivateMethodTable) (table : FunctionTable)
    (callee : Expr) (arguments : List Expr) (before : State) : Except EvalError (Value × State) := do
  if !bareFunctionCallee callee then .error .unsupported else do
  let (saved, state) ← evalExpression fuel limit callee before
  let (arguments, state) ← evalArguments fuel limit arguments state
  if !functionTableSeparated methods table state then .error .unsupported else do
  let closure ← resolveStringFunction table saved
  invokeStringFunction fuel limit closure arguments state

/-- The only new statement dispatch is an explicit root binding whose whole
initializer is an invoke. Typed metadata performs no argument/return checks. -/
def executeFunctionDeclaration (fuel limit : Nat) (methods : PrivateMethodTable) (table : FunctionTable)
    (statement : Stmt) (before : State) : Except EvalError State := do
  let (name, callee, arguments) ← match statement with
    | .declare name (.invoke callee arguments) | .typedDeclare name _ (.invoke callee arguments)
    | .mutableDeclare name _ (.invoke callee arguments) => pure (name, callee, arguments)
    | _ => throw .unsupported
  let (value, after) ← runFunctionCall fuel limit methods table callee arguments before
  pure {after with environment := (name, value) :: after.environment}

def executeFunctionStatements : Nat → Nat → PrivateMethodTable → FunctionTable → List Stmt → State →
    Except EvalError Completion
  | 0, _, _, _, _, _ => .error .exhausted
  | _ + 1, _, _, _, [], state => .ok (.normal state)
  | fuel + 1, limit, methods, table, statement :: tail, before => do
    match statement with
    | .declare _ (.invoke _ _) | .typedDeclare _ _ (.invoke _ _) | .mutableDeclare _ _ (.invoke _ _) =>
      let after ← executeFunctionDeclaration fuel limit methods table statement before
      executeFunctionStatements fuel limit methods table tail after
    | .branch _ _ | .countedFor _ _ _ _ => .error .unsupported
    | _ =>
      match ← execute fuel limit [statement] before with
      | .normal after => executeFunctionStatements fuel limit methods table tail after
      | .returned value after => pure (.returned value after)

private def callInitializerAdmitted (callee : Expr) (arguments : List Expr)
    (bindings names : List String) (allowThis : Bool) : Bool :=
  bareFunctionCallee callee && expressionAdmitted callee bindings names allowThis &&
    privateControlExpressionAllowed 65536 callee &&
    arguments.all (fun value => expressionAdmitted value bindings names allowThis && privateControlExpressionAllowed 65536 value)

private def functionStatementAdmitted (statement : Stmt) (bindings names : List String) (allowThis : Bool) : Bool :=
  match statement with
  | .declare name (.invoke callee arguments) | .typedDeclare name _ (.invoke callee arguments)
  | .mutableDeclare name _ (.invoke callee arguments) =>
    bindingNameAllowed name && name != "Object" && name != "Set" && !bindings.contains name &&
      callInitializerAdmitted callee arguments bindings names allowThis
  | .branch _ _ | .countedFor _ _ _ _ => false
  | _ => statementAdmitted statement bindings names allowThis &&
      (match statement with
        | .declare _ value | .typedDeclare _ _ value | .mutableDeclare _ _ value
        | .evaluate value | .ret value => privateControlExpressionAllowed 65536 value
        | .assign assignment => privateControlExpressionAllowed 65536 assignment.target &&
            privateControlExpressionAllowed 65536 assignment.value
        | _ => false)

private def functionStatements : Nat → List String → List String → Bool → List Token → Option (List Stmt × List Token)
  | 0, _, _, _, _ => none
  | fuel + 1, bindings, names, allowThis, tokens => do
    match skipTokenLines tokens with
    | .punctuation "}" :: rest => some ([], rest)
    | tokens =>
      let (head, rest) ← parseRawStatementTokens tokens
      if !functionStatementAdmitted head bindings names allowThis then none else do
      let next := match head with
        | .declare name _ | .typedDeclare name _ _ | .mutableDeclare name _ _ => name :: bindings
        | _ => bindings
      let (tail, rest) ← functionStatements fuel next names allowThis rest
      some (head :: tail, rest)

/-- Quote-aware line comments and existing raw statement grammar, with a
structural fresh-root declaration exception for function calls with arguments.
Ordinary parseBlock/evalExpression remain unchanged. -/
def parseFunctionStatements (text : String) (allowedBindings allowedPrivateNames : List String)
    (allowThis : Bool := false) : Option (List Stmt) := do
  if !allowedBindings.all bindingNameAllowed then none else do
  let tokens ← tokenizePrivateControl text
  let (body, rest) ← functionStatements (tokens.length + 1) allowedBindings allowedPrivateNames allowThis
    (tokens ++ [.punctuation "}"])
  if rest.isEmpty then some body else none

theorem functionActivation_this (closure : StringFunctionClosure) (arguments : List Value) (before : State) :
    (functionActivation closure arguments before).thisValue = .undefined := rfl

theorem functionActivation_parameter (closure : StringFunctionClosure) (arguments : List Value) (before : State) :
    (functionActivation closure arguments before).environment.lookup closure.program.parameter =
      some (arguments.headD .undefined) := by simp [functionActivation]

theorem restoreFunctionCaller_environment (before after : State) :
    (restoreFunctionCaller before after).environment = before.environment := rfl
theorem restoreFunctionCaller_this (before after : State) :
    (restoreFunctionCaller before after).thisValue = before.thisValue := rfl
theorem restoreFunctionCaller_private_names (before after : State) :
    (restoreFunctionCaller before after).privates.names = before.privates.names := rfl
theorem restoreFunctionCaller_heap (before after : State) :
    (restoreFunctionCaller before after).heap = after.heap := rfl

theorem invokeStringFunction_returned (fuel limit : Nat) (closure : StringFunctionClosure)
    (arguments : List Value) (before after : State) (value : Value)
    (safe : stringFunctionBodyAdmitted closure = true)
    (body : runBlock fuel closure.program.body (functionActivation closure arguments before) limit =
      .ok (.returned value after)) :
    invokeStringFunction fuel limit closure arguments before = .ok (value, restoreFunctionCaller before after) := by
  simp [invokeStringFunction, safe, body, bind, pure, Except.bind, Except.pure]

theorem runFunctionCall_resolved (fuel limit : Nat) (methods : PrivateMethodTable) (table : FunctionTable)
    (callee : Expr) (arguments : List Expr) (before calleeState argumentState : State)
    (reference : Nat) (values : List Value) (closure : StringFunctionClosure)
    (bare : bareFunctionCallee callee = true)
    (saved : evalExpression fuel limit callee before = .ok (.function reference, calleeState))
    (evaluated : evalArguments fuel limit arguments calleeState = .ok (values, argumentState))
    (separate : functionTableSeparated methods table argumentState = true)
    (bound : table.base ≤ reference)
    (found : table.entries[reference - table.base]? = some closure) :
    runFunctionCall fuel limit methods table callee arguments before =
      invokeStringFunction fuel limit closure values argumentState := by
  simp [runFunctionCall, bare, saved, evaluated, separate, resolveStringFunction,
    Nat.not_lt.mpr bound, found, bind, Except.bind]

theorem executeFunctionDeclaration_call (fuel limit : Nat) (methods : PrivateMethodTable) (table : FunctionTable)
    (name : String) (callee : Expr) (arguments : List Expr) (before after : State) (value : Value)
    (called : runFunctionCall fuel limit methods table callee arguments before = .ok (value, after)) :
    executeFunctionDeclaration fuel limit methods table (.declare name (.invoke callee arguments)) before =
      .ok {after with environment := (name, value) :: after.environment} := by
  simp [executeFunctionDeclaration, called, bind, pure, Except.bind, Except.pure]

/-- Concrete state endpoint for the actual body, retaining its newly allocated
array identity instead of using the older observation-only run function. -/
def splitPathCallState (before : State) (input : JSString) (limit : Nat) : State :=
  {before with heap := before.heap ++ [(dropLeadingEmpty ((input.splitOn (47 : UInt16)).take limit)).map Value.string]}

/-- Independent source-call contract: one fresh returned array containing a
slash partition result, exact old-array prefix and all caller/nonarray frames. -/
structure SplitPathCallContract (before : State) (input : JSString) (limit : Nat)
    (returned : Value) (after : State) : Prop where
  returnedReference : returned = .array before.heap.length
  freshReference : before.heap[before.heap.length]? = none
  output : ∃ parts, SplitPathContract limit input parts ∧ after.heap = before.heap ++ [parts.map Value.string]
  oldArrays : ∀ reference, reference < before.heap.length → after.heap[reference]? = before.heap[reference]?
  environment : after.environment = before.environment
  thisValue : after.thisValue = before.thisValue
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets

theorem splitPathCallState_contract (before : State) (input : JSString) (limit : Nat) :
    SplitPathCallContract before input limit (.array before.heap.length) (splitPathCallState before input limit) := by
  refine ⟨rfl, by simp, ⟨_, (contract_iff limit input _).mpr rfl, rfl⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro reference inside
  exact List.getElem?_append_left inside

theorem splitPathCallState_contents (before : State) (input : JSString) (limit : Nat) :
    (splitPathCallState before input limit).heap[before.heap.length]? =
      some ((dropLeadingEmpty ((input.splitOn (47 : UInt16)).take limit)).map Value.string) := by
  simp [splitPathCallState]

theorem splitPath_body_admitted (environment : List (String × Value)) (names : List (String × Nat)) :
    stringFunctionBodyAdmitted ⟨splitPathProgram, environment, names⟩ = true := by rfl

/-- Symbolic execution of the actual source body in ANY initial heap/scope.
Extra values are ignored only after their expressions have been evaluated by
runFunctionCall. This never calls the older state-discarding run helper. -/
theorem invoke_splitPath (extra limit : Nat) (closure : StringFunctionClosure) (before : State)
    (input : JSString) (rest : List Value) (source : closure.program = splitPathProgram) :
    invokeStringFunction (extra + 32) limit closure (.string input :: rest) before =
      .ok (.array before.heap.length, splitPathCallState before input limit) := by
  cases closure with
  | mk program environment names =>
    dsimp only at source
    subst program
    rw [invokeStringFunction, splitPath_body_admitted]
    generalize parts : (input.splitOn (47 : UInt16)).take limit = fields
    cases fields with
    | nil =>
      simp [runBlock, functionActivation, restoreFunctionCaller, splitPathProgram, execute,
        evalExpression, evalArguments, intrinsic, lookupVariable, withoutBindings, declaredNames, restoreCompletion,
        splitPathCallState, parts, dropLeadingEmpty, bind, pure, Except.bind, Except.pure, -List.map_take]
    | cons first remaining =>
      cases first with
      | nil =>
        simp [runBlock, functionActivation, restoreFunctionCaller, splitPathProgram, execute,
          evalExpression, evalArguments, intrinsic, lookupVariable, withoutBindings, declaredNames, restoreCompletion,
          splitPathCallState, parts, dropLeadingEmpty, bind, pure, Except.bind, Except.pure, -List.map_take]
      | cons unit tail =>
        simp [runBlock, functionActivation, restoreFunctionCaller, splitPathProgram, execute,
          evalExpression, evalArguments, intrinsic, lookupVariable, withoutBindings, declaredNames, restoreCompletion,
          splitPathCallState, parts, dropLeadingEmpty, bind, pure, Except.bind, Except.pure, -List.map_take]

theorem parsed_splitPath_call (extra limit : Nat) (before : State) (input : JSString) (rest : List Value)
    (environment : List (String × Value)) (names : List (String × Nat)) :
    (parse pinnedSource).map (fun program => invokeStringFunction (extra + 32) limit
      ⟨program, environment, names⟩ (.string input :: rest) before) =
      some (.ok (.array before.heap.length, splitPathCallState before input limit)) := by
  rw [parses_pinned_source, Option.map_some, invoke_splitPath extra limit _ before input rest rfl]

theorem parsed_splitPath_call_satisfies (extra limit : Nat) (before : State) (input : JSString)
    (environment : List (String × Value)) (names : List (String × Nat)) :
    ∃ returned after,
      (parse pinnedSource).map (fun program => invokeStringFunction (extra + 32) limit
        ⟨program, environment, names⟩ [.string input] before) = some (.ok (returned, after)) ∧
      SplitPathCallContract before input limit returned after :=
  ⟨_, _, parsed_splitPath_call extra limit before input [] environment names,
    splitPathCallState_contract before input limit⟩

end HonoLean.Upstream.SourceSubset
