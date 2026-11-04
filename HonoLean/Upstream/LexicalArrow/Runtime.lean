import HonoLean.Upstream.LexicalArrow.Syntax

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.LexicalArrow
open SourceSubset ECMA2025 GetPatternBody

def resolveBinding : Nat → Runtime → EnvironmentRef → String → Except LexicalError CellRef
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, world, environment, name => do
    let frame ← match world.environments[environment]? with
      | some frame => .ok frame | none => .error .invalidEnvironment
    match frame.bindings.lookup name with
    | some reference => pure reference
    | none => match frame.parent with
      | some parent => resolveBinding fuel world parent name
      | none => .error .missingBinding

def getBindingValue (fuel : Nat) (world : Runtime) (environment : EnvironmentRef) (name : String) : Except LexicalError Value := do
  let reference ← resolveBinding fuel world environment name
  let cell ← match world.cells[reference]? with
    | some cell => .ok cell | none => .error .invalidCell
  match cell.value with
  | some value => .ok value
  | none => .error .temporalDeadZone

def initializeCell (world : Runtime) (reference : CellRef) (value : Value) : Except LexicalError Runtime := do
  let cell ← match world.cells[reference]? with
    | some cell => .ok cell | none => .error .invalidCell
  if cell.value.isSome then .error .alreadyInitialized else
    pure {world with cells := world.cells.set reference {cell with value := some value}}

def setCell (world : Runtime) (reference : CellRef) (value : Value) : Except LexicalError Runtime := do
  let cell ← match world.cells[reference]? with
    | some cell => .ok cell | none => .error .invalidCell
  match cell.value, cell.kind with
  | none, _ => .error .temporalDeadZone
  | some _, .constant => .error .immutableBinding
  | some _, _ => pure {world with cells := world.cells.set reference {cell with value := some value}}

def setBindingValue (fuel : Nat) (world : Runtime) (environment : EnvironmentRef) (name : String) (value : Value) : Except LexicalError Runtime := do
  let reference ← resolveBinding fuel world environment name
  setCell world reference value

def flattenBindings : Nat → Runtime → EnvironmentRef → List (String × CellRef)
  | 0, _, _ => []
  | fuel + 1, world, environment =>
    match world.environments[environment]? with
    | none => []
    | some frame => frame.bindings ++ match frame.parent with
      | none => [] | some parent => flattenBindings fuel world parent

/-- Observation for ready DATA bindings only. Undefined placeholders retain
TDZ shadows; this lossy projection is never used by live variable lookup. -/
def projectEnvironment (fuel : Nat) (world : Runtime) (environment : EnvironmentRef) : List (String × Value) :=
  (flattenBindings fuel world environment).map (fun (name, reference) =>
    (name, ((world.cells[reference]?).bind Cell.value).getD .undefined))

def readyBindings (cells : List Cell) : List (String × CellRef) → List (String × Value)
  | [] => []
  | (name, reference) :: rest =>
    let outer := (readyBindings cells rest).filter (fun entry => entry.1 != name)
    match (cells[reference]?).bind Cell.value with
    | none => outer
    | some value => (name, value) :: outer

/-- Ghost observation for the old value-environment interpreter: missing/TDZ
nearest cells are omitted, and still hide outer cells of the same name. This
does not perform JavaScript GetBindingValue or impose readiness at call entry;
only evalOrdinary performs live variable evaluation. -/
def readyEnvironment (fuel : Nat) (world : Runtime) (environment : EnvironmentRef) : List (String × Value) :=
  readyBindings world.cells (flattenBindings fuel world environment)

def withData (world : Runtime) (data : LabelMatchState) : Runtime := {world with data}
def withAmbient (world : Runtime) (ambient : State) : Runtime :=
  withData world (cacheWithAmbient world.data ambient)

def arrowObject (program : ExportedArrow) (functionPrototype : Nat) : OrdinaryObject :=
  ⟨[(cacheAscii "length", .data (.number program.parameters.length) false false true),
    (cacheAscii "name", .data (.string (cacheAscii program.name)) false false true)], some functionPrototype, true⟩

def createArrow (program : ExportedArrow) (functionPrototype : Nat) (before : Runtime) : Except LexicalError (ArrowHandle × Runtime) := do
  let _ ← match before.data.base.regexp.ambient.objects[functionPrototype]? with
    | some object => .ok object | none => .error .invalidFunctionPrototype
  let handle := ArrowHandle.mk before.closures.length
  let reference := before.data.base.regexp.ambient.objects.length
  let closure : ArrowClosure := ⟨program, before.current, before.thisValue, reference⟩
  let after := withAmbient before {before.data.base.regexp.ambient with
    objects := before.data.base.regexp.ambient.objects ++ [arrowObject program functionPrototype]}
  pure (handle, {after with closures := before.closures ++ [closure]})

def functionObject (world : Runtime) (handle : ArrowHandle) : Except LexicalError Nat :=
  match world.closures[handle.index]? with
  | none => .error .invalidCallable | some closure => .ok closure.objectReference

def findClosureReference : List ArrowClosure → Nat → Option Nat
  | [], _ => none
  | closure :: rest, reference =>
    if closure.objectReference == reference then some 0 else
      (findClosureReference rest reference).map (· + 1)

/-- Ordinary object identity is the callable value in this extension. A
legacy intrinsic `Value.function` is never reinterpreted as an arrow handle. -/
def resolveArrowValue (world : Runtime) (value : Value) : Except LexicalError ArrowHandle :=
  match value with
  | .object reference => match findClosureReference world.closures reference with
    | some index => .ok ⟨index⟩ | none => .error .invalidCallable
  | _ => .error .invalidCallable

/-- Constructibility follows the callable kind, independently of mutable
ordinary properties such as a subsequently installed `prototype` field. -/
def constructArrow (world : Runtime) (handle : ArrowHandle) : Except LexicalError Value :=
  match world.closures[handle.index]? with
  | none => .error .invalidCallable | some _ => .error .notConstructible

def parameterCells (parameters : List ArrowParameter) (arguments : List Value) : List Cell :=
  parameters.zipIdx |>.map (fun (_, index) => ⟨.parameter, some (arguments[index]?.getD .undefined)⟩)

def parameterBindings (parameters : List ArrowParameter) (base : Nat) : List (String × CellRef) :=
  parameters.zipIdx |>.map (fun (parameter, index) => (parameter.name, base + index))

def enterCall (handle : ArrowHandle) (arguments : List Value) (before : Runtime) : Except LexicalError (Caller × Runtime) := do
  let closure ← match before.closures[handle.index]? with
    | some closure => .ok closure | none => .error .invalidCallable
  let caller : Caller := ⟨before.current, before.thisValue,
    before.data.base.regexp.ambient.environment, before.data.base.regexp.ambient.thisValue⟩
  let activation := before.environments.length
  let after : Runtime := {before with
    cells := before.cells ++ parameterCells closure.program.parameters arguments
    environments := before.environments ++ [⟨parameterBindings closure.program.parameters before.cells.length, some closure.environment⟩]
    current := activation, thisValue := closure.lexicalThis}
  pure (caller, withAmbient after {after.data.base.regexp.ambient with
    environment := readyEnvironment (after.environments.length + 1) after activation,
    thisValue := closure.lexicalThis})

def restoreCaller (caller : Caller) (after : Runtime) : Runtime :=
  withAmbient {after with current := caller.environment, thisValue := caller.thisValue}
    {after.data.base.regexp.ambient with environment := caller.legacyEnvironment, thisValue := caller.legacyThis}

/-- Initialized endpoint used by simulation and fixtures. Actual statement
execution first reserves the TDZ cell, evaluates its initializer, and finishes
that same cell; it does not skip the uninitialized stage. -/
def declareConstant (name : String) (value : Value) (before : Runtime) : Runtime :=
  let after : Runtime := {before with
    cells := before.cells ++ [⟨.constant, some value⟩]
    environments := before.environments ++ [⟨[(name, before.cells.length)], some before.current⟩]
    current := before.environments.length}
  withAmbient after {after.data.base.regexp.ambient with
    environment := (name, value) :: after.data.base.regexp.ambient.environment}

def reserveConstant (name : String) (before : Runtime) : CellRef × Runtime :=
  (before.cells.length, {before with
    cells := before.cells ++ [⟨.constant, none⟩]
    environments := before.environments ++ [⟨[(name, before.cells.length)], some before.current⟩]
    current := before.environments.length})

def finishConstant (name : String) (reference : CellRef) (value : Value) (before : Runtime) : Except LexicalError Runtime := do
  let after ← initializeCell before reference value
  pure (withAmbient after {after.data.base.regexp.ambient with
    environment := (name, value) :: after.data.base.regexp.ambient.environment})

/-- Exact read-only ordinary expression profile reached by the pinned body.
No user function is invoked through this interface. Every variable is resolved
from the CURRENT cell graph, rather than the legacy value projection. -/
def evalOrdinary : Nat → Runtime → Expr → Except Error Value
  | 0, _, _ => .error (.lexical .exhausted)
  | fuel + 1, world, expression => do
    match expression with
    | .variable name => (getBindingValue (world.environments.length + 1) world world.current name).mapError .lexical
    | .this => pure world.thisValue
    | .number value => pure (.number value)
    | .string value => pure (.string value)
    | .boolean value => pure (.boolean value)
    | .null => pure .null
    | .index base key =>
      let base ← evalOrdinary fuel world base
      let key ← evalOrdinary fuel world key
      (readProperty base key world.data.base.regexp.ambient).mapError (Error.body ∘ PatternCacheError.evaluation)
    | _ => .error (.lexical .unsupported)

/-- The closed intrinsic dispatch starts AFTER the live receiver read. Its
type cannot access or mutate lexical cells; arbitrary callbacks are rejected
by the existing identity tables, rather than receiving a stale snapshot. -/
def runResolvedLabelMatch (fuel : Nat) (context : LabelMatchContext) (receiver : Value)
    (method : String) (literal : LabelRegExpLiteral) (before : LabelMatchState) :
    Except LabelMatchError (Value × LabelMatchState) := do
  let before := {before with trace := before.trace ++ [.receiver receiver]}
  let _ ← match receiver with | .string _ => .ok () | _ => .error .methodDomain
  let (callee, after) ← getLabelProperty fuel context receiver context.stringPrototype (.string (cacheAscii method)) before
  let (argument, after) ← allocateLabelLiteral context literal after
  invokeLabelStringMatch fuel context callee receiver argument after

mutual
  /-- Expression effects can change the data heap, never the lexical store.
  This is the closed operation profile, not an arbitrary JS callback interface. -/
  def evalDataExpr : Nat → Nat → PatternCacheContext → PatternCacheExpr → Runtime → LabelMatchState → Except Error (Value × LabelMatchState)
    | 0, _, _, _, _, _ => .error (.body .exhausted)
    | fuel + 1, limit, context, expression, lexical, before => do
      match expression with
      | .ordinary expression =>
        let value ← evalOrdinary fuel (withData lexical before) expression
        pure (value, before)
      | .index base key =>
        let (base, after) ← evalDataExpr fuel limit context base lexical before
        let (key, after) ← evalDataExpr fuel limit context key lexical after
        let value ← (cacheReadProperty base key after.base.regexp.ambient).mapError (Error.body ∘ PatternCacheError.evaluation)
        pure (value, after)
      | .logicalNot value =>
        let (value, after) ← evalDataExpr fuel limit context value lexical before
        pure (.boolean (!truthy value), after)
      | .logicalAnd left right =>
        let (left, after) ← evalDataExpr fuel limit context left lexical before
        if truthy left then evalDataExpr fuel limit context right lexical after else pure (left, after)
      | .strictEqual left right =>
        let (left, after) ← evalDataExpr fuel limit context left lexical before
        let (right, after) ← evalDataExpr fuel limit context right lexical after
        pure (.boolean (decide (left = right)), after)
      | .strictNotEqual left right =>
        let (left, after) ← evalDataExpr fuel limit context left lexical before
        let (right, after) ← evalDataExpr fuel limit context right lexical after
        pure (.boolean (decide (left ≠ right)), after)
      | .conditional condition yes no =>
        let (condition, after) ← evalDataExpr fuel limit context condition lexical before
        evalDataExpr fuel limit context (if truthy condition then yes else no) lexical after
      | .template head substitutions =>
        let (tail, after) ← evalDataTemplate fuel limit substitutions lexical before
        pure (.string (head ++ tail), after)
      | .construct callee argument =>
        let saved ← evalOrdinary fuel (withData lexical before) callee
        let (argument, after) ← evalDataExpr fuel limit context argument lexical before
        let (value, constructed) ← (invokeRegExpConstructor context.label.iterators.constructors saved argument after.base.regexp).mapError (Error.body ∘ PatternCacheError.constructor)
        pure (value, {after with base := {after.base with regexp := constructed}})
      | .arrayLiteral elements =>
        let reference := before.base.regexp.ambient.heap.length
        let after ← evalDataElements fuel limit context reference elements lexical (cacheEmptyArray before)
        pure (.array reference, after)
      | .emptyObject =>
        let (value, ambient) ← (createLiteralObject before.base.regexp.ambient).mapError (Error.body ∘ PatternCacheError.evaluation)
        pure (value, cacheWithAmbient before ambient)
      | .labelMatch receiver method literal =>
        let receiver ← evalOrdinary fuel (withData lexical before) receiver
        (runResolvedLabelMatch fuel context.label receiver method literal before).mapError (Error.body ∘ PatternCacheError.label)
  def evalDataTemplate : Nat → Nat → List (Expr × JSString) → Runtime → LabelMatchState → Except Error (JSString × LabelMatchState)
    | 0, _, _, _, _ => .error (.body .exhausted)
    | _ + 1, _, [], _, before => .ok ([], before)
    | fuel + 1, limit, (operand, literal) :: rest, lexical, before => do
      let value ← evalOrdinary fuel (withData lexical before) operand
      let text ← (cachePrimitiveToString value).mapError .body
      let (tail, after) ← evalDataTemplate fuel limit rest lexical before
      pure (text ++ literal ++ tail, after)
  def evalDataElements : Nat → Nat → PatternCacheContext → Nat → List PatternCacheExpr → Runtime → LabelMatchState → Except Error LabelMatchState
    | 0, _, _, _, _, _, _ => .error (.body .exhausted)
    | _ + 1, _, _, _, [], _, before => .ok before
    | fuel + 1, limit, context, reference, head :: rest, lexical, before => do
      let (value, after) ← evalDataExpr fuel limit context head lexical before
      let after ← (cacheAppendElement reference value after).mapError .body
      evalDataElements fuel limit context reference rest lexical after
end

def evalExpr (fuel limit : Nat) (context : PatternCacheContext) (expression : PatternCacheExpr) (before : Runtime) : Except Error (Value × Runtime) :=
  (evalDataExpr fuel limit context expression before before.data).map
    (fun (value, after) => (value, withData before after))

def assign (fuel limit : Nat) (context : PatternCacheContext) (target value : PatternCacheExpr) (before : Runtime) : Except Error Runtime := do
  let (base, key, after) ← match target with
    | .index base key => do
      let (base, after) ← evalExpr fuel limit context base before
      let (key, after) ← evalExpr fuel limit context key after
      pure (base, key, after)
    | _ => .error (.body (.evaluation .unsupported))
  let (value, after) ← evalExpr fuel limit context value after
  let objects ← match base, key with
    | .object reference, .string key =>
      (setProperty propertyFuel after.data.base.regexp.ambient.objects reference key value).mapError
        (Error.body ∘ PatternCacheError.evaluation ∘ EvalError.objectError)
    | _, _ => .error (.body (.evaluation .unsupported))
  pure (withAmbient after {after.data.base.regexp.ambient with objects})

def restoreScope (environment : EnvironmentRef) (legacy : List (String × Value)) : Completion → Completion
  | .normal after => .normal (withAmbient {after with current := environment} {after.data.base.regexp.ambient with environment := legacy})
  | .returned value after => .returned value (withAmbient {after with current := environment} {after.data.base.regexp.ambient with environment := legacy})

def execute : Nat → Nat → PatternCacheContext → List PatternCacheStmt → Runtime → Except Error Completion
  | 0, _, _, _, _ => .error (.body .exhausted)
  | _ + 1, _, _, [], before => .ok (.normal before)
  | fuel + 1, limit, context, head :: tail, before => do
    match head with
    | .declare name initializer =>
      let (reference, reserved) := reserveConstant name before
      let (value, after) ← evalExpr fuel limit context initializer reserved
      let after ← (finishConstant name reference value after).mapError .lexical
      execute fuel limit context tail after
    | .assign target value =>
      let after ← assign fuel limit context target value before
      execute fuel limit context tail after
    | .ret value =>
      let (value, after) ← evalExpr fuel limit context value before
      pure (.returned value after)
    | .branch condition yes no =>
      let (condition, after) ← evalExpr fuel limit context condition before
      let completion ← execute fuel limit context (if truthy condition then yes else no) after
      match restoreScope after.current after.data.base.regexp.ambient.environment completion with
      | .normal after => execute fuel limit context tail after
      | .returned value after => pure (.returned value after)

def run (fuel limit : Nat) (context : PatternCacheContext) (program : List PatternCacheStmt) (before : Runtime) : Except Error (Value × Runtime) := do
  let completion ← execute fuel limit context program before
  match restoreScope before.current before.data.base.regexp.ambient.environment completion with
  | .normal after => pure (.undefined, after)
  | .returned value after => pure (value, after)

def invoke (fuel limit : Nat) (context : PatternCacheContext) (handle : ArrowHandle) (arguments : List Value) (before : Runtime) : Outcome :=
  match enterCall handle arguments before with
  | .error error => .outsideModel (.lexical error)
  | .ok (caller, entered) =>
    match before.closures[handle.index]? with
    | none => .outsideModel (.lexical .invalidCallable)
    | some closure => match run fuel limit context closure.program.body entered with
      | .error error => .outsideModel error
      | .ok (value, after) => .returned value (restoreCaller caller after)

def invokeValue (fuel limit : Nat) (context : PatternCacheContext) (callable : Value) (arguments : List Value) (before : Runtime) : Outcome :=
  match resolveArrowValue before callable with
  | .error error => .outsideModel (.lexical error)
  | .ok handle => invoke fuel limit context handle arguments before

def invokeBinding (fuel limit : Nat) (context : PatternCacheContext) (environment : EnvironmentRef) (name : String) (arguments : List Value) (before : Runtime) : Outcome :=
  match getBindingValue (before.environments.length + 1) before environment name with
  | .error error => .outsideModel (.lexical error)
  | .ok callable => invokeValue fuel limit context callable arguments before

/-- Source initialization and declaration share cells and the object heap.
Only the admitted actual empty-object initializer is supported here. -/
def initializeModule (initializer : PatternCacheInit) (program : ExportedArrow) (functionPrototype : Nat) (before : Runtime) : Except Error (ArrowHandle × Runtime) := do
  match initializer.initializer with
  | .emptyObject => pure ()
  | _ => .error (.lexical .unsupported)
  let (cacheCell, reserved) := reserveConstant initializer.name before
  let (value, ambient) ← (createLiteralObject reserved.data.base.regexp.ambient).mapError (Error.body ∘ PatternCacheError.evaluation)
  let cached ← (finishConstant initializer.name cacheCell value (withAmbient reserved ambient)).mapError .lexical
  let (exportCell, reserved) := reserveConstant program.name cached
  let (handle, after) ← (createArrow program functionPrototype reserved).mapError .lexical
  let reference ← (functionObject after handle).mapError .lexical
  let after ← (finishConstant program.name exportCell (.object reference) after).mapError .lexical
  pure (handle, after)

end HonoLean.Upstream.LexicalArrow
