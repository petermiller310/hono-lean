import HonoLean.Upstream.LexicalArrow.Runtime

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.LexicalArrow
open SourceSubset ECMA2025 GetPatternBody
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

@[simp] theorem withData_self (world : Runtime) : withData world world.data = world := by cases world; rfl

@[simp] theorem withData_withData (world : Runtime) (first second : LabelMatchState) :
    withData (withData world first) second = withData world second := by rfl

theorem resolveBinding_environment_congr (fuel : Nat) (left right : Runtime)
    (same : left.environments = right.environments) (environment : EnvironmentRef) (name : String) :
    resolveBinding fuel left environment name = resolveBinding fuel right environment name := by
  induction fuel generalizing environment with
  | zero => rfl
  | succ fuel ih => simp [resolveBinding, same, ih]

theorem getBindingValue_store_congr (fuel : Nat) (left right : Runtime)
    (environments : left.environments = right.environments) (cells : left.cells = right.cells)
    (environment : EnvironmentRef) (name : String) :
    getBindingValue fuel left environment name = getBindingValue fuel right environment name := by
  simp [getBindingValue, resolveBinding_environment_congr fuel left right environments environment name, cells]

def ordinaryReads : Expr → List String
  | .variable name => [name]
  | .index base key => ordinaryReads base ++ ordinaryReads key
  | _ => []

def ordinaryProfile : Expr → Bool
  | .variable name => name != "Object" && name != "Set"
  | .number _ | .string _ | .boolean _ | .null => true
  | .index base key => ordinaryProfile base && ordinaryProfile key
  | _ => false

mutual
  def expressionReads : Nat → PatternCacheExpr → List String
    | 0, _ => []
    | fuel + 1, expression => match expression with
      | .ordinary expression => ordinaryReads expression
      | .index left right | .logicalAnd left right | .strictEqual left right | .strictNotEqual left right => expressionReads fuel left ++ expressionReads fuel right
      | .logicalNot value => expressionReads fuel value
      | .conditional condition yes no => expressionReads fuel condition ++ expressionReads fuel yes ++ expressionReads fuel no
      | .template _ substitutions => substitutions.flatMap (fun entry => ordinaryReads entry.1)
      | .construct callee argument => ordinaryReads callee ++ expressionReads fuel argument
      | .arrayLiteral elements => elements.flatMap (expressionReads fuel)
      | .emptyObject => []
      | .labelMatch receiver _ _ => ordinaryReads receiver
  def expressionProfile : Nat → PatternCacheExpr → Bool
    | 0, _ => false
    | fuel + 1, expression => match expression with
      | .ordinary expression => ordinaryProfile expression
      | .index left right | .logicalAnd left right | .strictEqual left right | .strictNotEqual left right => expressionProfile fuel left && expressionProfile fuel right
      | .logicalNot value => expressionProfile fuel value
      | .conditional condition yes no => expressionProfile fuel condition && expressionProfile fuel yes && expressionProfile fuel no
      | .template _ substitutions => substitutions.all (fun entry => ordinaryProfile entry.1)
      | .construct callee argument => ordinaryProfile callee && expressionProfile fuel argument
      | .arrayLiteral elements => elements.all (expressionProfile fuel)
      | .emptyObject => true
      | .labelMatch receiver _ _ => ordinaryProfile receiver
end

def programProfile : Nat → List PatternCacheStmt → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | fuel + 1, head :: tail =>
    let admitted := match head with
      | .declare name initializer => expressionProfile fuel initializer && !(expressionReads fuel initializer).contains name
      | .assign (.index base key) value => expressionProfile fuel base && expressionProfile fuel key && expressionProfile fuel value
      | .assign _ _ => false
      | .ret value => expressionProfile fuel value
      | .branch condition yes no => expressionProfile fuel condition && programProfile fuel yes && programProfile fuel no
    admitted && programProfile fuel tail

/-- Checked against the retained actual AST: no ordinary callbacks/constructors
or binding writes, and no declaration initializer reads its reserved own name.
Whole-block binding instantiation/native adequacy remains open; this local
certificate does not claim it. Arbitrary callbacks are rejected. -/
theorem actual_program_profile : programProfile 128 GetPatternBody.program = true := by decide

def SameLexicalStore (before after : Runtime) : Prop :=
  after.cells = before.cells ∧ after.environments = before.environments ∧
  after.closures = before.closures ∧ after.current = before.current ∧ after.thisValue = before.thisValue

/-- This preservation law follows from the closed expression VM's result
type: effects return only LabelMatchState; cells are never copied back from
an old value environment. -/
theorem expression_preserves_lexical_store (fuel limit : Nat) (context : PatternCacheContext)
    (expression : PatternCacheExpr) (before after : Runtime) (value : Value)
    (returned : evalExpr fuel limit context expression before = .ok (value, after)) :
    SameLexicalStore before after := by
  unfold evalExpr at returned
  cases evaluated : evalDataExpr fuel limit context expression before before.data with
  | error error => simp [evaluated] at returned
  | ok result =>
    obtain ⟨result, data⟩ := result
    simp [evaluated] at returned
    obtain ⟨rfl, rfl⟩ := returned
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lookup_filter_excluding (entries : List (String × Value)) (name excluded : String) :
    (entries.filter (fun entry => entry.1 != excluded)).lookup name =
      if name == excluded then none else entries.lookup name := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    by_cases same : name = excluded
    · subst name
      by_cases keyEq : key = excluded
      · subst key
        simpa only [List.filter_cons, bne_self_eq_false, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] using ih
      · have reverse : (excluded == key) = false := by simp [Ne.symm keyEq]
        have forward : (key != excluded) = true := by simp [keyEq]
        simpa only [List.filter_cons, forward, ↓reduceIte, List.lookup, reverse] using ih
    · by_cases keyEq : key = excluded
      · subst key
        have neq : (name == excluded) = false := by simp [same]
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.lookup, neq]
        simpa only [neq, Bool.false_eq_true, ↓reduceIte] using ih
      · have forward : (key != excluded) = true := by simp [keyEq]
        have neq : (name == excluded) = false := by simp [same]
        simp only [List.filter_cons, forward, ↓reduceIte, List.lookup, neq]
        by_cases sameKey : name == key
        · simp only [sameKey, Bool.false_eq_true, ↓reduceIte]
        · simp only [sameKey, Bool.false_eq_true, ↓reduceIte]
          simpa only [neq, Bool.false_eq_true, ↓reduceIte] using ih

theorem readyBindings_lookup (cells : List Cell) (entries : List (String × CellRef)) (name : String) :
    (readyBindings cells entries).lookup name =
      (entries.lookup name).bind (fun reference => (cells[reference]?).bind Cell.value) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, reference⟩ := entry
    cases found : (cells[reference]?).bind Cell.value <;>
      by_cases same : name = key <;>
      simp only [readyBindings, found, List.lookup, lookup_filter_excluding] <;>
      simp [same, found, ih] <;>
      (have unequal : (name == key) = false := beq_eq_false_iff_ne.mpr same
       simp only [unequal])

def ReadsAgree (world : Runtime) (names : List String) : Prop :=
  ∀ name ∈ names, ∀ value,
    world.data.base.regexp.ambient.environment.lookup name = some value →
    getBindingValue (world.environments.length + 1) world world.current name = .ok value

/-- Successful evaluation of an admitted ordinary expression is read-only.
This is a local simulation lemma, not an assumed successful body invocation. -/
theorem ordinary_refines (fuel limit : Nat) (world : Runtime) (expression : Expr)
    (value : Value) (ambient : State)
    (profile : ordinaryProfile expression = true)
    (agreement : ReadsAgree world (ordinaryReads expression))
    (evaluated : evalExpression fuel limit expression world.data.base.regexp.ambient = .ok (value, ambient)) :
    ambient = world.data.base.regexp.ambient ∧ evalOrdinary fuel world expression = .ok value := by
  induction fuel generalizing world expression value ambient with
  | zero => simp [evalExpression] at evaluated
  | succ fuel ih =>
    cases expression <;> try { simp only [ordinaryProfile, Bool.false_eq_true] at profile }
    case «variable» name =>
      have excluded : name ≠ "Object" ∧ name ≠ "Set" := by simpa [ordinaryProfile] using profile
      cases binding : world.data.base.regexp.ambient.environment.lookup name with
      | none => simp [evalExpression, lookupVariable, binding, excluded.1, excluded.2] at evaluated
      | some observed =>
        have live := agreement name (by simp [ordinaryReads]) observed binding
        simp [evalExpression, lookupVariable, binding] at evaluated
        obtain ⟨rfl, rfl⟩ := evaluated
        exact ⟨rfl, by simp [evalOrdinary, live]⟩
    case number number =>
      simp [evalExpression] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact ⟨rfl, rfl⟩
    case string string =>
      simp [evalExpression] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact ⟨rfl, rfl⟩
    case boolean boolean =>
      simp [evalExpression] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact ⟨rfl, rfl⟩
    case null =>
      simp [evalExpression] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact ⟨rfl, rfl⟩
    case index base key =>
      have admitted : ordinaryProfile base = true ∧ ordinaryProfile key = true := by
        simpa [ordinaryProfile] using profile
      have leftAgreement : ReadsAgree world (ordinaryReads base) := by
        intro name member observed binding
        exact agreement name (List.mem_append_left _ member) observed binding
      have rightAgreement : ReadsAgree world (ordinaryReads key) := by
        intro name member observed binding
        exact agreement name (List.mem_append_right _ member) observed binding
      cases left : evalExpression fuel limit base world.data.base.regexp.ambient with
      | error error => simp [evalExpression, left] at evaluated
      | ok result =>
        obtain ⟨leftValue, leftAmbient⟩ := result
        obtain ⟨same, liveLeft⟩ := ih world base leftValue leftAmbient admitted.1 leftAgreement left
        subst leftAmbient
        cases right : evalExpression fuel limit key world.data.base.regexp.ambient with
        | error error => simp [evalExpression, left, right] at evaluated
        | ok result =>
          obtain ⟨rightValue, rightAmbient⟩ := result
          obtain ⟨same, liveRight⟩ := ih world key rightValue rightAmbient admitted.2 rightAgreement right
          subst rightAmbient
          cases read : readProperty leftValue rightValue world.data.base.regexp.ambient with
          | error error => simp [evalExpression, left, right, read, -readProperty] at evaluated
          | ok observed =>
            simp [evalExpression, left, right, read, -readProperty] at evaluated
            obtain ⟨rfl, rfl⟩ := evaluated
            exact ⟨rfl, by simp [evalOrdinary, liveLeft, liveRight, read, -readProperty]⟩

theorem resolve_nearest (fuel : Nat) (world : Runtime) (environment : EnvironmentRef)
    (name : String) (frame : Environment) (reference : CellRef)
    (found : world.environments[environment]? = some frame)
    (binding : frame.bindings.lookup name = some reference) :
    resolveBinding (fuel + 1) world environment name = .ok reference := by
  simp [resolveBinding, found, binding]

theorem read_nearest_tdz (fuel : Nat) (world : Runtime) (environment : EnvironmentRef)
    (name : String) (frame : Environment) (reference : CellRef) (kind : BindingKind)
    (found : world.environments[environment]? = some frame)
    (binding : frame.bindings.lookup name = some reference)
    (uninitialized : world.cells[reference]? = some ⟨kind, none⟩) :
    getBindingValue (fuel + 1) world environment name = .error .temporalDeadZone := by
  simp [getBindingValue, resolve_nearest fuel world environment name frame reference found binding, uninitialized]

theorem read_nearest_ready (fuel : Nat) (world : Runtime) (environment : EnvironmentRef)
    (name : String) (frame : Environment) (reference : CellRef) (kind : BindingKind) (value : Value)
    (found : world.environments[environment]? = some frame)
    (binding : frame.bindings.lookup name = some reference)
    (initialized : world.cells[reference]? = some ⟨kind, some value⟩) :
    getBindingValue (fuel + 1) world environment name = .ok value := by
  simp [getBindingValue, resolve_nearest fuel world environment name frame reference found binding, initialized]

theorem constant_set_rejected (world : Runtime) (reference : CellRef) (old value : Value)
    (found : world.cells[reference]? = some ⟨.constant, some old⟩) :
    setCell world reference value = .error .immutableBinding := by
  simp [setCell, found]

theorem tdz_set_rejected (world : Runtime) (reference : CellRef) (kind : BindingKind) (value : Value)
    (found : world.cells[reference]? = some ⟨kind, none⟩) :
    setCell world reference value = .error .temporalDeadZone := by
  simp [setCell, found]

theorem mutable_set (world : Runtime) (reference : CellRef) (old value : Value)
    (found : world.cells[reference]? = some ⟨.mutable, some old⟩) :
    setCell world reference value = .ok {world with cells := world.cells.set reference ⟨.mutable, some value⟩} := by
  simp [setCell, found]

theorem arrow_no_own_prototype (program : ExportedArrow) (functionPrototype : Nat) :
    (arrowObject program functionPrototype).own.lookup (cacheAscii "prototype") = none := by
  rfl

theorem arrow_name (program : ExportedArrow) (functionPrototype : Nat) :
    (arrowObject program functionPrototype).own.lookup (cacheAscii "name") =
      some (.data (.string (cacheAscii program.name)) false false true) := by
  rfl

theorem arrow_length (program : ExportedArrow) (functionPrototype : Nat) :
    (arrowObject program functionPrototype).own.lookup (cacheAscii "length") =
      some (.data (.number program.parameters.length) false false true) := by
  rfl

theorem arrow_function_prototype (program : ExportedArrow) (functionPrototype : Nat) :
    (arrowObject program functionPrototype).prototype = some functionPrototype := by rfl

theorem arrow_never_constructible (world : Runtime) (handle : ArrowHandle) (closure : ArrowClosure)
    (found : world.closures[handle.index]? = some closure) :
    constructArrow world handle = .error .notConstructible := by
  simp [constructArrow, found]

theorem actual_arrow_length (functionPrototype : Nat) :
    (arrowObject GetPatternBody.declaration functionPrototype).own.lookup (cacheAscii "length") =
      some (.data (.number 2) false false true) := by rfl

theorem actual_parameters (arguments : List Value) :
    parameterCells GetPatternBody.declaration.parameters arguments =
      [⟨.parameter, some (arguments[0]?.getD .undefined)⟩,
       ⟨.parameter, some (arguments[1]?.getD .undefined)⟩] := by rfl

theorem actual_parameters_missing_next (label : Value) :
    parameterCells GetPatternBody.declaration.parameters [label] =
      [⟨.parameter, some label⟩, ⟨.parameter, some .undefined⟩] := by rfl

theorem actual_parameters_ignore_extra (label next : Value) (extra : List Value) :
    parameterCells GetPatternBody.declaration.parameters (label :: next :: extra) =
      [⟨.parameter, some label⟩, ⟨.parameter, some next⟩] := by rfl

theorem actual_parameter_bindings (base : Nat) :
    parameterBindings GetPatternBody.declaration.parameters base =
      [("label", base), ("next", base + 1)] := by simp [parameterBindings, GetPatternBody.declaration]

theorem restore_current (caller : Caller) (after : Runtime) :
    (restoreCaller caller after).current = caller.environment := by rfl

theorem restore_this (caller : Caller) (after : Runtime) :
    (restoreCaller caller after).thisValue = caller.thisValue := by rfl

theorem restore_cells (caller : Caller) (after : Runtime) :
    (restoreCaller caller after).cells = after.cells := by rfl

theorem restore_objects (caller : Caller) (after : Runtime) :
    (restoreCaller caller after).data.base.regexp.ambient.objects = after.data.base.regexp.ambient.objects := by rfl

theorem restore_arrays (caller : Caller) (after : Runtime) :
    (restoreCaller caller after).data.base.regexp.ambient.heap = after.data.base.regexp.ambient.heap := by rfl

theorem restore_legacy_environment (caller : Caller) (after : Runtime) :
    (restoreCaller caller after).data.base.regexp.ambient.environment = caller.legacyEnvironment := by rfl

theorem eval_variable (fuel : Nat) (world : Runtime) (name : String) (value : Value)
    (binding : getBindingValue (world.environments.length + 1) world world.current name = .ok value) :
    evalOrdinary (fuel + 1) world (.variable name) = .ok value := by
  simp [evalOrdinary, binding]

theorem eval_variable_ignores_projection (fuel : Nat) (world : Runtime) (name : String)
    (projection : List (String × Value)) :
    evalOrdinary (fuel + 1) (withAmbient world {world.data.base.regexp.ambient with environment := projection}) (.variable name) =
      evalOrdinary (fuel + 1) world (.variable name) := by
  simp only [evalOrdinary]
  change Except.mapError Error.lexical
    (getBindingValue (world.environments.length + 1)
      (withAmbient world {world.data.base.regexp.ambient with environment := projection}) world.current name) = _
  exact congrArg (Except.mapError Error.lexical)
    (getBindingValue_store_congr (world.environments.length + 1)
      (withAmbient world {world.data.base.regexp.ambient with environment := projection}) world rfl rfl world.current name)

/-- Ordinary source receiver evaluation and the live cell read meet at the
same saved value; the rest is the actual closed method/Get/literal/@@match VM. -/
theorem resolved_label_refines (fuel limit : Nat) (context : LabelMatchContext)
    (before : LabelMatchState) (name method : String) (literal : LabelRegExpLiteral) (value : Value)
    (binding : before.base.regexp.ambient.environment.lookup name = some value) :
    runLabelMatch (fuel + 1) limit context ⟨"", .variable name, method, literal⟩ before =
      runResolvedLabelMatch (fuel + 1) context value method literal before := by
  simp [runLabelMatch, evalExpression, lookupVariable, binding, runResolvedLabelMatch,
    cacheAscii]
  rfl

theorem live_label_refines (fuel limit : Nat) (context : PatternCacheContext)
    (before : Runtime) (name method : String) (literal : LabelRegExpLiteral) (value : Value)
    (live : getBindingValue (before.environments.length + 1) before before.current name = .ok value)
    (projection : before.data.base.regexp.ambient.environment.lookup name = some value) :
    evalExpr (fuel + 3) limit context (.labelMatch (.variable name) method literal) before =
      ((runLabelMatch (fuel + 2) limit context.label ⟨"", .variable name, method, literal⟩ before.data).mapError
        (Error.body ∘ PatternCacheError.label)).map (fun (value, after) => (value, withData before after)) := by
  rw [resolved_label_refines (fuel + 1) limit context.label before.data name method literal value projection]
  simp [evalExpr, evalDataExpr, evalOrdinary, live]

theorem wildcard_run (extra limit : Nat) (context : PatternCacheContext) (before : Runtime)
    (binding : getBindingValue (before.environments.length + 1) before before.current "label" = .ok GetPatternBody.star) :
    run (extra + 5) limit context GetPatternBody.program before = .ok (GetPatternBody.star, before) := by
  simp [run, execute, GetPatternBody.program, GetPatternBody.guardProgram,
    GetPatternBody.guardExpr, PatternCache.labelExpr, evalExpr, evalDataExpr, evalDataExpr, evalOrdinary, binding,
    GetPatternBody.star, truthy, restoreScope, withAmbient, withData, cacheWithAmbient]

/-- Current constructor identity is saved before argument execution. There
is no definition-time RegExp value in the closure record. -/
theorem construct_current_binding (fuel limit : Nat) (context : PatternCacheContext)
    (before : Runtime) (name : String) (argument : PatternCacheExpr) (value : Value)
    (binding : getBindingValue (before.environments.length + 1) before before.current name = .ok value) :
    evalExpr (fuel + 2) limit context (.construct (.variable name) argument) before = (do
      let (argument, after) ← evalDataExpr (fuel + 1) limit context argument before before.data
      let (result, constructed) ← (invokeRegExpConstructor context.label.iterators.constructors value argument after.base.regexp).mapError
        (Error.body ∘ PatternCacheError.constructor)
      pure (result, withData before {after with base := {after.base with regexp := constructed}})) := by
  unfold evalExpr
  rw [evalDataExpr, withData_self, eval_variable fuel before name value binding]
  cases argumentResult : evalDataExpr (fuel + 1) limit context argument before before.data with
  | error error => simp
  | ok result =>
    obtain ⟨argument, after⟩ := result
    cases constructed : invokeRegExpConstructor context.label.iterators.constructors value argument after.base.regexp <;>
      simp [constructed]

end HonoLean.Upstream.LexicalArrow
