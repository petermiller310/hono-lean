import HonoLean.Upstream.LexicalArrow.ExpressionSimulation

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.GetPatternInvocation
open SourceSubset hiding pinnedSource Completion execute run
open ECMA2025 LexicalArrow
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

theorem flattened_lookup_resolves (fuel : Nat) (before : Runtime) (environment : Nat) (name : String) (reference : Nat)
    (found : (flattenBindings fuel before environment).lookup name = some reference) :
    resolveBinding fuel before environment name = .ok reference := by
  induction fuel generalizing environment with
  | zero => simp [flattenBindings] at found
  | succ fuel ih =>
    cases frameFound : before.environments[environment]? with
    | none => simp [flattenBindings, frameFound] at found
    | some frame =>
      cases binding : frame.bindings.lookup name with
      | some cell =>
        simp [flattenBindings, frameFound, List.lookup_append, binding] at found
        subst reference
        simp [resolveBinding, frameFound, binding]
      | none =>
        cases parent : frame.parent with
        | none => simp [flattenBindings, frameFound, binding, parent] at found
        | some outer =>
          have next : (flattenBindings fuel before outer).lookup name = some reference := by
            simpa [flattenBindings, frameFound, List.lookup_append, binding, parent] using found
          simp [resolveBinding, frameFound, binding, parent, ih outer next]

theorem flatten_environment_congr (fuel : Nat) (left right : Runtime) (environment : Nat)
    (same : left.environments = right.environments) :
    flattenBindings fuel left environment = flattenBindings fuel right environment := by
  induction fuel generalizing environment with
  | zero => rfl
  | succ fuel ih => simp [flattenBindings, same, ih]

theorem ready_environment_store_congr (fuel : Nat) (left right : Runtime) (environment : Nat)
    (environments : left.environments = right.environments) (cells : left.cells = right.cells) :
    readyEnvironment fuel left environment = readyEnvironment fuel right environment := by
  simp [readyEnvironment, cells, flatten_environment_congr fuel left right environment environments]

/-- A raw ghost projection supplies agreement only for initialized nearest
cells. Omitted TDZ entries remain shadowing barriers; unused cells need no read. -/
theorem ready_environment_agrees (before : Runtime)
    (mirror : before.data.base.regexp.ambient.environment =
      readyEnvironment (before.environments.length + 1) before before.current) : EnvironmentAgrees before := by
  intro name value found
  rw [mirror, readyEnvironment, readyBindings_lookup] at found
  cases binding : (flattenBindings (before.environments.length + 1) before before.current).lookup name with
  | none => simp [binding] at found
  | some reference =>
    cases cellFound : before.cells[reference]? with
    | none => simp [binding, cellFound] at found
    | some cell =>
      have resolved := flattened_lookup_resolves (before.environments.length + 1) before before.current name reference binding
      have initialized : cell.value = some value := by simpa [binding, cellFound] using found
      simp [getBindingValue, resolved, cellFound, initialized]

/-- Each expression is checked at its own fixed structural bound; statement
fuel controls only nested statement lists. This avoids confusing VM fuel with
the independently checked source profile. -/
def callProgramProfile : Nat → List PatternCacheStmt → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | fuel + 1, statement :: rest =>
    let admitted := match statement with
      | .declare name initializer => expressionProfile 128 initializer && !(expressionReads 128 initializer).contains name
      | .assign (.index base key) value => expressionProfile 128 base && expressionProfile 128 key && expressionProfile 128 value
      | .assign _ _ => false
      | .ret value => expressionProfile 128 value
      | .branch condition yes no => expressionProfile 128 condition && callProgramProfile fuel yes && callProgramProfile fuel no
    admitted && callProgramProfile fuel rest

theorem actual_call_program_profile : callProgramProfile 128 GetPatternBody.program = true := by decide

def completionWorld : Completion → Runtime
  | .normal after | .returned _ after => after

def completionData : PatternCacheCompletion → LabelMatchState
  | .normal after | .returned _ after => after

def SameCompletion : PatternCacheCompletion → Completion → Prop
  | .normal data, .normal after => after.data = data
  | .returned value data, .returned returned after => returned = value ∧ after.data = data
  | _, _ => False

/-- Simulation also retains actual lexical storage and the caller-independent
function/this components; ordinary heap effects are carried by the data relation. -/
structure ExecutionFrame (before after : Runtime) : Prop where
  store : StoreExtension before after
  closures : after.closures = before.closures
  thisValue : after.thisValue = before.thisValue

theorem ExecutionFrame.refl (before : Runtime) : ExecutionFrame before before :=
  ⟨StoreExtension.refl before, rfl, rfl⟩

theorem ExecutionFrame.trans (before middle after : Runtime)
    (left : ExecutionFrame before middle) (right : ExecutionFrame middle after) : ExecutionFrame before after :=
  ⟨StoreExtension.trans before middle after left.store right.store,
   right.closures.trans left.closures, right.thisValue.trans left.thisValue⟩

theorem with_data_agrees (before : Runtime) (data : LabelMatchState)
    (same : data.base.regexp.ambient.environment = before.data.base.regexp.ambient.environment)
    (agreement : EnvironmentAgrees before) : EnvironmentAgrees (withData before data) := by
  intro name value found
  change data.base.regexp.ambient.environment.lookup name = some value at found
  rw [same] at found
  rw [getBindingValue_store_congr _ (withData before data) before rfl rfl]
  exact agreement name value found

theorem with_data_frame (before : Runtime) (data : LabelMatchState) : ExecutionFrame before (withData before data) :=
  ⟨⟨fun _ _ found => found, fun _ _ found => found, Nat.le_refl _⟩, rfl, rfl⟩

theorem agrees_on_reads (before : Runtime) (names : List String) (agreement : EnvironmentAgrees before) :
    ReadsAgree before names := fun name _ value found => agreement name value found

theorem reserved_agrees_on_reads (before : Runtime) (name : String) (reads : List String)
    (absent : name ∉ reads) (agreement : EnvironmentAgrees before) :
    ReadsAgree (reserveConstant name before).2 reads := by
  intro query member value found
  have different : query ≠ name := by intro same; subst query; exact absent member
  exact reserved_lookup_other before name query value different (agreement query value found)

def resumeWorld (before after : Runtime) : Runtime :=
  withAmbient {after with current := before.current}
    {after.data.base.regexp.ambient with environment := before.data.base.regexp.ambient.environment}

theorem resume_frame (before after : Runtime) (frame : ExecutionFrame before after) :
    ExecutionFrame before (resumeWorld before after) :=
  ⟨⟨frame.store.cells, frame.store.environments, frame.store.length⟩, frame.closures, frame.thisValue⟩

theorem resume_agrees (before after : Runtime) (extension : StoreExtension before after)
    (agreement : EnvironmentAgrees before) : EnvironmentAgrees (resumeWorld before after) := by
  intro name value found
  have read := agreement name value found
  have preserved := getBindingValue_extension (before.environments.length + 1)
    (after.environments.length - before.environments.length) before after extension before.current name value read
  have fuel : before.environments.length + 1 + (after.environments.length - before.environments.length) =
      after.environments.length + 1 := by have bound := extension.length; omega
  rw [fuel] at preserved
  rw [getBindingValue_store_congr _ (resumeWorld before after) after rfl rfl]
  exact preserved

theorem declare_frame (before : Runtime) (name : String) (value : Value) :
    ExecutionFrame before (declareConstant name value before) := ⟨declare_extends name value before, rfl, rfl⟩

theorem assignment_refines (fuel limit : Nat) (context : PatternCacheContext)
    (base key value : PatternCacheExpr) (before : Runtime) (data : LabelMatchState)
    (baseProfile : expressionProfile 128 base = true) (keyProfile : expressionProfile 128 key = true)
    (valueProfile : expressionProfile 128 value = true) (agreement : EnvironmentAgrees before)
    (old : executePatternCacheAssignment fuel limit context (.index base key) value before.data = .ok data) :
    assign fuel limit context (.index base key) value before = .ok (withData before data) ∧
    data.base.regexp.ambient.environment = before.data.base.regexp.ambient.environment := by
  cases baseEval : evalPatternCacheExpr fuel limit context base before.data with
  | error error => simp [executePatternCacheAssignment, baseEval] at old
  | ok result =>
    obtain ⟨baseValue, baseData⟩ := result
    obtain ⟨liveBase, sameBase⟩ := expression_refines fuel 128 limit context base before baseValue baseData
      baseProfile (agrees_on_reads before _ agreement) baseEval
    have baseAgrees := with_data_agrees before baseData sameBase agreement
    cases keyEval : evalPatternCacheExpr fuel limit context key baseData with
    | error error => simp [executePatternCacheAssignment, baseEval, keyEval] at old
    | ok result =>
      obtain ⟨keyValue, keyData⟩ := result
      obtain ⟨liveKey, sameKey⟩ := expression_refines fuel 128 limit context key (withData before baseData) keyValue keyData
        keyProfile (agrees_on_reads _ _ baseAgrees) keyEval
      have keyAgrees := with_data_agrees (withData before baseData) keyData sameKey baseAgrees
      cases valueEval : evalPatternCacheExpr fuel limit context value keyData with
      | error error => simp [executePatternCacheAssignment, baseEval, keyEval, valueEval] at old
      | ok result =>
        obtain ⟨storedValue, valueData⟩ := result
        obtain ⟨liveValue, sameValue⟩ := expression_refines fuel 128 limit context value (withData before keyData) storedValue valueData
          valueProfile (agrees_on_reads _ _ keyAgrees) valueEval
        cases baseValue <;> cases keyValue <;>
          try { simp [executePatternCacheAssignment, baseEval, keyEval, valueEval] at old }
        case object.string reference property =>
          cases written : setProperty propertyFuel valueData.base.regexp.ambient.objects reference property storedValue with
          | error error => simp [executePatternCacheAssignment, baseEval, keyEval, valueEval, written] at old
          | ok objects =>
            simp [executePatternCacheAssignment, baseEval, keyEval, valueEval, written] at old
            subst data
            constructor
            · simp only [assign, liveBase, bind, Except.bind]
              rw [liveKey]
              simp only [pure, Except.pure, withData_withData]
              rw [liveValue]
              simp [written, withData, withAmbient]
            · exact sameValue.trans (sameKey.trans sameBase)

theorem execute_refines (fuel profileFuel limit : Nat) (context : PatternCacheContext)
    (statements : List PatternCacheStmt) (before : Runtime) (oldCompletion : PatternCacheCompletion)
    (profile : callProgramProfile profileFuel statements = true) (agreement : EnvironmentAgrees before)
    (old : executePatternCache fuel limit context statements before.data = .ok oldCompletion) :
    ∃ completion, execute fuel limit context statements before = .ok completion ∧
      SameCompletion oldCompletion completion ∧ ExecutionFrame before (completionWorld completion) ∧
      EnvironmentAgrees (completionWorld completion) := by
  induction fuel generalizing profileFuel statements before oldCompletion with
  | zero => simp [executePatternCache] at old
  | succ fuel ih =>
    cases profileFuel with
    | zero => simp [callProgramProfile] at profile
    | succ profileFuel =>
      cases statements with
      | nil =>
        simp [executePatternCache] at old
        subst oldCompletion
        exact ⟨.normal before, rfl, rfl, ExecutionFrame.refl before, agreement⟩
      | cons statement rest =>
        cases statement with
        | declare name initializer =>
          have admitted : expressionProfile 128 initializer = true ∧ name ∉ expressionReads 128 initializer ∧
              callProgramProfile profileFuel rest = true := by
            simpa [callProgramProfile, Bool.and_assoc] using profile
          cases evaluated : evalPatternCacheExpr fuel limit context initializer before.data with
          | error error => simp [executePatternCache, evaluated] at old
          | ok result =>
            obtain ⟨value, data⟩ := result
            have ready := reserved_agrees_on_reads before name _ admitted.2.1 agreement
            obtain ⟨live, same⟩ := expression_refines fuel 128 limit context initializer (reserveConstant name before).2 value data
              admitted.1 ready evaluated
            let next := declareConstant name value (withData before data)
            have nextAgrees : EnvironmentAgrees next := declared_agrees (withData before data) name value
              (with_data_agrees before data same agreement)
            have oldNext : executePatternCache fuel limit context rest next.data = .ok oldCompletion := by
              simpa [executePatternCache, evaluated, next, declareConstant, withAmbient, withData] using old
            obtain ⟨completion, executed, related, frame, finalAgrees⟩ :=
              ih profileFuel rest next oldCompletion admitted.2.2 nextAgrees oldNext
            refine ⟨completion, ?_, related, ?_, finalAgrees⟩
            · have reference : (reserveConstant name before).1 = before.cells.length := rfl
              simpa only [execute, live, reference, finish_reserved, next,
                bind, Except.bind, pure, Except.pure, Except.mapError, Except.map] using executed
            · exact ExecutionFrame.trans before next _
                (ExecutionFrame.trans before (withData before data) next (with_data_frame before data)
                  (declare_frame (withData before data) name value)) frame
        | assign target value =>
          cases target <;> try { simp [callProgramProfile] at profile }
          case index base key =>
            have admitted : expressionProfile 128 base = true ∧ expressionProfile 128 key = true ∧
                expressionProfile 128 value = true ∧ callProgramProfile profileFuel rest = true := by
              simpa [callProgramProfile, Bool.and_assoc] using profile
            cases evaluated : executePatternCacheAssignment fuel limit context (.index base key) value before.data with
            | error error => simp [executePatternCache, evaluated] at old
            | ok data =>
              obtain ⟨live, same⟩ := assignment_refines fuel limit context base key value before data
                admitted.1 admitted.2.1 admitted.2.2.1 agreement evaluated
              have nextAgrees := with_data_agrees before data same agreement
              have oldNext : executePatternCache fuel limit context rest data = .ok oldCompletion := by
                simpa [executePatternCache, evaluated] using old
              obtain ⟨completion, executed, related, frame, finalAgrees⟩ :=
                ih profileFuel rest (withData before data) oldCompletion admitted.2.2.2 nextAgrees oldNext
              refine ⟨completion, ?_, related,
                ExecutionFrame.trans before (withData before data) _ (with_data_frame before data) frame, finalAgrees⟩
              simpa [execute, live] using executed
        | ret expression =>
          have admitted : expressionProfile 128 expression = true := by
            have both : expressionProfile 128 expression = true ∧ callProgramProfile profileFuel rest = true := by
              simpa [callProgramProfile] using profile
            exact both.1
          cases evaluated : evalPatternCacheExpr fuel limit context expression before.data with
          | error error => simp [executePatternCache, evaluated] at old
          | ok result =>
            obtain ⟨value, data⟩ := result
            obtain ⟨live, same⟩ := expression_refines fuel 128 limit context expression before value data
              admitted (agrees_on_reads before _ agreement) evaluated
            simp [executePatternCache, evaluated] at old
            subst oldCompletion
            exact ⟨.returned value (withData before data), by simp [execute, live], ⟨rfl, rfl⟩,
              with_data_frame before data, with_data_agrees before data same agreement⟩
        | branch condition yes no =>
          have admitted : expressionProfile 128 condition = true ∧ callProgramProfile profileFuel yes = true ∧
              callProgramProfile profileFuel no = true ∧ callProgramProfile profileFuel rest = true := by
            simpa [callProgramProfile, Bool.and_assoc] using profile
          cases evaluated : evalPatternCacheExpr fuel limit context condition before.data with
          | error error => simp [executePatternCache, evaluated] at old
          | ok result =>
            obtain ⟨value, data⟩ := result
            obtain ⟨live, same⟩ := expression_refines fuel 128 limit context condition before value data
              admitted.1 (agrees_on_reads before _ agreement) evaluated
            let next := withData before data
            have nextAgrees : EnvironmentAgrees next := with_data_agrees before data same agreement
            have chosen : callProgramProfile profileFuel (if truthy value then yes else no) = true := by
              split
              · exact admitted.2.1
              · exact admitted.2.2.1
            cases branchEval : executePatternCache fuel limit context (if truthy value then yes else no) data with
            | error error =>
              simp only [executePatternCache, evaluated, bind, Except.bind, branchEval] at old
              cases old
            | ok branchResult =>
              obtain ⟨branchCompletion, branchLive, branchRelated, branchFrame, _⟩ :=
                ih profileFuel _ next branchResult chosen nextAgrees branchEval
              dsimp only [next] at branchLive
              cases branchResult with
              | normal oldData =>
                cases branchCompletion with
                | returned returned after => simp only [SameCompletion] at branchRelated
                | normal after =>
                  simp only [SameCompletion] at branchRelated
                  have equal : after.data = oldData := branchRelated
                  let resumed := resumeWorld next after
                  have resumedAgrees : EnvironmentAgrees resumed := resume_agrees next after branchFrame.store nextAgrees
                  have oldNext : executePatternCache fuel limit context rest resumed.data = .ok oldCompletion := by
                    simpa only [executePatternCache, evaluated, bind, Except.bind, pure, Except.pure, branchEval, cacheRestoreEnvironment,
                      resumed, resumeWorld, next, equal, withAmbient, withData] using old
                  obtain ⟨completion, tailLive, related, tailFrame, finalAgrees⟩ :=
                    ih profileFuel rest resumed oldCompletion admitted.2.2.2 resumedAgrees oldNext
                  refine ⟨completion, ?_, related, ?_, finalAgrees⟩
                  · simpa only [execute, live, bind, Except.bind, pure, Except.pure, branchLive, restoreScope, resumed, resumeWorld] using tailLive
                  · exact ExecutionFrame.trans before next _ (with_data_frame before data)
                      (ExecutionFrame.trans next resumed _ (resume_frame next after branchFrame) tailFrame)
              | returned oldValue oldData =>
                cases branchCompletion with
                | normal after => simp only [SameCompletion] at branchRelated
                | returned returned after =>
                  simp only [SameCompletion] at branchRelated
                  obtain ⟨sameValue, equal⟩ := branchRelated
                  subst returned
                  simp only [executePatternCache, evaluated, bind, Except.bind, pure, Except.pure, branchEval, cacheRestoreEnvironment,
                    Except.ok.injEq] at old
                  subst oldCompletion
                  refine ⟨.returned oldValue (resumeWorld next after), ?_, ⟨rfl, ?_⟩, ?_, ?_⟩
                  · simp only [execute, live, bind, Except.bind, pure, Except.pure, branchLive, restoreScope, resumeWorld, next]
                  · simp [resumeWorld, next, equal, withAmbient, withData]
                  · exact ExecutionFrame.trans before next _ (with_data_frame before data) (resume_frame next after branchFrame)
                  · exact resume_agrees next after branchFrame.store nextAgrees

/-- The completed old-body fact is an internal simulation input. Public source
call theorems discharge it from the independent cache/realm contracts. The live
runner derives parameter/local lookup and retains actual lexical storage. -/
theorem run_refines (fuel profileFuel limit : Nat) (context : PatternCacheContext)
    (statements : List PatternCacheStmt) (before : Runtime) (value : Value) (data : LabelMatchState)
    (profile : callProgramProfile profileFuel statements = true) (agreement : EnvironmentAgrees before)
    (old : runPatternCache fuel limit context statements before.data = .ok (value, data)) :
    ∃ after, run fuel limit context statements before = .ok (value, after) ∧ after.data = data ∧
      ExecutionFrame before after ∧ EnvironmentAgrees after ∧ after.current = before.current := by
  cases evaluated : executePatternCache fuel limit context statements before.data with
  | error error => simp [runPatternCache, evaluated] at old
  | ok oldCompletion =>
    obtain ⟨completion, live, related, frame, _⟩ :=
      execute_refines fuel profileFuel limit context statements before oldCompletion profile agreement evaluated
    cases oldCompletion with
    | normal oldData =>
      cases completion with
      | returned returned after => simp only [SameCompletion] at related
      | normal after =>
        simp only [SameCompletion] at related
        simp [runPatternCache, evaluated, cacheRestoreEnvironment] at old
        obtain ⟨rfl, rfl⟩ := old
        refine ⟨resumeWorld before after, ?_, ?_, resume_frame before after frame,
          resume_agrees before after frame.store agreement, rfl⟩
        · simp [run, live, restoreScope, resumeWorld]
        · simp [resumeWorld, related, withAmbient, withData]
    | returned oldValue oldData =>
      cases completion with
      | normal after => simp only [SameCompletion] at related
      | returned returned after =>
        simp only [SameCompletion] at related
        obtain ⟨rfl, equal⟩ := related
        simp [runPatternCache, evaluated, cacheRestoreEnvironment] at old
        obtain ⟨rfl, rfl⟩ := old
        refine ⟨resumeWorld before after, ?_, ?_, resume_frame before after frame,
          resume_agrees before after frame.store agreement, rfl⟩
        · simp [run, live, restoreScope, resumeWorld]
        · simp [resumeWorld, equal, withAmbient, withData]

end HonoLean.Upstream.GetPatternInvocation
