import HonoLean.Upstream.LexicalArrow.Simulation

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.LexicalArrow.Core
open SourceSubset ECMA2025 GetPatternBody
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

theorem cacheWithAmbient_self (before : LabelMatchState) : cacheWithAmbient before before.base.regexp.ambient = before := by rfl

theorem cacheAppendElement_environment (reference : Nat) (value : Value) (before after : LabelMatchState)
    (returned : cacheAppendElement reference value before = .ok after) :
    after.base.regexp.ambient.environment = before.base.regexp.ambient.environment := by
  cases found : before.base.regexp.ambient.heap[reference]? <;>
    simp [cacheAppendElement, appendLiteralElements, found] at returned
  subst after
  rfl

theorem createLiteralObject_environment (before after : State) (value : Value)
    (returned : createLiteralObject before = .ok (value, after)) : after.environment = before.environment := by
  cases found : before.objects[ordinaryObjectPrototype]? <;> simp [createLiteralObject, found] at returned
  obtain ⟨rfl, rfl⟩ := returned
  rfl

theorem resolved_label_receiver (fuel limit : Nat) (context : LabelMatchContext)
    (receiver : Expr) (method : String) (literal : LabelRegExpLiteral) (before : LabelMatchState) (value : Value)
    (evaluated : evalExpression fuel limit receiver before.base.regexp.ambient = .ok (value, before.base.regexp.ambient)) :
    runLabelMatch fuel limit context ⟨"", receiver, method, literal⟩ before =
      runResolvedLabelMatch fuel context value method literal before := by
  simp [runLabelMatch, evaluated, runResolvedLabelMatch, cacheAscii]
  rfl

private theorem next_reads (lexical : Runtime) (before after : LabelMatchState) (names : List String)
    (same : after.base.regexp.ambient.environment = before.base.regexp.ambient.environment)
    (agreement : ReadsAgree (withData lexical before) names) : ReadsAgree (withData lexical after) names := by
  simpa only [withData_withData] using ReadsAgree_transport (withData lexical before) after names same agreement

section
variable
  (constructorEnvironment : ∀ (context : RegExpConstructContext) (callee argument : Value)
    (before : RegExpCallState) (value : Value) (after : RegExpCallState),
    invokeRegExpConstructor context callee argument before = .ok (value, after) →
      after.ambient.environment = before.ambient.environment)
  (labelEnvironment : ∀ (fuel : Nat) (context : LabelMatchContext) (receiver : Value)
    (method : String) (literal : LabelRegExpLiteral) (before : LabelMatchState)
    (value : Value) (after : LabelMatchState),
    runResolvedLabelMatch fuel context receiver method literal before = .ok (value, after) →
      after.base.regexp.ambient.environment = before.base.regexp.ambient.environment)

include constructorEnvironment labelEnvironment

/-- Successful closed expression evaluation is simulated one AST operation at
a time. The fixed lexical store is re-read at every ordinary variable leaf;
closed host operations can change only the data heap. -/
theorem closed_expression_refines (fuel : Nat) :
    (∀ (depth limit : Nat) (context : PatternCacheContext) (expression : PatternCacheExpr)
      (lexical : Runtime) (before : LabelMatchState) (value : Value) (after : LabelMatchState),
      expressionProfile depth expression = true →
      ReadsAgree (withData lexical before) (expressionReads depth expression) →
      evalPatternCacheExpr fuel limit context expression before = .ok (value, after) →
      evalDataExpr fuel limit context expression lexical before = .ok (value, after) ∧
        after.base.regexp.ambient.environment = before.base.regexp.ambient.environment) ∧
    (∀ (limit : Nat) (substitutions : List (Expr × JSString))
      (lexical : Runtime) (before : LabelMatchState) (value : JSString) (after : LabelMatchState),
      substitutions.all (fun entry => ordinaryProfile entry.1) = true →
      ReadsAgree (withData lexical before) (substitutions.flatMap (fun entry => ordinaryReads entry.1)) →
      evalPatternCacheTemplate fuel limit substitutions before = .ok (value, after) →
      evalDataTemplate fuel limit substitutions lexical before = .ok (value, after) ∧
        after.base.regexp.ambient.environment = before.base.regexp.ambient.environment) ∧
    (∀ (depth limit : Nat) (context : PatternCacheContext) (reference : Nat) (elements : List PatternCacheExpr)
      (lexical : Runtime) (before after : LabelMatchState),
      elements.all (expressionProfile depth) = true →
      ReadsAgree (withData lexical before) (elements.flatMap (expressionReads depth)) →
      evalPatternCacheElements fuel limit context reference elements before = .ok after →
      evalDataElements fuel limit context reference elements lexical before = .ok after ∧
        after.base.regexp.ambient.environment = before.base.regexp.ambient.environment) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intros <;>
      simp_all [evalPatternCacheExpr, evalPatternCacheTemplate, evalPatternCacheElements]
  | succ fuel ih =>
    obtain ⟨expressionIH, templateIH, elementsIH⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro depth limit context expression lexical before value after profile agreement returned
      cases depth with
      | zero => simp [expressionProfile] at profile
      | succ depth =>
        cases expression with
        | ordinary expression =>
          cases evaluated : evalExpression fuel limit expression before.base.regexp.ambient with
          | error error => simp [evalPatternCacheExpr, evaluated] at returned
          | ok result =>
            obtain ⟨observed, ambient⟩ := result
            obtain ⟨same, live⟩ := ordinary_refines fuel limit (withData lexical before) expression observed ambient
              profile agreement evaluated
            change ambient = before.base.regexp.ambient at same
            subst ambient
            simp [evalPatternCacheExpr, evaluated, cacheWithAmbient_self] at returned
            obtain ⟨rfl, rfl⟩ := returned
            exact ⟨by simp [evalDataExpr, live], rfl⟩
        | index left right =>
          have profiles : expressionProfile depth left = true ∧ expressionProfile depth right = true := by simpa [expressionProfile] using profile
          have agreements : ReadsAgree (withData lexical before) (expressionReads depth left) ∧ ReadsAgree (withData lexical before) (expressionReads depth right) :=
            (ReadsAgree.append _ _ _).mp agreement
          cases leftResult : evalPatternCacheExpr fuel limit context left before with
          | error error => simp [evalPatternCacheExpr, leftResult] at returned
          | ok result =>
            obtain ⟨leftValue, leftState⟩ := result
            obtain ⟨liveLeft, leftEnv⟩ := expressionIH depth limit context left lexical before leftValue leftState profiles.1 agreements.1 leftResult
            cases rightResult : evalPatternCacheExpr fuel limit context right leftState with
            | error error => simp [evalPatternCacheExpr, leftResult, rightResult] at returned
            | ok result =>
              obtain ⟨rightValue, rightState⟩ := result
              obtain ⟨liveRight, rightEnv⟩ := expressionIH depth limit context right lexical leftState rightValue rightState profiles.2
                (next_reads lexical before leftState _ leftEnv agreements.2) rightResult
              cases read : cacheReadProperty leftValue rightValue rightState.base.regexp.ambient with
              | error error => simp [evalPatternCacheExpr, leftResult, rightResult, read, -readProperty] at returned
              | ok observed =>
                simp [evalPatternCacheExpr, leftResult, rightResult, read, -readProperty] at returned
                obtain ⟨rfl, rfl⟩ := returned
                exact ⟨by simp [evalDataExpr, liveLeft, liveRight, read, -readProperty], rightEnv.trans leftEnv⟩
        | logicalNot expression =>
          cases evaluated : evalPatternCacheExpr fuel limit context expression before with
          | error error => simp [evalPatternCacheExpr, evaluated] at returned
          | ok result =>
            obtain ⟨observed, state⟩ := result
            obtain ⟨live, same⟩ := expressionIH depth limit context expression lexical before observed state profile agreement evaluated
            simp [evalPatternCacheExpr, evaluated] at returned
            obtain ⟨rfl, rfl⟩ := returned
            exact ⟨by simp [evalDataExpr, live], same⟩
        | logicalAnd left right =>
          have profiles : expressionProfile depth left = true ∧ expressionProfile depth right = true := by simpa [expressionProfile] using profile
          have agreements : ReadsAgree (withData lexical before) (expressionReads depth left) ∧ ReadsAgree (withData lexical before) (expressionReads depth right) :=
            (ReadsAgree.append _ _ _).mp agreement
          cases leftResult : evalPatternCacheExpr fuel limit context left before with
          | error error => simp [evalPatternCacheExpr, leftResult] at returned
          | ok result =>
            obtain ⟨leftValue, leftState⟩ := result
            obtain ⟨liveLeft, leftEnv⟩ := expressionIH depth limit context left lexical before leftValue leftState profiles.1 agreements.1 leftResult
            by_cases truth : truthy leftValue
            · have rightResult : evalPatternCacheExpr fuel limit context right leftState = .ok (value, after) := by simpa [evalPatternCacheExpr, leftResult, truth, -truthy] using returned
              obtain ⟨liveRight, rightEnv⟩ := expressionIH depth limit context right lexical leftState value after profiles.2
                (next_reads lexical before leftState _ leftEnv agreements.2) rightResult
              exact ⟨by simp [evalDataExpr, liveLeft, truth, liveRight, -truthy], rightEnv.trans leftEnv⟩
            · simp [evalPatternCacheExpr, leftResult, truth, -truthy] at returned
              obtain ⟨rfl, rfl⟩ := returned
              exact ⟨by simp [evalDataExpr, liveLeft, truth, -truthy], leftEnv⟩
        | strictEqual left right | strictNotEqual left right =>
          all_goals
            have profiles : expressionProfile depth left = true ∧ expressionProfile depth right = true := by simpa [expressionProfile] using profile
            have agreements : ReadsAgree (withData lexical before) (expressionReads depth left) ∧ ReadsAgree (withData lexical before) (expressionReads depth right) :=
              (ReadsAgree.append _ _ _).mp agreement
            cases leftResult : evalPatternCacheExpr fuel limit context left before with
            | error error => simp [evalPatternCacheExpr, leftResult] at returned
            | ok result =>
              obtain ⟨leftValue, leftState⟩ := result
              obtain ⟨liveLeft, leftEnv⟩ := expressionIH depth limit context left lexical before leftValue leftState profiles.1 agreements.1 leftResult
              cases rightResult : evalPatternCacheExpr fuel limit context right leftState with
              | error error => simp [evalPatternCacheExpr, leftResult, rightResult] at returned
              | ok result =>
                obtain ⟨rightValue, rightState⟩ := result
                obtain ⟨liveRight, rightEnv⟩ := expressionIH depth limit context right lexical leftState rightValue rightState profiles.2
                  (next_reads lexical before leftState _ leftEnv agreements.2) rightResult
                simp [evalPatternCacheExpr, leftResult, rightResult] at returned
                obtain ⟨rfl, rfl⟩ := returned
                exact ⟨by simp [evalDataExpr, liveLeft, liveRight], rightEnv.trans leftEnv⟩
        | conditional condition yes no =>
          have profiles : (expressionProfile depth condition = true ∧ expressionProfile depth yes = true) ∧ expressionProfile depth no = true := by simpa [expressionProfile] using profile
          have agreements : (ReadsAgree (withData lexical before) (expressionReads depth condition) ∧ ReadsAgree (withData lexical before) (expressionReads depth yes)) ∧ ReadsAgree (withData lexical before) (expressionReads depth no) := by
            simpa only [expressionReads, ReadsAgree.append] using agreement
          cases test : evalPatternCacheExpr fuel limit context condition before with
          | error error => simp [evalPatternCacheExpr, test] at returned
          | ok result =>
            obtain ⟨testValue, testState⟩ := result
            obtain ⟨liveTest, testEnv⟩ := expressionIH depth limit context condition lexical before testValue testState profiles.1.1 agreements.1.1 test
            by_cases truth : truthy testValue
            · have branch : evalPatternCacheExpr fuel limit context yes testState = .ok (value, after) := by simpa [evalPatternCacheExpr, test, truth, -truthy] using returned
              obtain ⟨liveBranch, branchEnv⟩ := expressionIH depth limit context yes lexical testState value after profiles.1.2
                (next_reads lexical before testState _ testEnv agreements.1.2) branch
              exact ⟨by simp [evalDataExpr, liveTest, truth, liveBranch, -truthy], branchEnv.trans testEnv⟩
            · have branch : evalPatternCacheExpr fuel limit context no testState = .ok (value, after) := by simpa [evalPatternCacheExpr, test, truth, -truthy] using returned
              obtain ⟨liveBranch, branchEnv⟩ := expressionIH depth limit context no lexical testState value after profiles.2
                (next_reads lexical before testState _ testEnv agreements.2) branch
              exact ⟨by simp [evalDataExpr, liveTest, truth, liveBranch, -truthy], branchEnv.trans testEnv⟩
        | template head substitutions =>
          cases evaluated : evalPatternCacheTemplate fuel limit substitutions before with
          | error error => simp [evalPatternCacheExpr, evaluated] at returned
          | ok result =>
            obtain ⟨observed, state⟩ := result
            obtain ⟨live, same⟩ := templateIH limit substitutions lexical before observed state profile agreement evaluated
            simp [evalPatternCacheExpr, evaluated] at returned
            obtain ⟨rfl, rfl⟩ := returned
            exact ⟨by simp [evalDataExpr, live], same⟩
        | construct callee argument =>
          have profiles : ordinaryProfile callee = true ∧ expressionProfile depth argument = true := by simpa [expressionProfile] using profile
          have agreements : ReadsAgree (withData lexical before) (ordinaryReads callee) ∧ ReadsAgree (withData lexical before) (expressionReads depth argument) :=
            (ReadsAgree.append _ _ _).mp agreement
          cases evaluated : evalExpression fuel limit callee before.base.regexp.ambient with
          | error error => simp [evalPatternCacheExpr, evaluated] at returned
          | ok result =>
            obtain ⟨saved, ambient⟩ := result
            obtain ⟨same, liveCallee⟩ := ordinary_refines fuel limit (withData lexical before) callee saved ambient profiles.1 agreements.1 evaluated
            change ambient = before.base.regexp.ambient at same
            subst ambient
            cases argumentResult : evalPatternCacheExpr fuel limit context argument before with
            | error error => simp [evalPatternCacheExpr, evaluated, cacheWithAmbient_self, argumentResult] at returned
            | ok result =>
              obtain ⟨argumentValue, argumentState⟩ := result
              obtain ⟨liveArgument, argumentEnv⟩ := expressionIH depth limit context argument lexical before argumentValue argumentState profiles.2 agreements.2 argumentResult
              cases constructed : invokeRegExpConstructor context.label.iterators.constructors saved argumentValue argumentState.base.regexp with
              | error error => simp [evalPatternCacheExpr, evaluated, cacheWithAmbient_self, argumentResult, constructed] at returned
              | ok result =>
                obtain ⟨resultValue, resultState⟩ := result
                have sameEnv := constructorEnvironment context.label.iterators.constructors saved argumentValue argumentState.base.regexp resultValue resultState constructed
                simp [evalPatternCacheExpr, evaluated, cacheWithAmbient_self, argumentResult, constructed] at returned
                obtain ⟨rfl, rfl⟩ := returned
                exact ⟨by simp [evalDataExpr, liveCallee, liveArgument, constructed], sameEnv.trans argumentEnv⟩
        | arrayLiteral values =>
          cases evaluated : evalPatternCacheElements fuel limit context before.base.regexp.ambient.heap.length values (cacheEmptyArray before) with
          | error error => simp [evalPatternCacheExpr, evaluated] at returned
          | ok state =>
            have afterAgreement : ReadsAgree (withData lexical (cacheEmptyArray before)) (values.flatMap (expressionReads depth)) :=
              next_reads lexical before (cacheEmptyArray before) _ rfl agreement
            obtain ⟨live, same⟩ := elementsIH depth limit context before.base.regexp.ambient.heap.length values lexical (cacheEmptyArray before) state profile afterAgreement evaluated
            simp [evalPatternCacheExpr, evaluated] at returned
            obtain ⟨rfl, rfl⟩ := returned
            exact ⟨by simp [evalDataExpr, live], same⟩
        | emptyObject =>
          cases evaluated : createLiteralObject before.base.regexp.ambient with
          | error error => simp [evalPatternCacheExpr, evaluated] at returned
          | ok result =>
            obtain ⟨observed, ambient⟩ := result
            have same := createLiteralObject_environment before.base.regexp.ambient ambient observed evaluated
            simp [evalPatternCacheExpr, evaluated] at returned
            obtain ⟨rfl, rfl⟩ := returned
            exact ⟨by simp [evalDataExpr, evaluated], same⟩
        | labelMatch receiver method literal =>
          cases evaluated : evalExpression fuel limit receiver before.base.regexp.ambient with
          | error error => simp [evalPatternCacheExpr, runLabelMatch, evaluated] at returned
          | ok result =>
            obtain ⟨observed, ambient⟩ := result
            obtain ⟨same, live⟩ := ordinary_refines fuel limit (withData lexical before) receiver observed ambient profile agreement evaluated
            change ambient = before.base.regexp.ambient at same
            subst ambient
            have bridge := resolved_label_receiver fuel limit context.label receiver method literal before observed evaluated
            cases matched : runResolvedLabelMatch fuel context.label observed method literal before with
            | error error => simp [evalPatternCacheExpr, bridge, matched] at returned
            | ok result =>
              obtain ⟨observed, state⟩ := result
              simp [evalPatternCacheExpr, bridge, matched] at returned
              obtain ⟨rfl, rfl⟩ := returned
              exact ⟨by simp [evalDataExpr, live, matched], labelEnvironment fuel context.label _ method literal before _ _ matched⟩
    · intro limit substitutions lexical before value after profile agreement returned
      cases substitutions with
      | nil =>
        simp [evalPatternCacheTemplate] at returned
        obtain ⟨rfl, rfl⟩ := returned
        exact ⟨rfl, rfl⟩
      | cons entry rest =>
        obtain ⟨operand, literal⟩ := entry
        have profiles : ordinaryProfile operand = true ∧ rest.all (fun entry => ordinaryProfile entry.1) = true := by simpa using profile
        have agreements : ReadsAgree (withData lexical before) (ordinaryReads operand) ∧ ReadsAgree (withData lexical before) (rest.flatMap (fun entry => ordinaryReads entry.1)) :=
          (ReadsAgree.append _ _ _).mp agreement
        cases evaluated : evalExpression fuel limit operand before.base.regexp.ambient with
        | error error => simp [evalPatternCacheTemplate, evaluated] at returned
        | ok result =>
          obtain ⟨observed, ambient⟩ := result
          obtain ⟨same, live⟩ := ordinary_refines fuel limit (withData lexical before) operand observed ambient profiles.1 agreements.1 evaluated
          change ambient = before.base.regexp.ambient at same
          subst ambient
          cases converted : cachePrimitiveToString observed with
          | error error => simp [evalPatternCacheTemplate, evaluated, converted] at returned
          | ok text =>
            cases tailResult : evalPatternCacheTemplate fuel limit rest before with
            | error error => simp [evalPatternCacheTemplate, evaluated, converted, cacheWithAmbient_self, tailResult] at returned
            | ok result =>
              obtain ⟨tail, state⟩ := result
              obtain ⟨liveTail, sameEnv⟩ := templateIH limit rest lexical before tail state profiles.2 agreements.2 tailResult
              simp [evalPatternCacheTemplate, evaluated, converted, cacheWithAmbient_self, tailResult] at returned
              obtain ⟨rfl, rfl⟩ := returned
              exact ⟨by simp [evalDataTemplate, live, converted, liveTail], sameEnv⟩
    · intro depth limit context reference values lexical before after profile agreement returned
      cases values with
      | nil =>
        simp [evalPatternCacheElements] at returned
        subst after
        exact ⟨rfl, rfl⟩
      | cons head tail =>
        have profiles : expressionProfile depth head = true ∧ tail.all (expressionProfile depth) = true := by simpa using profile
        have agreements : ReadsAgree (withData lexical before) (expressionReads depth head) ∧ ReadsAgree (withData lexical before) (tail.flatMap (expressionReads depth)) :=
          (ReadsAgree.append _ _ _).mp agreement
        cases evaluated : evalPatternCacheExpr fuel limit context head before with
        | error error => simp [evalPatternCacheElements, evaluated] at returned
        | ok result =>
          obtain ⟨observed, state⟩ := result
          obtain ⟨live, expressionEnv⟩ := expressionIH depth limit context head lexical before observed state profiles.1 agreements.1 evaluated
          cases appended : cacheAppendElement reference observed state with
          | error error => simp [evalPatternCacheElements, evaluated, appended] at returned
          | ok appendedState =>
            have appendEnv := cacheAppendElement_environment reference observed state appendedState appended
            have tailResult : evalPatternCacheElements fuel limit context reference tail appendedState = .ok after := by
              simpa [evalPatternCacheElements, evaluated, appended] using returned
            obtain ⟨liveTail, tailEnv⟩ := elementsIH depth limit context reference tail lexical appendedState after profiles.2
              (next_reads lexical before appendedState _ (appendEnv.trans expressionEnv) agreements.2) tailResult
            exact ⟨by simp [evalDataElements, live, appended, liveTail], tailEnv.trans (appendEnv.trans expressionEnv)⟩

theorem expression_refines (fuel profileFuel limit : Nat) (context : PatternCacheContext)
    (expression : PatternCacheExpr) (before : Runtime) (value : Value) (data : LabelMatchState)
    (profile : expressionProfile profileFuel expression = true)
    (agreement : ReadsAgree before (expressionReads profileFuel expression))
    (old : evalPatternCacheExpr fuel limit context expression before.data = .ok (value, data)) :
    evalExpr fuel limit context expression before = .ok (value, withData before data) ∧
      data.base.regexp.ambient.environment = before.data.base.regexp.ambient.environment := by
  obtain ⟨live, same⟩ := (closed_expression_refines constructorEnvironment labelEnvironment fuel).1 profileFuel limit context expression before before.data value data profile
    (by simpa only [withData_self] using agreement) old
  exact ⟨by simp [evalExpr, live], same⟩

end

end HonoLean.Upstream.LexicalArrow.Core
