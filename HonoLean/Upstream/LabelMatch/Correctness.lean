import HonoLean.Upstream.LabelMatch.Contract

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace HonoLean.Upstream.LabelMatch
open SourceSubset ECMA2025

theorem execute_source (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (input : JSString)
    (inputs : Inputs before context input) :
    sourceMatch (extra + 128) context before = some (.ok (resultState before context input)) := by
  have receiver : evalExpression (extra + 128) defaultSplitLimit program.receiver before.base.regexp.ambient =
      .ok (.string input, before.base.regexp.ambient) := by
    simp [program, evalExpression, lookupVariable, inputs.labelBinding]
    rfl
  have method := label_get_string_method (extra + 127) {before with trace := before.trace ++ [LabelEvent.receiver (.string input)]} context
    (labelRealm_trace before context _ inputs.toLabelRealm) input
  have budget : extra + 127 + 1 = extra + 128 := by omega
  rw [budget] at method
  have allocated := label_allocate_actual
    {before with trace := (before.trace ++ [LabelEvent.receiver (.string input)]) ++
      [LabelEvent.get (.string input) (.string labelMatchKey) context.stringPrototype (.function context.builtins.base)]} context (labelRealm_trace before context _ inputs.toLabelRealm)
  rw [sourceMatch, parses_source]
  dsimp only [Option.map, executeLabelMatch, runLabelMatch]
  rw [receiver]
  dsimp only [Except.mapError, bind, Except.bind]
  apply congrArg some
  simp only [program]
  have key : "match".toList.map (fun c => UInt16.ofNat c.toNat) = labelMatchKey := by decide
  rw [key]
  rw [method]
  dsimp only [bind, Except.bind]
  rw [allocated]
  dsimp only [bind, Except.bind]
  simp only [labelFreshState_before_trace, List.append_assoc, List.cons_append, List.nil_append]
  rw [label_string_match_fresh extra before context inputs.toLabelRealm]
  cases outcome : LabelRegExp.execute LabelRegExp.labelCode input <;>
    simp [resultState, sourceEvents, labelEngineState, labelFreshState, outcome, pure, Except.pure, List.append_assoc]

private def optionalStringValue : Option JSString → Value
  | none => .undefined | some string => .string string

theorem match_values (input name : JSString) (body : Option JSString) (valid : LabelRegExp.Label input name body) :
    labelMatchValues input (LabelRegExp.labelMatch name body) = captures input name body := by
  have bounds := LabelRegExp.label_capture_bounds input name body valid
  have values := congrArg (List.map optionalStringValue) (LabelRegExp.label_capture_values input name body valid)
  have bridge : ∀ span, optionalStringValue (LabelRegExp.extractCapture input span) = labelCaptureValue input span := by
    intro span
    cases span <;> rfl
  simp only [List.map_map, Function.comp_def, bridge] at values
  simp only [labelMatchValues, bounds.1, bounds.2.1, List.drop_zero, Nat.sub_zero, List.take_length]
  rw [values]
  cases body <;> rfl

theorem result_contract (before : LabelMatchState) (context : LabelMatchContext) (input : JSString) :
    Contract before (resultState before context input) context input := by
  constructor
  case environment => exact ⟨labelEngineValue before input, rfl⟩
  case success =>
    intro name body valid
    have hit := LabelRegExp.execute_label_hit input name body valid
    have values := match_values input name body valid
    have bounds := LabelRegExp.label_capture_bounds input name body valid
    cases body <;>
      simp [resultState, labelEngineValue, labelEngineState, hit, values, captures, observeLabelResult,
        labelFreshState, bounds.1]
  case failure =>
    intro absent
    have miss := (LabelRegExp.execute_label_miss_iff input).mpr absent
    simp [resultState, labelEngineValue, labelEngineState, miss, labelFreshState]
  case oldObjects =>
    intro reference old
    cases result : LabelRegExp.execute LabelRegExp.labelCode input <;>
      simpa [resultState, labelEngineState, labelFreshState, result] using
        (List.getElem?_append_left (l₂ := [initializedRegExpObject context.regexpPrototype]) old)
  case oldLabelBrands =>
    intro reference different
    cases result : LabelRegExp.execute LabelRegExp.labelCode input <;>
      simp [resultState, labelEngineState, labelFreshState, result, List.lookup, beq_eq_false_iff_ne.mpr different]
  case oldLabelResults =>
    intro reference different
    cases result : LabelRegExp.execute LabelRegExp.labelCode input <;>
      simp [resultState, labelEngineState, labelFreshState, result, List.lookup, beq_eq_false_iff_ne.mpr different]
  case oldArrays =>
    intro reference old
    cases result : LabelRegExp.execute LabelRegExp.labelCode input <;>
      simp [resultState, labelEngineState, labelFreshState, result, List.getElem?_append_left old]
  all_goals cases result : LabelRegExp.execute LabelRegExp.labelCode input <;>
    simp [resultState, labelEngineState, labelFreshState, result]

/-- Actual source literal/call dispatch and operational captures, proved against
an independent label language. No match, flags output, branded record or future
successful callback is supplied. OLD realm identity interpretation remains open. -/
theorem source_match_satisfies (extra : Nat) (before : LabelMatchState) (context : LabelMatchContext) (input : JSString)
    (inputs : Inputs before context input) :
    sourceMatch (extra + 128) context before = some (.ok (resultState before context input)) ∧
    Contract before (resultState before context input) context input :=
  ⟨execute_source extra before context input inputs, result_contract before context input⟩

end HonoLean.Upstream.LabelMatch
