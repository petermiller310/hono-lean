import HonoLean.Upstream.LabelMatch.Composition

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.LabelMatch.Checks
open SourceSubset ECMA2025

private theorem standard_realm (input : JSString) : LabelRealm (labelStandardState input) labelStandardContext := by
  refine ⟨rfl, rfl, (by change 1 ≤ 9; decide), (by change 2 ≤ 9; decide), (by change 3 ≤ 9; decide),
    (by change 5 ≤ 9; decide), (by change 6 ≤ 9; decide), (by change 7 ≤ 9; decide), (by change 9 ≤ 9; decide),
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_,
    (by change 1 ≤ 1; decide), (by change 2 ≤ 2; decide), (by change 3 ≤ 3; decide),
    (by change 5 ≤ 5; decide), (by change 6 ≤ 6; decide), (by change 7 ≤ 7; decide)⟩
  intro entry member
  simp only [labelStandardState, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  change 2 < 7
  decide

private theorem standard_inputs (input : JSString) : Inputs (labelStandardState input) labelStandardContext input :=
  ⟨standard_realm input, rfl⟩

/-- A genuinely inhabited universal source domain for arbitrary finite rawUTF16
labels. Initial realm/type projections are fixtures, not native bootstrap proofs. -/
theorem arbitrary_utf16_source_has_independent_contract (input : JSString) :
    sourceMatch 128 labelStandardContext (labelStandardState input) =
      some (.ok (resultState (labelStandardState input) labelStandardContext input)) ∧
    Contract (labelStandardState input) (resultState (labelStandardState input) labelStandardContext input) labelStandardContext input :=
  source_match_satisfies 0 _ _ input (standard_inputs input)

private def observation (text : JSString) :=
  (sourceMatch 128 labelStandardContext (labelStandardState text)).map (fun result => result.map (fun state =>
    (state.base.regexp.ambient.environment.lookup "match", state.base.regexp.ambient.heap[1]?,
      observeLabelResult state 1 .two, observeLabelResult state 1 .groups,
      state.base.regexp.ambient.objects[6]?, state.base.regexp.ambient.heap[0]?)))

theorem absent_capture_is_own_undefined_and_literal_ignores_RegExp_shadow :
    observation [58,105,100] = some (.ok (some (.array 1), some [.string [58,105,100], .string [105,100], .undefined],
      some (.data .undefined true true true), some (.data .undefined true true true),
      some ⟨[(lastIndexKey, .data (.number 17) false false false)], some 2, false⟩, some [.string labelPrior])) := by cbv

theorem greedy_body_keeps_internal_braces :
    (sourceMatch 128 labelStandardContext (labelStandardState [58,105,100,123,97,125,123,98,125])).map
      (fun result => result.map (fun state => state.base.regexp.ambient.heap[1]?)) =
      some (.ok (some [.string [58,105,100,123,97,125,123,98,125], .string [105,100], .string [97,125,123,98]])) := by cbv

theorem malformed_future_regex_body_is_still_a_valid_label_capture :
    (sourceMatch 128 labelStandardContext (labelStandardState [58,120,123,91,125])).map
      (fun result => result.map (fun state => state.base.regexp.ambient.heap[1]?)) =
      some (.ok (some [.string [58,120,123,91,125], .string [120], .string [91]])) := by cbv

theorem names_keep_line_terminators_nul_and_lone_surrogates :
    (sourceMatch 128 labelStandardContext (labelStandardState [58,0,10,13,8232,8233,55296])).map
      (fun result => result.map (fun state => state.base.regexp.ambient.heap[1]?)) =
      some (.ok (some [.string [58,0,10,13,8232,8233,55296], .string [0,10,13,8232,8233,55296], .undefined])) := by cbv

theorem empty_name_empty_body_and_body_line_terminators_miss :
    ([[58], [58,123,97,125], [58,120,123,125], [58,120,123,97,10,98,125], [58,120,123,97,8232,98,125]] : List JSString).all
      (fun input => match sourceMatch 128 labelStandardContext (labelStandardState input) with
        | some (.ok state) => state.base.regexp.ambient.environment.lookup "match" == some .null
        | _ => false) = true := by cbv

private def getterHandles (trace : List LabelEvent) : List Value :=
  trace.filterMap (fun event => match event with | .getter callee _ => some callee | _ => none)
private def calls (trace : List LabelEvent) : List Value :=
  trace.filterMap (fun event => match event with | .call callee _ => some callee | _ => none)

theorem selected_2025_protocol_reads_all_flags_and_reuses_old_exec_identity :
    (sourceMatch 128 labelStandardContext (labelStandardState [58,120])).map (fun result => result.map (fun state =>
      (getterHandles state.trace, calls state.trace))) =
      some (.ok ([.function 11, .function 12, .function 13, .function 14, .function 15, .function 16, .function 17, .function 18, .function 19],
        [.function 9, .function 10, .function 5])) := by cbv

theorem frontend_rejects_keyword_prefix_invalid_literal_and_flags_before_execution :
    (["constmatch = label.match(/^x$/)", "const$match = label.match(/^x$/)",
      "const match = label.match(/(/)", "const match = label.match(/^x$/i)", "const match = label.match(/a/)", "const match = label.match(//)"] |>.all
      (fun text => (parseLabelMatch text ["label"]).isNone)) = true := by cbv

theorem actual_producer_preserves_prior_arrays_objects_and_metadata :
    Contract (labelStandardState [58,120]) (resultState (labelStandardState [58,120]) labelStandardContext [58,120]) labelStandardContext [58,120] :=
  (arbitrary_utf16_source_has_independent_contract [58,120]).2


private def idName : JSString := [105,100]
private def pipelineBefore (lower upper : UInt16) (query : JSString) : LabelMatchState :=
  let old := labelStandardState (safeRangeLabel idName lower upper)
  {old with base := {old.base with
    regexp := {old.base.regexp with ambient := {old.base.regexp.ambient with
      environment := ("restPathString", .string query) :: ("RegExp", .function 6) :: old.base.regexp.ambient.environment}}
    symbols := [(.object 3, [(.iterator, .data (.function 7) true false true)])]}}

private theorem pipeline_inputs (lower upper : UInt16) (query : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) :
    ConstructorInputs (pipelineBefore lower upper query) labelStandardContext idName lower upper 6 ⟨2⟩
      ⟨standardLabelRegExpOwn 9 5, some 0, true⟩ := by
  refine ⟨⟨?_, rfl⟩, (by simp [LabelRegExp.Name, idName]), safeLower, safeUpper, ordered, rfl,
    (by change 1 ≤ 6; decide), (by change 2 ≤ 6; decide), (by change 3 ≤ 6; decide),
    (by change 5 ≤ 6; decide), (by change 6 ≤ 6; decide), (by change 6 ≤ 6; decide), rfl, rfl⟩
  · have realm := standard_realm (safeRangeLabel idName lower upper)
    cases realm
    constructor <;> assumption

private theorem pipeline_closed (lower upper : UInt16) (query : JSString) :
    IteratorPrototypeClosed (pipelineBefore lower upper query).base.regexp.ambient.objects := by
  intro reference object found parent edge
  rcases reference with _ | _ | _ | _ | _ | _ | _ | reference <;>
    simp [pipelineBefore, labelStandardState, labelStandardAmbient] at found <;>
    subst object <;> simp [objectPrototypeProjection] at edge <;> subst parent <;>
    change _ < 7 <;> decide

private theorem pipeline_realm (lower upper : UInt16) (query : JSString) :
    NodePatternBinding.Realm (pipelineBefore lower upper query).base labelStandardContext.iterators 7 8 .undefined := by
  refine ⟨pipeline_closed lower upper query, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, rfl,
    (by change 1 ≤ 7; decide), (by change 2 ≤ 7; decide), (by change 3 ≤ 7; decide),
    (by change 5 ≤ 7; decide), (by change 6 ≤ 7; decide), (by change 7 ≤ 7; decide),
    (by change 7 ≤ 7; decide), rfl, (by change 7 ≤ 8; decide), rfl, ?_, ?_, Or.inl rfl⟩
  · exact ⟨1, .own rfl rfl, by decide⟩
  · exact ⟨none, 2, .parent rfl rfl rfl (.absent rfl rfl rfl), by decide, .absent⟩

private theorem pipeline_symbols (lower upper : UInt16) (query : JSString) : ArraySymbolsAllocated (pipelineBefore lower upper query).base := by
  intro entry member reference equal
  simp only [pipelineBefore, List.mem_cons, List.not_mem_nil, or_false] at member
  subst entry
  cases equal

private theorem pipeline_exec (lower upper : UInt16) (query : JSString) :
    NodePatternBinding.ExecRealm (pipelineBefore lower upper query).base labelStandardContext.iterators 2 5 query := by
  refine ⟨rfl, ?_, (by change 1 ≤ 3; decide), (by change 2 ≤ 3; decide),
    (by change 3 ≤ 3; decide), (by change 5 ≤ 5; decide), (by change 5 ≤ 5; decide), rfl⟩
  exact ⟨true, false, true, 1, .own rfl rfl, by decide⟩

/-- Arbitrary safe constructor endpoints are inhabited using a real label match.
No supplied match array/raw capture is hidden in this initial fixture. -/
theorem actual_label_produces_constructor_inputs (lower upper : UInt16) (query : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper) (ordered : lower.toNat ≤ upper.toNat) :
    PatternConstruct.Inputs (resultState (pipelineBefore lower upper query) labelStandardContext (safeRangeLabel idName lower upper)).base.regexp
      labelStandardContext.iterators.constructors (safeRangeLabel idName lower upper) idName 1 6
      (captures (safeRangeLabel idName lower upper) idName (some (PatternConstruct.rawBody lower upper))) lower upper ⟨2⟩
      ⟨standardLabelRegExpOwn 9 5, some 0, true⟩ :=
  produced_constructor_inputs _ _ _ lower upper _ _ _ (pipeline_inputs lower upper query safeLower safeUpper ordered)

theorem four_stage_source_pipeline_has_no_supplied_capture_or_matcher (query : JSString) :
    NodeRegExpExec.sourceExec 20 labelStandardOldContext.methods labelStandardOldContext.functions labelStandardOldContext.members labelStandardOldContext.builtins
      (NodePatternBinding.boundState (resultState (pipelineBefore 48 57 query) labelStandardContext (safeRangeLabel idName 48 57)).base
        labelStandardContext.iterators 2 48 57 (safeRangeLabel idName 48 57) idName 7 8 .undefined).regexp =
      some (.ok (NodeRegExpExec.resultState
        (NodePatternBinding.boundState (resultState (pipelineBefore 48 57 query) labelStandardContext (safeRangeLabel idName 48 57)).base
          labelStandardContext.iterators 2 48 57 (safeRangeLabel idName 48 57) idName 7 8 .undefined).regexp query)) := by
  exact (source_label_construct_binding_digits_exec_satisfies 0 0 0 0 (pipelineBefore 48 57 query) labelStandardContext idName query
    6 7 8 5 ⟨2⟩ ⟨standardLabelRegExpOwn 9 5, some 0, true⟩ .undefined
    (pipeline_inputs 48 57 query (by decide) (by decide) (by decide)) (pipeline_realm 48 57 query)
    (pipeline_symbols 48 57 query) (pipeline_exec 48 57 query)).2.2.2.1

private def pipelineRun (query : JSString) := do
  let produced ← (sourceMatch 128 labelStandardContext (pipelineBefore 48 57 query))
  let produced ← produced.toOption
  let tuple ← PatternConstruct.sourceConstruct 16 labelStandardOldContext produced.base.regexp
  let (value, tuple) ← tuple.toOption
  let selected : ArrayBindingState := {produced.base with regexp := {tuple with ambient := {tuple.ambient with environment := ("pattern", value) :: tuple.ambient.environment}}}
  let binding ← NodePatternBinding.sourceBinding 4 labelStandardContext.iterators selected
  let (_, binding) ← binding.toOption
  let result ← NodeRegExpExec.sourceExec 20 labelStandardOldContext.methods labelStandardOldContext.functions labelStandardOldContext.members labelStandardOldContext.builtins binding.regexp
  let result ← result.toOption
  pure (result.ambient.environment.lookup "m", result.ambient.environment.lookup "name", result.ambient.environment.lookup "matcher",
    result.ambient.heap[1]?, result.ambient.heap[2]?, result.ambient.heap[3]?)

theorem parsed_four_stage_pipeline_computes_captures_tuple_bindings_and_match :
    pipelineRun [49,50] = some (some (.array 3), some (.string idName), some (.object 8),
      some (captures (safeRangeLabel idName 48 57) idName (some (PatternConstruct.rawBody 48 57))),
      some [.string (safeRangeLabel idName 48 57), .string idName, .object 8], some [.string [49,50]]) := by cbv


private def getterFixture (descriptor : PropertyDescriptor) (slot : Value := .function 13) : LabelMatchState :=
  let old := labelStandardState [58,120]
  let object : OrdinaryObject := ⟨[(labelFlagKey .global, descriptor), (lastIndexKey, .data (.number 17) false false false)], some 2, false⟩
  {old with
    base := {old.base with regexp := {old.base.regexp with ambient := {old.base.regexp.ambient with objects := old.base.regexp.ambient.objects.set 6 object}}}
    accessors := ⟨6, .string (labelFlagKey .global), slot⟩ :: old.accessors}
private def readGlobal (before : LabelMatchState) :=
  (getLabelProperty 128 labelStandardContext (.object 6) 6 (.string (labelFlagKey .global)) before).map Prod.fst

/-- Real current own descriptors win over old sidecar identities. Missing getter
is undefined and never invokes the incompatible identity stored in that slot. -/
theorem current_data_and_missing_getter_dominate_accessor_sidecar :
    readGlobal (getterFixture (.data (.number 0) false false false) (.function 999)) = .ok (.number 0) ∧
    readGlobal (getterFixture (.accessor .missing .unsupported true true) (.function 999)) = .ok .undefined := by cbv

theorem flags_getter_reads_current_truthy_property_override :
    (invokeLabelGetter 128 labelStandardContext (.function 11) (.object 6)
      (getterFixture (.data (.number 17) false false false))).map Prod.fst = .ok (.string [103]) := by cbv

private def globalRangeFixture : LabelMatchState :=
  let old := labelStandardState [58,120]
  {old with base := {old.base with regexp := {old.base.regexp with brands := [(6, ⟨digitsPattern, [103], RangeRegExp.code 48 57⟩)]}}}

theorem intrinsic_flag_uses_original_receiver_and_old_range_brand :
    readGlobal globalRangeFixture = .ok (.boolean true) ∧
    (getLabelProperty 128 labelStandardContext (.object 2) 2 (.string (labelFlagKey .global)) globalRangeFixture).map Prod.fst = .ok .undefined := by cbv

theorem unresolved_intrinsic_getter_identity_fails_model_domain :
    readGlobal (getterFixture (.accessor .unsupported .missing false true) (.function 999)) = .error .getterDomain := by cbv


/-- Retained real optional-zero counterexample: a successful empty quantified
body is discarded with its original undefined capture, not materialized as ''. -/
theorem nullable_quantifier_keeps_original_undefined_capture :
    (parseLabelMatch "const match = label.match(/^()?$/)" ["label"]).map
      (fun declaration => (executeLabelMatch 128 defaultSplitLimit labelStandardContext declaration (labelStandardState [])).map
        (fun state => (state.base.regexp.ambient.heap[1]?, observeLabelResult state 1 .one, observeLabelResult state 1 .two))) =
      some (.ok (some [.string [], .undefined], some (.data .undefined true true true), none)) := by cbv

/-- info: 'HonoLean.Upstream.LabelMatch.source_match_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_match_satisfies
/-- info: 'HonoLean.Upstream.LabelMatch.source_match_then_construct_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_match_then_construct_satisfies
/-- info: 'HonoLean.Upstream.LabelMatch.source_label_construct_binding_digits_exec_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_label_construct_binding_digits_exec_satisfies
/-- info: 'HonoLean.Upstream.LabelMatch.Checks.arbitrary_utf16_source_has_independent_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms arbitrary_utf16_source_has_independent_contract

/-- info: 'HonoLean.Upstream.LabelMatch.Checks.actual_label_produces_constructor_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_label_produces_constructor_inputs
/-- info: 'HonoLean.Upstream.LabelMatch.Checks.four_stage_source_pipeline_has_no_supplied_capture_or_matcher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms four_stage_source_pipeline_has_no_supplied_capture_or_matcher

end HonoLean.Upstream.LabelMatch.Checks
