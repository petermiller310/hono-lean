import HonoLean.Upstream.NodePatternBinding.Composition

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace HonoLean.Upstream.NodePatternBinding.Checks
open SourceSubset ECMA2025

/-- Supplied old realm/ordinary graph, not native bootstrap or Hono installation.
Every opaque array/object reference in these fixtures is already allocated. -/
private def oldContext : RegExpConstructContext :=
  ⟨⟨1, [⟨⟨"old", [], .named "void", []⟩, [], []⟩]⟩,
   ⟨2, [⟨⟨"old", "input", []⟩, [], []⟩]⟩,
   ⟨3, [⟨⟨"echo", "input", [.ret (.variable "input")]⟩, [], []⟩,
        ⟨⟨"other", "input", [.ret .null]⟩, [], []⟩]⟩,
   ⟨5, [.regexpExec]⟩, ⟨6, [⟨1⟩]⟩⟩
private def context : ArrayIteratorContext := ⟨oldContext, ⟨7, [.arrayValues, .arrayNext]⟩, 2, 3, 0⟩
private def label : JSString := [58, 110]
private def name : JSString := [110]
private def query : JSString := [49, 50]
private def prototype : OrdinaryObject := ⟨[(NodeExecCall.execKey, .data (.function 5) true false true)], some 0, true⟩
private def arrayProto : OrdinaryObject := ⟨[], some 0, true⟩
private def iteratorProto : OrdinaryObject := ⟨[(iteratorNextKey, .data (.function 8) true false true)], some 0, true⟩
private def before (lo : UInt16 := 48) (hi : UInt16 := 57) (input : JSString := query) : ArrayBindingState :=
  { regexp := {ambient := {
      environment := [("label", .string label), ("match", .array 1), ("RegExp", .function 6),
        ("restPathString", .string input), ("name", .boolean false), ("matcher", .boolean true)]
      heap := [[.object 0], [.string [], .string name, .string (PatternConstruct.rawBody lo hi)]]
      objects := [objectPrototypeProjection, prototype, arrayProto, iteratorProto]
      functions := [⟨⟨"old", .number 0⟩, []⟩]
      thisValue := .object 0
      privates := .ofData [("old", 19)] [(0, [(19, .number 17)])]
      sets := [[name]]}}
    symbols := [(.object 2, [(.iterator, .data (.function 7) true false true)]),
      (.array 0, [(.iterator, .data (.function 7) true false true)])]
    iterators := [(0, ⟨none, 9⟩)]}

private theorem old_closed (lo hi : UInt16) (input : JSString) : IteratorPrototypeClosed (before lo hi input).regexp.ambient.objects := by
  intro reference object found parent edge
  rcases reference with _ | _ | _ | _ | reference <;>
    simp [before, prototype, arrayProto, iteratorProto] at found <;>
    subst object <;> simp [objectPrototypeProjection] at edge <;> subst parent <;> change 0 < 4 <;> decide

private theorem realm (lo hi : UInt16) (input : JSString) : Realm (before lo hi input) context 7 8 .undefined := by
  refine ⟨old_closed lo hi input, ⟨arrayProto, rfl⟩, ⟨iteratorProto, rfl⟩, ⟨objectPrototypeProjection, rfl⟩,
    rfl, (by change 1 ≤ 7; decide), (by change 2 ≤ 7; decide), (by change 3 ≤ 7; decide),
    (by change 5 ≤ 7; decide), (by change 6 ≤ 7; decide), (by change 7 ≤ 7; decide),
    (by change 7 ≤ 7; decide), rfl, (by change 7 ≤ 8; decide), rfl, ?_, ?_, Or.inl rfl⟩
  · exact ⟨1, .own rfl rfl, by decide⟩
  · exact ⟨none, 2, .parent rfl rfl rfl (.absent rfl rfl rfl), by decide, .absent⟩

private theorem allocated (lo hi : UInt16) (input : JSString) : ArraySymbolsAllocated (before lo hi input) := by
  intro entry member reference equal
  simp only [before, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · contradiction
  · cases equal
    change 0 < 2
    decide

private theorem construct_inputs (lo hi : UInt16) (input : JSString) (safeLo : RangeRegExp.SafeEndpoint lo)
    (safeHi : RangeRegExp.SafeEndpoint hi) (ordered : lo.toNat ≤ hi.toNat) :
    PatternConstruct.Inputs (before lo hi input).regexp oldContext label name 1 6
      [.string [], .string name, .string (PatternConstruct.rawBody lo hi)] lo hi ⟨1⟩ prototype := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, (by change 3 ≤ 4294967295; decide), safeLo, safeHi, ordered, rfl,
    (by change 1 ≤ 6; decide), (by change 2 ≤ 6; decide), (by change 3 ≤ 6; decide),
    (by change 5 ≤ 6; decide), (by change 6 ≤ 6; decide), (by change 6 ≤ 6; decide), rfl, rfl⟩

private theorem exec_realm (lo hi : UInt16) (input : JSString) : ExecRealm (before lo hi input) context 1 5 input := by
  refine ⟨rfl, ?_, (by change 1 ≤ 3; decide), (by change 2 ≤ 3; decide),
    (by change 3 ≤ 3; decide), (by change 5 ≤ 5; decide), (by change 5 ≤ 5; decide), rfl⟩
  exact ⟨true, false, true, 1, .own rfl rfl, by decide⟩

/-- Arbitrary safe endpoints inhabit the initial-only constructor/binding domain.
No desired tuple, matcher binding, compiled record or iterator run is supplied. -/
theorem arbitrary_safe_range_has_causal_source_binding (lo hi : UInt16) (input : JSString)
    (safeLo : RangeRegExp.SafeEndpoint lo) (safeHi : RangeRegExp.SafeEndpoint hi) (ordered : lo.toNat ≤ hi.toNat) :
    sourceBinding 4 context (constructedActivation (before lo hi input) 1 lo hi label name) =
      some (.ok (record (constructedActivation (before lo hi input) 1 lo hi label name) 8,
        boundState (before lo hi input) context 1 lo hi label name 7 8 .undefined)) := by
  exact (source_construct_then_binding_satisfies 0 0 (before lo hi input) context label name 1 6 7 8
    [.string [], .string name, .string (PatternConstruct.rawBody lo hi)] lo hi ⟨1⟩ prototype .undefined
    (construct_inputs lo hi input safeLo safeHi ordered) (realm lo hi input) (allocated lo hi input)).2.2.1

/-- Exact URL tuple expression, actual138, then actual156. The query is the
initial caller input; no execution of source146–154 or tree/cache claim. -/
theorem digits_pipeline_derives_actual_exec_inputs :
    NodeRegExpExec.sourceExec 20 oldContext.methods oldContext.functions oldContext.members oldContext.builtins
      (boundState (before 48 57 query) context 1 48 57 label name 7 8 .undefined).regexp =
      some (.ok (NodeRegExpExec.resultState (boundState (before 48 57 query) context 1 48 57 label name 7 8 .undefined).regexp query)) := by
  exact (source_construct_binding_digits_exec_satisfies 0 0 0 (before 48 57 query) context label name query 1 6 7 8 5
    [.string [], .string name, .string (PatternConstruct.rawBody 48 57)] ⟨1⟩ prototype .undefined
    (construct_inputs 48 57 query (by decide) (by decide) (by decide)) (realm 48 57 query) (allocated 48 57 query)
    (exec_realm 48 57 query)).2.2.1

private def actual (values : List Value) : ArrayBindingState :=
  let old := before
  {old with regexp := {old.regexp with ambient := {old.regexp.ambient with
    environment := ("pattern", .array 1) :: old.regexp.ambient.environment
    heap := [[.object 0], values]}}}
private def observe (result : Option (Except ArrayBindingError (ArrayIteratorRecord × ArrayBindingState))) :=
  result.map (fun result => result.map (fun (record, state) =>
    (record, state.regexp.ambient.environment.take 2, state.iterators.lookup 4,
     state.trace.countP (fun (event : ArrayIteratorEvent) => match event with | .resultAllocated _ _ _ => true | _ => false),
     state.trace.countP (fun (event : ArrayIteratorEvent) => match event with | .valueGet _ _ => true | _ => false),
     state.trace.countP (fun (event : ArrayIteratorEvent) => match event with | .returnGet _ _ => true | _ => false))))

theorem default_protocol_uses_three_next_two_values_one_close :
    observe (sourceBinding 4 context (actual [.string label, .string name, .boolean true])) =
      some (.ok (⟨4, .function 8, false⟩, [("matcher", .boolean true), ("name", .string name)],
        some ⟨some 1, 3⟩, 3, 2, 1)) := by cbv

theorem short_tuple_exhausts_once_and_omits_close :
    observe (sourceBinding 4 context (actual [.string label])) =
      some (.ok (⟨4, .function 8, true⟩, [("matcher", .undefined), ("name", .undefined)],
        some ⟨none, 1⟩, 2, 0, 0)) := by cbv

theorem empty_tuple_exhausts_once :
    observe (sourceBinding 4 context (actual [])) =
      some (.ok (⟨4, .function 8, true⟩, [("matcher", .undefined), ("name", .undefined)],
        some ⟨none, 0⟩, 1, 0, 0)) := by cbv

theorem utf16_name_and_true_matcher_remain_opaque :
    observe (sourceBinding 4 context (actual [.null, .string [55357, 56832, 47, 55296], .boolean true])) =
      some (.ok (⟨4, .function 8, false⟩, [("matcher", .boolean true), ("name", .string [55357, 56832, 47, 55296])],
        some ⟨some 1, 3⟩, 3, 2, 1)) := by cbv

private def pipelineObservation (input : JSString) :=
  (NodeRegExpExec.sourceExec 20 oldContext.methods oldContext.functions oldContext.members oldContext.builtins
    (boundState (before 48 57 input) context 1 48 57 label name 7 8 .undefined).regexp).map
    (fun result => result.map (fun state => (state.ambient.environment.lookup "m", state.ambient.heap[3]?,
      state.ambient.objects[4]?, state.brands.lookup 4)))

theorem pipeline_success_retains_constructed_brand_and_returns_real_match :
    pipelineObservation [49, 50] = some (.ok (some (.array 3), some [.string [49, 50]],
      some (initializedRegExpObject 1), some (constructedRangeRecord 48 57))) := by cbv

theorem pipeline_failure_allocates_no_match_array :
    pipelineObservation [49, 120] = some (.ok (some .null, none,
      some (initializedRegExpObject 1), some (constructedRangeRecord 48 57))) := by cbv

#print axioms source_binding_protocol_satisfies
#print axioms source_binding_satisfies
#print axioms source_construct_then_binding_satisfies
#print axioms source_construct_binding_digits_exec_satisfies
#print axioms arbitrary_safe_range_has_causal_source_binding
#print axioms digits_pipeline_derives_actual_exec_inputs

end HonoLean.Upstream.NodePatternBinding.Checks
