import HonoLean.Upstream.SourceSubset.ForInSequence

namespace HonoLean.Upstream.SourceSubset.ForInSequenceChecks

open ECMA2025
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private def source := "for (const _ in child.#children) {\n  child.#params = params\n  const componentCount = m[0].match(/\\//g)?.length ?? 0\n  const targetCurNodes = (curNodesQueue[componentCount] ||= [])\n  targetCurNodes.push(child)\n  break\n}"
private def bindings := ["child", "params", "m", "curNodesQueue"]
private def assignment : Assignment := ⟨.privateProperty (.variable "child") "params", .variable "params"⟩
private def body : List ForInStmt :=
  [.privateWrite assignment,
   .regexp (.declare "componentCount" (unitCountExpression (.index (.variable "m") (.number 0)) 47)),
   .regexp (.sparse (.declare "targetCurNodes" (.logicalOrAssign (.variable "curNodesQueue") (.variable "componentCount") (.arrayLiteral [])))),
   .regexp (.sparse (.evaluate (.call (.variable "targetCurNodes") "push" [.variable "child"]))), .breakLoop]
private def program : List ForInStmt := [.forIn "_" (.privateProperty (.variable "child") "children") body]

theorem parses_original_forin_private_count_schedule_break :
    parseForInSequence source bindings ["children", "params"] = some program := by cbv

theorem rejects_head_tdz_binder_reads_callbacks_and_outer_writes :
    (["for (const child in child.#children) { break }", "for (const _ in child.#children) { child.#params = _ }",
      "for (const _ in child.#children) { curNodesQueue.push(_) }", "for (const _ in child.#children) { const _ = 1 }",
      "for (const _ in child.#children) { f() }", "for (const _ in child.#children) { params = child }",
      "for (const _ in child.#children) { curNodesQueue.push(++m) }", "for (let _ in child.#children) { break }",
      "for (const _ of child.#children) { break }", "for (const _ in child.#children) { break label }"] : List String).all
      (fun text => (parseForInSequence text ("f" :: bindings) ["children", "params"]).isNone) = true := by cbv

private def childrenObject : OrdinaryObject :=
  {own := [([109], .accessor .unsupported .unsupported true false),
           ([55296, 233], .data .null false true false),
           ([95], .data (.number 0) false false false)]}
private def path : JSString := [47, 97, 47]
private def before : ForInState :=
  {ambient := {
      environment := [("m", .null), ("params", .null), ("_", .number 999)]
      heap := [[.number 888]]
      objects := [emptyNullObject, emptyNullObject, childrenObject]
      thisValue := .object 1
      functions := [⟨⟨"opaque", .number 7⟩, [("capture", .string [55296]) ]⟩]
      sets := [[[99]]]
      privates := {
        names := [("children", 0), ("params", 1), ("keep", 2)]
        elements := [(0, [(0, .data (.object 2)), (1, .data (.object 0)), (2, .data (.array 0))])]}}
   regexp := {
      arrays := {
        environment := [("child", .object 0), ("params", .object 1), ("m", .array 0), ("curNodesQueue", .array 1),
          ("_", .number 123), ("componentCount", .number 99), ("targetCurNodes", .number 77)]
        heap := [ofList [.string path], ofList []]}
      regexps := [⟨120, 17⟩]}}

private def finalProbe : ForInCompletion → Option (List (String × Value) × Nat × Option PrivateElement ×
    List (Nat × List (Option Value)) × List UnitRegExpCell × Nat)
  | .breakLoop _ => none
  | .normal state => some (state.regexp.arrays.environment, state.regexp.arrays.heap.length,
      (state.ambient.privates.elements.lookup 0).bind (fun fields => fields.lookup 1),
      state.regexp.arrays.heap.map (fun array => (array.length, [array.own 0, array.own 1, array.own 2])),
      state.regexp.regexps, state.regexp.executions.length)

theorem actual_loop_uses_authoritative_arrays_and_restores_locals :
    (parseForInSequence source bindings ["children", "params"]).map
      (fun code => (executeForInSequence 66 code before).map finalProbe) =
    some (.ok (some (before.regexp.arrays.environment, 4, some (.data (.object 1)),
      [(1, [some (.string path), none, none]), (3, [none, none, some (.array 3)]),
       (2, [some (.string [47]), some (.string [47]), none]), (1, [some (.object 0), none, none])],
      [⟨120, 17⟩, ⟨47, 0⟩], 1))) := by cbv

theorem actual_loop_preserves_arbitrary_nonprivate_ambient_frame :
    (executeForInSequence 66 program before).map (fun completion => match completion with
      | .normal state => some (state.ambient.environment, state.ambient.heap, state.ambient.objects,
          state.ambient.functions, state.ambient.sets, state.ambient.thisValue)
      | .breakLoop _ => none) =
    .ok (some (before.ambient.environment, before.ambient.heap, before.ambient.objects,
      before.ambient.functions, before.ambient.sets, before.ambient.thisValue)) := by cbv

private def emptyBefore : ForInState :=
  {ambient := {
      objects := [emptyNullObject, emptyNullObject,
        {own := [([55296], .accessor .unsupported .unsupported false false)]}]
      privates := {
        names := [("children", 0), ("params", 1)]
        elements := [(0, [(0, .data (.object 2)), (1, .method (.number 999))])]}}
   regexp := {
      arrays := {environment := [("child", .object 0)]}
      regexps := [⟨120, 17⟩]}}

/-- No m, params, queue or writable params cell is supplied. Empty descriptor
inspection skips the entire body, without invoking its unsupported getter. -/
theorem empty_children_skip_every_body_requirement :
    (parseForInSequence source bindings ["children", "params"]).map
      (fun code => executeForInSequence 66 code emptyBefore) = some (.ok (.normal emptyBefore)) := by cbv

theorem omitting_break_really_iterates_and_registers_twice :
    (parseForInSequence "for (const _ in child.#children) {\n  child.#params = params\n  const componentCount = m[0].match(/\\//g)?.length ?? 0\n  const targetCurNodes = (curNodesQueue[componentCount] ||= [])\n  targetCurNodes.push(child)\n}" bindings ["children", "params"]).map
      (fun code => (executeForInSequence 100 code before).map (fun completion => match completion with
        | .normal state => some (state.regexp.arrays.heap.length, state.regexp.executions.length,
            state.regexp.arrays.heap[3]?.map observe)
        | .breakLoop _ => none)) = some (.ok (some (5, 2, some [.object 0, .object 0]))) := by cbv

theorem descriptor_inspection_uses_enumerability_not_values_or_getters :
    enumerableOwn childrenObject = [[109], [55296, 233]] ∧
    enumerableOwn {own := [([97], .data .null true false true), ([97], .data .null true true true)]} = [] ∧
    enumerableOwn {own := [([], .data .null false true false)]} = [[]] := by cbv

private def bodyAfter (key : JSString) : ForInState :=
  {ambient := (forInDataState before 0 1 (.object 1)).ambient
   regexp := {
      arrays := {
        environment := [("targetCurNodes", .array 3), ("componentCount", .number 2), ("_", .string key)] ++ before.regexp.arrays.environment
        heap := [ofList [.string path], indexedSet (ofList []) 2 (.array 3),
          ofList [.string [47], .string [47]], pushOwn (ofList []) (.object 0)]}
      regexps := before.regexp.regexps ++ [⟨47, 0⟩]
      executions := [executeUnitGlobal path ⟨47, 0⟩]}}

private def commonAfter : ForInState := restoreForInEnvironment before.regexp.arrays.environment (bodyAfter [])

/-- Any raw UTF16 property name, even 'm'/'params'/'_', has exactly the same
scoped endpoint because only the unused binder receives it. -/
theorem actual_body_breaks_independently_of_key (key : JSString) :
    executeForInSequence 64 body (bindForInKey "_" key before) = .ok (.breakLoop (bodyAfter key)) := by cbv

theorem actual_break_is_independent_of_all_legal_key_orders (keys : List JSString)
    (legal : LegalForInOrder childrenObject keys) :
    executeForInKeys 65 "_" body keys before = .ok commonAfter := by
  apply executeForInKeys_all_orders 64 "_" body childrenObject before commonAfter keys legal
  · exact ⟨[109], .accessor .unsupported .unsupported true false, rfl, rfl⟩
  · intro key _
    exact ⟨bodyAfter key, actual_body_breaks_independently_of_key key, rfl⟩

/-- info: 'HonoLean.Upstream.ECMA2025.enumerableOwn_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.ECMA2025.enumerableOwn_member
/-- info: 'HonoLean.Upstream.SourceSubset.forInChildren_private_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.forInChildren_private_data
/-- info: 'HonoLean.Upstream.SourceSubset.executeForInPrivateWrite_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.executeForInPrivateWrite_data
/-- info: 'HonoLean.Upstream.SourceSubset.executeForInKeys_all_orders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.executeForInKeys_all_orders

end HonoLean.Upstream.SourceSubset.ForInSequenceChecks
