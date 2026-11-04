import HonoLean.Upstream.SourceSubset.SparseSequence

namespace HonoLean.Upstream.SourceSubset.SparseSequenceChecks

open ECMA2025
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private def source := "const targetCurNodes = (curNodesQueue[componentCount] ||= [])\ntargetCurNodes.push(child)"
private def bindings := ["curNodesQueue", "componentCount", "child"]
private def program : List SparseStmt :=
  [.declare "targetCurNodes" (.logicalOrAssign (.variable "curNodesQueue") (.variable "componentCount") (.arrayLiteral [])),
   .evaluate (.call (.variable "targetCurNodes") "push" [.variable "child"])]

theorem parses_original_logical_assignment : parseSparseSequence source bindings = some program := by cbv

theorem adjacent_maximal_munch_and_old_entries_closed :
    tokenizeFragment "q[i] ||= []" = some [.name "q", .punctuation "[", .name "i", .punctuation "]", .punctuation "||=", .punctuation "[", .punctuation "]"] ∧
    tokenizeFragment "q[i] || = []" = some [.name "q", .punctuation "[", .name "i", .punctuation "]", .punctuation "||", .punctuation "=", .punctuation "[", .punctuation "]"] ∧
    parseBlock source bindings = none ∧ parseMutableSequence source bindings [] = none ∧
    parsePrivateControl source bindings [] = none := by cbv

theorem rejects_unsupported_logical_forms :
    (["const t = (curNodesQueue[componentCount] || = [])", "const t = (curNodesQueue[componentCount] ||= []) t.push(child)",
      "const t = (curNodesQueue[unknown] ||= [])", "const t = (curNodesQueue[++componentCount] ||= [])",
      "const t = (curNodesQueue[componentCount] ||= ++child)", "const t = (curNodesQueue[componentCount] ||= t)",
      "const child = (curNodesQueue[componentCount] ||= [])", "const t = (child ||= [])",
      "const t = (curNodesQueue[componentCount] ||= []); return t", "const t = (curNodesQueue[componentCount] ||= []); }"] : List String).all
      (fun text => (parseSparseSequence text bindings).isNone) = true := by cbv

private def cellView (array : IndexedArray) : Nat × List (Option Value) :=
  (array.length, [array.own 0, array.own 1, array.own 2, array.own 3])
private def probe (state : IndexedState) :=
  (state.environment.lookup "targetCurNodes", state.heap.map cellView)
private def emptyBefore : IndexedState :=
  {environment := [("curNodesQueue", .array 0), ("componentCount", .number 2), ("child", .object 0)]
   heap := [ofList []]}

/-- The missing indices stay absent, rather than becoming own undefined cells. -/
theorem sparse_extension_creates_holes_and_pushes_selected_array :
    (parseSparseSequence source bindings).map (fun code => (executeSparseSequence 32 [] code emptyBefore).map probe) =
    some (.ok (some (.array 1), [(3, [none, none, some (.array 1), none]),
      (1, [some (.object 0), none, none, none])])) := by cbv

private def truthyBefore : IndexedState :=
  {environment := [("curNodesQueue", .array 0), ("componentCount", .number 0), ("child", .object 0)]
   heap := [ofList [.array 1], ofList []]}

theorem truthy_existing_empty_array_skips_allocation :
    (executeSparseSequence 32 [] program truthyBefore).map probe =
    .ok (some (.array 1), [(1, [some (.array 1), none, none, none]), (1, [some (.object 0), none, none, none])]) := by cbv

theorem truthy_skips_even_invalid_rhs :
    (evalSparseInitializer 32 (.logicalOrAssign (.variable "curNodesQueue") (.number 0)
      (.variable "missing")) truthyBefore).map (fun (value, state) => (value, state.heap.length)) =
      .ok (.array 1, 2) := by cbv

private def selfBefore : IndexedState :=
  {environment := [("curNodesQueue", .array 0), ("componentCount", .number 0), ("child", .object 0)]
   heap := [ofList [.array 0]]}

theorem target_queue_self_alias_push_uses_current_length :
    (executeSparseSequence 32 [] program selfBefore).map probe =
      .ok (some (.array 0), [(2, [some (.array 0), some (.object 0), none, none])]) := by cbv

private def hole : IndexedArray := ⟨2, fun index => if index = 1 then some (.array 1) else none⟩
private def ownUndefined : IndexedArray := ⟨2, fun index => if index = 0 then some .undefined else if index = 1 then some (.array 1) else none⟩

theorem own_hole_distinction_survives_equal_read_observation :
    hole.own 0 = none ∧ ownUndefined.own 0 = some .undefined ∧
    observe hole = observe ownUndefined ∧ (shiftSteps hole).2.own 0 = some (.array 1) ∧
    (concatOwn (ofList []) hole).own 0 = none ∧ (concatOwn (ofList []) ownUndefined).own 0 = some .undefined := by cbv

theorem read_erasure_laws_apply_without_densifying :
    observe (shiftSteps hole).2 = (observe hole).tail ∧
    observe (concatOwn hole ownUndefined) = observe hole ++ observe ownUndefined :=
  ⟨observe_shiftSteps hole, observe_concatOwn hole ownUndefined⟩

private def consumer : List SparseStmt :=
  [.declare "shifted" (.ordinary (.call (.variable "curNodesQueue") "shift" [])),
   .rebind "curNodes" (.conditional (.variable "shifted")
     (.call (.variable "tempNodes") "concat" [.variable "shifted"]) (.variable "tempNodes"))]

theorem parses_actual_sparse_consumer :
    parseSparseSequence "const shifted = curNodesQueue.shift()\ncurNodes = shifted ? tempNodes.concat(shifted) : tempNodes"
      ["curNodesQueue", "curNodes", "tempNodes"] ["curNodes"] = some consumer := by cbv

/-- Shift of a hole reads undefined, deletes/moves own cells, and selects the
actual temp reference; it does not materialize an own undefined at the hole. -/
theorem sparse_consumer_moves_holes_and_retains_outer_binding :
    (executeSparseSequence 32 ["curNodes"] consumer
      {environment := [("curNodesQueue", .array 0), ("curNodes", .array 2), ("tempNodes", .array 1)],
       heap := [hole, ofList [.object 0], ofList []]}).map
      (fun state => (state.environment.lookup "curNodes", state.heap.map cellView)) =
    .ok (some (.array 1), [(1, [some (.array 1), none, none, none]),
      (1, [some (.object 0), none, none, none]), (0, [none, none, none, none])]) := by cbv

theorem legal_index_boundary_is_not_named_property_boundary :
    LegalArrayIndex 4294967294 ∧ ¬LegalArrayIndex 4294967295 ∧
    (indexedSet (ofList []) 4294967294 .null).length = 4294967295 ∧
    setAt 0 4294967295 .null {heap := [ofList []]} = .error .unsupported :=
  ⟨by change 4294967294 < 4294967295; decide,
   by change ¬(4294967295 < 4294967295); decide, by decide, rfl⟩

theorem explicit_ambient_frame_is_preserved :
    (embedIndexedState {
      objects := [emptyNullObject]
      thisValue := .object 0
      privates := PrivateStore.ofData [("tag", 1)] [(0, [(1, .number 2)])]} emptyBefore).objects = [emptyNullObject] ∧
    (embedIndexedState {objects := [emptyNullObject], thisValue := .object 0} emptyBefore).thisValue = .object 0 := by cbv

/-- RHS shifts the operand-source arrays again, but saved queue3/index2 are
still used. Each initial base/index expression executes exactly once. -/
theorem effects_do_not_change_saved_base_or_index :
    (evalSparseInitializer 32
      (.logicalOrAssign (.call (.variable "bases") "shift" []) (.call (.variable "indices") "shift" [])
        (.conditional (.call (.variable "bases") "shift" [])
          (.conditional (.call (.variable "indices") "shift" []) (.arrayLiteral []) .null) .null))
      {environment := [("bases", .array 0), ("indices", .array 1)]
       heap := [ofList [.array 3, .array 4], ofList [.number 2, .number 1], ofList [], ofList [], ofList []]}).map
      (fun (value, state) => (value, state.heap.map cellView)) =
    .ok (.array 5, [(0, [none, none, none, none]), (0, [none, none, none, none]),
      (0, [none, none, none, none]), (3, [none, none, some (.array 5), none]),
      (0, [none, none, none, none]), (0, [none, none, none, none])]) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.evalSparseInitializer_truthy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.evalSparseInitializer_truthy
/-- info: 'HonoLean.Upstream.SourceSubset.evalSparseInitializer_falsy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.evalSparseInitializer_falsy
/-- info: 'HonoLean.Upstream.ECMA2025.observe_shiftSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.ECMA2025.observe_shiftSteps
/-- info: 'HonoLean.Upstream.ECMA2025.observe_concatOwn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.ECMA2025.observe_concatOwn

end HonoLean.Upstream.SourceSubset.SparseSequenceChecks
