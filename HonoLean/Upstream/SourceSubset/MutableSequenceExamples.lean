import HonoLean.Upstream.SourceSubset.MutableSequence

namespace HonoLean.Upstream.SourceSubset.MutableSequenceChecks

open ECMA2025
set_option maxRecDepth 4096

private def bindings := ["curNodesQueue", "curNodes", "tempNodes"]
private def queueSource := "const shifted = curNodesQueue.shift()\ncurNodes = shifted ? tempNodes.concat(shifted) : tempNodes"
private def queueProgram : List Stmt :=
  [.declare "shifted" (.call (.variable "curNodesQueue") "shift" []),
   .assign ⟨.variable "curNodes", .conditional (.variable "shifted")
     (.call (.variable "tempNodes") "concat" [.variable "shifted"]) (.variable "tempNodes")⟩]

/-- The extension returns the original conditional/concat/bare-assignment AST. -/
theorem parses_original_concat_ast : parseMutableSequence queueSource bindings ["curNodes"] = some queueProgram := by cbv

theorem old_entries_stay_closed :
    parseBlock "curNodes = tempNodes" bindings = none ∧
    parseExpression "tempNodes.concat(curNodes)" bindings = none ∧
    parsePrivateControl "curNodes = tempNodes" bindings [] = none ∧
    parsePrivateControl "tempNodes.concat(curNodes)" bindings [] = none := by cbv

theorem rejects_scope_and_syntax_gaps :
    (["unknown = tempNodes", "tempNodes = curNodes", "curNodes = ++tempNodes",
      "curNodes = tempNodes.concat()", "curNodes = tempNodes.concat(curNodes, curNodes)",
      "curNodes = tempNodes.concat(unknown)", "curNodes = tempNodes.concat(++curNodes)",
      "const fresh = []\nfresh = tempNodes", "let fresh = []\nfresh = tempNodes",
      "const curNodes = []", "curNodes = tempNodes curNodes = []", "curNodes = tempNodes\n[0] = null",
      "if (curNodes) { curNodes = tempNodes }", "return curNodes", "curNodes[0] = null"] : List String).all
      (fun source => (parseMutableSequence source bindings ["curNodes", "fresh"]).isNone) = true := by cbv

private def duplicateBefore : State :=
  {environment := [("unrelated", .number 8), ("curNodes", .number 1),
    ("curNodes", .number 2), ("tail", .number 9)]}

theorem first_binding_only_and_retained_rebind :
    (parseMutableSequence "curNodes = 7" bindings ["curNodes"]).map
      (fun program => executeMutableSequence 32 defaultSplitLimit ["curNodes"] program duplicateBefore) =
    some (.ok (.normal {duplicateBefore with environment :=
      [("unrelated", .number 8), ("curNodes", .number 7), ("curNodes", .number 2), ("tail", .number 9)]})) := by cbv

/-- The RHS's invalid-reference error precedes unresolved-LHS rejection. A
successful RHS instead reaches missingVariable after evaluation. The separate
allowlist failure is a model authority boundary, not native const ordering. -/
theorem rhs_precedes_missing_lhs_and_never_inserts :
    executeMutableRebind 32 defaultSplitLimit ["missing"] "missing"
      (.call (.variable "bad") "shift" []) {environment := [("bad", .array 9)]} = .error .invalidReference ∧
    executeMutableRebind 32 defaultSplitLimit ["missing"] "missing" (.arrayLiteral []) {} = .error .missingVariable ∧
    executeMutableRebind 32 defaultSplitLimit [] "curNodes" (.number 1) duplicateBefore = .error .unsupported := by cbv

/-- Source admission rejects this increment, but explicit model execution
demonstrates that writing the saved slot retains unrelated RHS lexical effects. -/
theorem rhs_environment_effect_is_retained :
    executeMutableRebind 32 defaultSplitLimit ["curNodes"] "curNodes" (.preIncrement "unrelated") duplicateBefore =
      .ok {duplicateBefore with environment :=
        [("unrelated", .number 9), ("curNodes", .number 9), ("curNodes", .number 2), ("tail", .number 9)]} := by cbv

theorem new_declarations_are_not_made_mutable_by_allowlist :
    executeMutableSequence 32 defaultSplitLimit ["fresh", "fresh"]
      [.declare "fresh" (.number 0), .assign ⟨.variable "fresh", .number 1⟩] {} = .error .unsupported := by cbv

private def aliasBefore : State :=
  {environment := [("a", .array 0)]
   heap := [[.array 0, .object 2]]
   thisValue := .object 4
   objects := List.replicate 5 emptyNullObject
   sets := [[[120]]]
   privates := PrivateStore.ofData [("saved", 7)] [(3, [(7, .number 8)])]}

theorem concat_is_fresh_shallow_and_self_alias_safe :
    intrinsic defaultSplitLimit (.array 0) "concat" [.array 0] aliasBefore =
      .ok (.array 1, {aliasBefore with heap :=
        [[.array 0, .object 2], [.array 0, .object 2, .array 0, .object 2]]}) := by cbv

theorem self_alias_has_independent_indexed_copy_contract :
    DenseConcatContract aliasBefore 0 0 (.array 1)
      {aliasBefore with heap := [[.array 0, .object 2], [.array 0, .object 2, .array 0, .object 2]]} :=
  intrinsic_concat_satisfies aliasBefore 0 0 [.array 0, .object 2] [.array 0, .object 2] rfl rfl

/-- Both input cells are read after the argument shifts the saved receiver.
The output length is two, rather than the old receiver length plus new length. -/
theorem concat_reads_after_argument_effect :
    evalExpression 32 defaultSplitLimit
      (.call (.variable "a") "concat" [.call (.variable "a") "shift" []])
      {environment := [("a", .array 0)], heap := [[.array 0, .number 7]]} =
    .ok (.array 1, {environment := [("a", .array 0)], heap := [[.number 7], [.number 7, .number 7]]}) := by cbv

theorem concat_rejects_missing_cells_and_wrong_arity :
    intrinsic defaultSplitLimit (.array 0) "concat" [.array 8] aliasBefore = .error .invalidReference ∧
    intrinsic defaultSplitLimit (.array 8) "concat" [.array 0] aliasBefore = .error .invalidReference ∧
    intrinsic defaultSplitLimit (.array 0) "concat" [] aliasBefore = .error .unsupported := by cbv

theorem scalar_arguments_append_once :
    intrinsic defaultSplitLimit (.array 0) "concat" [.string [120, 121]] aliasBefore =
      .ok (.array 1, {aliasBefore with heap := [[.array 0, .object 2], [.array 0, .object 2, .string [120, 121]]]}) ∧
    intrinsic defaultSplitLimit (.array 0) "concat" [.object 2] aliasBefore =
      .ok (.array 1, {aliasBefore with heap := [[.array 0, .object 2], [.array 0, .object 2, .object 2]]}) := by
  cbv
  exact ⟨rfl, rfl⟩

theorem scalar_argument_has_independent_copy_contract :
    DenseConcatValueContract aliasBefore 0 (.string [120, 121]) (.array 1)
      {aliasBefore with heap := [[.array 0, .object 2], [.array 0, .object 2, .string [120, 121]]]} :=
  intrinsic_concat_scalar_satisfies aliasBefore 0 (.string [120, 121]) [.array 0, .object 2] rfl (by intro reference; intro impossible; cases impossible)

/-- An empty shifted array remains truthy and therefore creates a fresh
concat result rather than reusing tempNodes. -/
theorem empty_array_shift_still_allocates :
    executeMutableSequence 32 defaultSplitLimit ["curNodes"] queueProgram
      {environment := [("curNodesQueue", .array 0), ("curNodes", .array 2), ("tempNodes", .array 1)],
       heap := [[.array 2], [.number 1], []]} =
    .ok (.normal {
      environment := [("shifted", .array 2), ("curNodesQueue", .array 0), ("curNodes", .array 3), ("tempNodes", .array 1)]
      heap := [[], [.number 1], [], [.number 1]]}) := by cbv

private def queueBefore : State :=
  {environment := [("curNodesQueue", .array 0), ("curNodes", .array 2), ("tempNodes", .array 1)]
   heap := [[.array 0], [.object 3], [.object 4]]
   objects := List.replicate 5 emptyNullObject}

/-- The shifted array aliases the queue itself. Shift empties it before the
concat reads; the retained outer curNodes points at the new result cell. -/
theorem actual_sequence_shift_then_concat_then_outer_rebind :
    (parseMutableSequence queueSource bindings ["curNodes"]).map
      (fun program => executeMutableSequence 32 defaultSplitLimit ["curNodes"] program queueBefore) =
    some (.ok (.normal {queueBefore with
      environment := [("shifted", .array 0), ("curNodesQueue", .array 0), ("curNodes", .array 3), ("tempNodes", .array 1)]
      heap := [[], [.object 3], [.object 4], [.object 3]]})) := by cbv

theorem falsy_shift_avoids_concat_allocation :
    executeMutableSequence 32 defaultSplitLimit ["curNodes"] queueProgram
      {environment := [("curNodesQueue", .array 0), ("curNodes", .array 2), ("tempNodes", .array 1)], heap := [[], [], []]} =
    .ok (.normal {
      environment := [("shifted", .undefined), ("curNodesQueue", .array 0), ("curNodes", .array 1), ("tempNodes", .array 1)]
      heap := [[], [], []]}) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.executeMutableRebind_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.executeMutableRebind_first

/-- info: 'HonoLean.Upstream.ECMA2025.intrinsic_concat_satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.ECMA2025.intrinsic_concat_satisfies

end HonoLean.Upstream.SourceSubset.MutableSequenceChecks
