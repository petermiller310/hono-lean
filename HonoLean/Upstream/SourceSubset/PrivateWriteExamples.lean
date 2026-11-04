import HonoLean.Upstream.SourceSubset.PrivateWrite
import HonoLean.Upstream.SourceSubset.PrivateClass

namespace HonoLean.Upstream.SourceSubset.PrivateWriteChecks

open ECMA2025
set_option maxRecDepth 32768

private def before : State :=
  {environment := [("node", .object 1), ("replacement", .number 7), ("receivers", .array 0),
      ("bad", .object 99), ("this", .object 2)]
   thisValue := .object 1
   objects := [emptyNullObject, {prototype := some 0, extensible := false}, emptyNullObject]
   heap := [[.object 1, .object 2]]
   functions := [⟨⟨"first", .number 0⟩, []⟩, ⟨⟨"second", .number 1⟩, []⟩]
   privates := ⟨[("params", 17), ("run", 18)],
     [(1, [(17, .data (.function 0)), (18, .method (.function 1))]),
      (2, [(17, .data .null), (18, .method (.function 1))])]⟩}

private def run (source : String) (state : State := before) (allowThis : Bool := false) :
    Option (Except EvalError (Value × State)) :=
  (parseAssignment source ["node", "replacement", "receivers", "bad"] ["params", "run"] allowThis).map
    (fun assignment => executeAssignment 32 defaultSplitLimit assignment state)

example : (parseAssignment "this.#params = replacement" ["replacement"] ["params"]).isNone = true := by cbv
example : (parseAssignment "this.#params = replacement" ["replacement"] ["params"] true).isSome = true := by cbv
example : (parseBlock "this.#params = replacement" ["replacement"] ["params"] true).isSome = true := by cbv
example : (parseAssignment "node.#unknown = replacement" ["node", "replacement"] ["params"]).isNone = true := by cbv
example : (parsePrivateFields "#field = this" []).isNone = true := by cbv
example : (parseNoArg "export const f = () => this").isNone = true := by cbv

/-- DATA is writable even when its old value is a function; METHOD is not.
The kind comes from the stored tag, never a value-shape guess. -/
theorem data_function_and_method_are_different :
    (run "node.#params = replacement").map (fun result => result.map Prod.fst) =
      some (.ok (.number 7)) ∧
    run "node.#run = replacement" = some (.error .privateReadOnly) := by cbv

/-- The universal independent write contract has a concrete allocated domain,
including genuine stored function handles and a nonextensible owner. -/
theorem data_write_has_nonempty_contract :
    ∃ after, privateSet (.object 1) 17 (.number 7) before = .ok after ∧
      PrivateWriteContract before after 1 17 (.number 7) :=
  privateSet_satisfies before 1 17 (.number 7) (.function 0)
    {prototype := some 0, extensible := false}
    [(17, .data (.function 0)), (18, .method (.function 1))] rfl rfl rfl

/-- No public property/prototype/extensibility dispatch occurs. The existing
ordinary heap is identical after the successful private write. -/
theorem nonextensible_owner_and_public_frames :
    (run "node.#params = replacement").map (fun result => result.map (fun (_, state) =>
      (state.objects, state.heap, state.thisValue,
       privateGet (.object 1) "params" state,
       state.privates.elements.lookup 1))) =
      some (.ok (before.objects, before.heap, before.thisValue, .ok (.number 7),
        some [(17, .data (.number 7)), (18, .method (.function 1))])) := by cbv

/-- The first shift captures the destination before the second shift produces
the assigned value. Re-reading the base after RHS effects would pick owner2. -/
theorem receiver_captured_before_rhs_effects :
    (run "receivers.shift().#params = receivers.shift()").map
      (fun result => result.map (fun (value, state) =>
        (value, state.heap, privateGet (.object 1) "params" state,
          privateGet (.object 2) "params" state))) =
      some (.ok (.object 2, [[]], .ok (.object 2), .ok .null)) := by cbv

/-- Reference evaluation saves the identity, not the spelling to resolve in a
later scope. The subsequent PutValue ignores the changed lexical map. -/
theorem resolved_identity_is_retained :
    putAssignmentReference (.privateField (.object 1) 17) (.number 7)
      {before with privates := {before.privates with names := [("params", 99)]}} =
      .ok (writePrivateDataState
        {before with privates := {before.privates with names := [("params", 99)]}} 1 17 (.number 7)) := by cbv

/-- RHS rejection wins over a later method/brand rejection. Except records the
error priority; it does not expose the failed execution's partial heap trace. -/
theorem rhs_errors_precede_private_put_rejection :
    run "node.#run = bad.value" = some (.error (.objectError .invalidReference)) ∧
    run "node.#params = bad.value" {before with environment := [("node", .null), ("bad", .object 99)]} =
      some (.error (.objectError .invalidReference)) ∧
    run "node.#params = replacement" {before with environment := [("node", .null), ("replacement", .number 7)]} =
      some (.error .privateBrand) := by cbv

private def method : PrivateMethod :=
  ⟨"self", [], .named "void", [.ret .this]⟩
private def thisClosure : PrivateMethodClosure :=
  ⟨method, [("this", .number 99)], []⟩
private def caller : State :=
  {before with thisValue := .boolean false, environment := [("this", .number 42)]}

example : parsePrivateMethod "#self(): void { return this }" [] [] = some method := by cbv

/-- this is a dynamic receiver, not a spoofable ordinary lexical variable. The
caller's separate this value and ordinary binding are both restored. -/
theorem method_this_and_caller_restore :
    (invokePrivateClosure 16 defaultSplitLimit thisClosure (.object 1) [] caller).map
      (fun (value, state) => (value, state.thisValue, state.environment)) =
      .ok (.object 1, .boolean false, [("this", .number 42)]) := by cbv

private def setter : PrivateMethod :=
  ⟨"set", [⟨"replacement", false, .named "T"⟩], .named "void",
    [.assign ⟨.privateProperty .this "params", .variable "replacement"⟩]⟩

example : parsePrivateMethod "#set(replacement: T): void { this.#params = replacement }" [] ["params"] =
    some setter := by cbv

theorem parsed_method_body_private_assignment :
    (invokePrivateClosure 32 defaultSplitLimit ⟨setter, [], [("params", 17)]⟩
      (.object 1) [.number 7] caller).map (fun (value, state) =>
        (value, state.thisValue, state.environment,
          state.privates.elements.lookup 1, state.privates.names)) =
      .ok (.undefined, caller.thisValue, caller.environment,
        some [(17, .data (.number 7)), (18, .method (.function 1))], caller.privates.names) := by cbv

end HonoLean.Upstream.SourceSubset.PrivateWriteChecks
