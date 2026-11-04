import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Generated
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset

def splitPathProgram : Function :=
  ⟨"splitPath", "path", [
    .declare "paths" (.call (.variable "path") "split" [.string [47]]),
    .branch (.strictEqual (.index (.variable "paths") (.number 0)) (.string []))
      [.evaluate (.call (.variable "paths") "shift" [])],
    .ret (.variable "paths")]⟩

set_option maxRecDepth 32768 in
/-- The embedded bytes are parsed by Lean, including the actual declaration,
identifiers, annotations, condition, mutation, and return. -/
theorem parses_pinned_source : parse pinnedSource = some splitPathProgram := by cbv

def dropLeadingEmpty : List JSString → List JSString
  | [] :: remaining => remaining
  | other => other

/-- A delimiter partition is nonempty, rejoins to the entire input, and has no
delimiter inside any field. Empty and trailing fields are deliberately allowed. -/
def SlashPartition (input : JSString) (fields : List JSString) : Prop :=
  fields ≠ [] ∧ [47].intercalate fields = input ∧ ∀ field ∈ fields, (47 : UInt16) ∉ field

/-- The observable contract first applies the split limit, then removes a
single leading empty field. This definition never runs a parser/interpreter. -/
def SplitPathContract (limit : Nat) (input : JSString) (output : List JSString) : Prop :=
  ∃ fields, SlashPartition input fields ∧ output = dropLeadingEmpty (fields.take limit)

private theorem split_fields_clean (input : JSString) :
    ∀ field ∈ input.splitOn (47 : UInt16), (47 : UInt16) ∉ field := by
  induction input with
  | nil => simp
  | cons c rest ih =>
    by_cases same : c = 47
    · subst c
      simpa [List.splitOn_cons_eq_ite_modifyHead] using ih
    · have nonempty := List.splitOn_ne_nil (47 : UInt16) rest
      cases parts : rest.splitOn (47 : UInt16) with
      | nil => exact False.elim (nonempty parts)
      | cons first remaining =>
        simp only [parts, List.mem_cons, forall_eq_or_imp] at ih
        simp only [List.splitOn_cons_eq_ite_modifyHead, show (c == (47 : UInt16)) = false by simp [same], Bool.false_eq_true, ↓reduceIte, parts, List.modifyHead_cons, List.mem_cons, forall_eq_or_imp]
        exact ⟨fun member => member.elim (Ne.symm same) ih.1, ih.2⟩

theorem split_partition (input : JSString) :
    SlashPartition input (input.splitOn (47 : UInt16)) :=
  ⟨List.splitOn_ne_nil _ _, List.intercalate_splitOn _, split_fields_clean input⟩

theorem partition_unique {input : JSString} {fields : List JSString}
    (partition : SlashPartition input fields) : fields = input.splitOn (47 : UInt16) := by
  have rejoin := List.splitOn_intercalate (47 : UInt16) partition.2.2 partition.1
  rw [partition.2.1] at rejoin
  exact rejoin.symm

theorem contract_iff (limit : Nat) (input : JSString) (output : List JSString) :
    SplitPathContract limit input output ↔
      output = dropLeadingEmpty ((input.splitOn (47 : UInt16)).take limit) := by
  constructor
  · rintro ⟨fields, partition, rfl⟩
    rw [partition_unique partition]
  · intro equal
    exact ⟨_, split_partition input, equal⟩

theorem run_splitPath (input : JSString) (limit : Nat) :
    run splitPathProgram input limit =
      .ok ((dropLeadingEmpty ((input.splitOn (47 : UInt16)).take limit)).map Value.string) := by
  generalize parts : (input.splitOn (47 : UInt16)).take limit = fields
  cases fields with
  | nil =>
    simp [run, splitPathProgram, execute, evalExpression, evalArguments, intrinsic,
      lookupVariable, bind, pure, Except.bind, Except.pure, parts, dropLeadingEmpty, -List.map_take]
  | cons first remaining =>
    cases first with
    | nil =>
      simp [run, splitPathProgram, execute, evalExpression, evalArguments, intrinsic,
        lookupVariable, bind, pure, Except.bind, Except.pure, parts, dropLeadingEmpty, -List.map_take]
    | cons unit tail =>
      simp [run, splitPathProgram, execute, evalExpression, evalArguments, intrinsic,
        lookupVariable, bind, pure, Except.bind, Except.pure, parts, dropLeadingEmpty, -List.map_take]

/-- Actual parsed source, not just a hand-constructed AST, satisfies the
independent contract in the declared single-code-unit intrinsic semantics. -/
theorem parsed_source_correct (input : JSString) (output : List JSString) :
    (parse pinnedSource).map (fun program => run program input defaultSplitLimit) =
      some (.ok (output.map Value.string)) ↔
        SplitPathContract defaultSplitLimit input output := by
  rw [parses_pinned_source, Option.map_some, run_splitPath, contract_iff]
  simp only [Option.some.injEq, Except.ok.injEq]
  rw [List.map_inj_right (fun _ _ equal => Value.string.inj equal)]
  exact eq_comm

/-- info: 'HonoLean.Upstream.SourceSubset.parsed_source_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_correct

end HonoLean.Upstream.SourceSubset
