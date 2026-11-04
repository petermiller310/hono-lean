import HonoLean.Upstream.NodeInitialization.Generated
import HonoLean.Upstream.NodeParamLoop.Setup
import HonoLean.Upstream.SourceSubset.Parser

namespace HonoLean.Upstream.NodeInitialization

open SourceSubset ECMA2025

def preambleProgram : List Stmt :=
  [.declare "emptyParams" (.invoke (.variable "createNullObject") []),
   .mutableDeclare "order" none (.number 0)]

set_option maxRecDepth 32768 in
theorem parses_preamble : parseBlock pinnedPreambleSource ["createNullObject"] = some preambleProgram := by cbv

/-- Imported helper identity/value context, not a proof of module linking or
native mutable lexical-cell semantics. Its parsed implementation is checked by
the separate CreateNullObject source theorem. -/
def HelperBinding (before : State) : Prop :=
  ∃ reference environment,
    before.environment.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩ ∧
    StandardObjectBinding {before with environment}

def preambleEntry (before : State) : State :=
  {before with environment := withoutBindings before.environment ["emptyParams", "order"]}

/-- Independent allocation/binding endpoint. The order value and shared empty
params address are produced by the actual declarations, not caller inputs. -/
def preambleState (before : State) : State :=
  {before with
    environment := [("order", .number 0), ("emptyParams", .object before.objects.length)] ++
      withoutBindings before.environment ["emptyParams", "order"]
    objects := before.objects ++ [emptyNullObject]}

def PreambleContract (before after : State) : Prop :=
  after = preambleState before ∧ before.objects[before.objects.length]? = none

theorem run_preamble (before : State) (helper : HelperBinding before) :
    execute 32 defaultSplitLimit preambleProgram (preambleEntry before) =
      .ok (.normal (preambleState before)) := by
  obtain ⟨reference, environment, binding, found, standard⟩ := helper
  have entryBinding : (preambleEntry before).environment.lookup "createNullObject" = some (.function reference) := by
    rw [preambleEntry, lookup_withoutBindings _ _ _ (by decide)]
    exact binding
  have called := NodeParamLoop.invoke_helper 23 defaultSplitLimit (preambleEntry before) reference environment
    entryBinding found standard
  change evalExpression 31 defaultSplitLimit (.invoke (.variable "createNullObject") []) (preambleEntry before) = _ at called
  simp only [preambleProgram, execute]
  rw [called]
  simp [evalExpression, preambleState, preambleEntry, bind, pure, Except.bind, Except.pure]

theorem parsed_preamble_satisfies (before : State) (helper : HelperBinding before) :
    ∃ after,
      (parseBlock pinnedPreambleSource ["createNullObject"]).map
        (fun source => execute 32 defaultSplitLimit source (preambleEntry before)) = some (.ok (.normal after)) ∧
      PreambleContract before after := by
  refine ⟨preambleState before, ?_, rfl, by simp⟩
  rw [parses_preamble, Option.map_some, run_preamble before helper]

theorem parsed_preamble_correct (before after : State) (helper : HelperBinding before) :
    (parseBlock pinnedPreambleSource ["createNullObject"]).map
      (fun source => execute 32 defaultSplitLimit source (preambleEntry before)) = some (.ok (.normal after)) ↔
    PreambleContract before after := by
  rw [parses_preamble, Option.map_some, run_preamble before helper]
  simp [PreambleContract, eq_comm]

theorem preamble_order (before : State) :
    (preambleState before).environment.lookup "order" = some (.number 0) := by simp [preambleState]

theorem preamble_empty_binding (before : State) :
    (preambleState before).environment.lookup "emptyParams" = some (.object before.objects.length) := by
  simp [preambleState, List.lookup]

theorem preamble_empty_cell (before : State) :
    (preambleState before).objects[before.objects.length]? = some emptyNullObject := by simp [preambleState]

theorem preamble_helper (before : State) (helper : HelperBinding before) : HelperBinding (preambleState before) := by
  obtain ⟨reference, environment, binding, found, standard⟩ := helper
  refine ⟨reference, environment, ?_, found, standard⟩
  have preserved := lookup_withoutBindings before.environment ["emptyParams", "order"] "createNullObject" (by decide)
  simpa [preambleState, List.lookup] using preserved.trans binding

/-- info: 'HonoLean.Upstream.NodeInitialization.parsed_preamble_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_preamble_correct

end HonoLean.Upstream.NodeInitialization
