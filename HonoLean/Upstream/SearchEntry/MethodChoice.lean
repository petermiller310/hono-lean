import HonoLean.Upstream.SearchEntry.Collector

namespace HonoLean.Upstream.SearchEntry

open SourceSubset ECMA2025

def selectionExpression : Expr := .typeAssertion
  (.logicalOr (.index (.variable "m") (.variable "method"))
    (.index (.variable "m") (.variable "METHOD_NAME_ALL"))) handlerType
def selectionProgram : List Stmt := [.declare "handlerSet" selectionExpression]
def selectionBindings : List String := ["m", "method", "METHOD_NAME_ALL"]
def allExpression : Expr := .typeAssertion (.string allKey) .constAssertion

set_option maxRecDepth 32768 in
theorem parses_selection : parseBlock pinnedSelectionSource selectionBindings = some selectionProgram := by cbv
set_option maxRecDepth 32768 in
theorem parses_all : parseExpression pinnedAllSource [] = some allExpression := by cbv

/-- This derives the initializer's actual string; module export/import identity
is an explicit separate handoff, not supplied by parser type metadata. -/
theorem parsed_all_value (before : State) :
    (parseExpression pinnedAllSource []).map (fun source => evalExpression 32 defaultSplitLimit source before) =
      some (.ok (.string allKey, before)) := by
  rw [parses_all]
  simp [allExpression, evalExpression, pure, Except.pure]

structure ChoiceBindings (before : State) (row : ObjectRef) (method : JSString) : Prop where
  rowBinding : before.environment.lookup "m" = some (.object row)
  methodBinding : before.environment.lookup "method" = some (.string method)

theorem run_choice_direct (before : State) (row : ObjectRef) (method : JSString) (direct : Value)
    (bindings : ChoiceBindings before row method)
    (read : getProperty propertyFuel before.objects row method = .ok direct)
    (truth : NodeParamAssignment.Truthy direct) :
    execute 32 defaultSplitLimit selectionProgram
      {before with environment := withoutBindings before.environment ["handlerSet"]} =
        .ok (.normal (boundState before "handlerSet" direct)) := by
  have rowBinding := lookup_withoutBindings before.environment ["handlerSet"] "m" (by decide)
  have methodBinding := lookup_withoutBindings before.environment ["handlerSet"] "method" (by decide)
  have truthValue := (NodeParamAssignment.truthy_iff direct).mpr truth
  simp [selectionProgram, selectionExpression, execute, evalExpression, lookupVariable,
    rowBinding, methodBinding, bindings.rowBinding, bindings.methodBinding, readProperty, read,
    truthValue, boundState, Except.mapError, bind, pure, Except.bind, Except.pure, -truthy]

theorem run_choice_fallback (before : State) (row : ObjectRef) (method fallbackKey : JSString) (direct fallback : Value)
    (bindings : ChoiceBindings before row method)
    (read : getProperty propertyFuel before.objects row method = .ok direct)
    (falsy : ¬ NodeParamAssignment.Truthy direct)
    (allBinding : before.environment.lookup "METHOD_NAME_ALL" = some (.string fallbackKey))
    (fallbackRead : getProperty propertyFuel before.objects row fallbackKey = .ok fallback) :
    execute 32 defaultSplitLimit selectionProgram
      {before with environment := withoutBindings before.environment ["handlerSet"]} =
        .ok (.normal (boundState before "handlerSet" fallback)) := by
  have rowBinding := lookup_withoutBindings before.environment ["handlerSet"] "m" (by decide)
  have methodBinding := lookup_withoutBindings before.environment ["handlerSet"] "method" (by decide)
  have imported := lookup_withoutBindings before.environment ["handlerSet"] "METHOD_NAME_ALL" (by decide)
  have truthValue : truthy direct = false := by
    cases observed : truthy direct
    · rfl
    · exact False.elim (falsy ((NodeParamAssignment.truthy_iff direct).mp observed))
  simp [selectionProgram, selectionExpression, execute, evalExpression, lookupVariable,
    rowBinding, methodBinding, imported, bindings.rowBinding, bindings.methodBinding, readProperty,
    read, allBinding, fallbackRead, truthValue, boundState, Except.mapError,
    bind, pure, Except.bind, Except.pure, -truthy]

theorem run_choice (before : State) (row : ObjectRef) (method : JSString) (chosen : Value)
    (bindings : ChoiceBindings before row method) (choice : Choice before row method chosen) :
    execute 32 defaultSplitLimit selectionProgram
      {before with environment := withoutBindings before.environment ["handlerSet"]} =
        .ok (.normal (boundState before "handlerSet" chosen)) := by
  obtain ⟨direct, read, cases⟩ := choice
  rcases cases with ⟨truth, rfl⟩ | ⟨falsy, key, imported, rightRead⟩
  · exact run_choice_direct before row method chosen bindings read truth
  · exact run_choice_fallback before row method key direct chosen bindings read falsy imported rightRead

theorem parsed_choice_satisfies (before : State) (row : ObjectRef) (method : JSString)
    (bindings : ChoiceBindings before row method) (domain : ChoiceDomain before row method) :
    ∃ chosen after,
      (parseBlock pinnedSelectionSource selectionBindings).map (fun source => execute 32 defaultSplitLimit source
        {before with environment := withoutBindings before.environment ["handlerSet"]}) = some (.ok (.normal after)) ∧
      ChoiceContract before after row method chosen := by
  obtain ⟨direct, read, fallback⟩ := domain
  have inhabited : ∃ chosen, Choice before row method chosen := by
    by_cases truth : truthy direct = true
    · exact ⟨direct, direct, read, Or.inl ⟨(NodeParamAssignment.truthy_iff direct).mp truth, rfl⟩⟩
    · have falsy : ¬ NodeParamAssignment.Truthy direct := fun h => truth ((NodeParamAssignment.truthy_iff direct).mpr h)
      obtain ⟨key, chosen, imported, rightRead⟩ := fallback falsy
      exact ⟨chosen, direct, read, Or.inr ⟨falsy, key, imported, rightRead⟩⟩
  obtain ⟨chosen, choice⟩ := inhabited
  refine ⟨chosen, boundState before "handlerSet" chosen, ?_, choice, rfl⟩
  rw [parses_selection, Option.map_some, run_choice before row method chosen bindings choice]

theorem parsed_choice_correct (before after : State) (row : ObjectRef) (method : JSString)
    (bindings : ChoiceBindings before row method) (domain : ChoiceDomain before row method) :
    (parseBlock pinnedSelectionSource selectionBindings).map (fun source => execute 32 defaultSplitLimit source
      {before with environment := withoutBindings before.environment ["handlerSet"]}) = some (.ok (.normal after)) ↔
        ∃ chosen, ChoiceContract before after row method chosen := by
  constructor
  · intro observed
    obtain ⟨chosen, completed, execution, contract⟩ := parsed_choice_satisfies before row method bindings domain
    rw [execution] at observed
    simp only [Option.some.injEq, Except.ok.injEq, Completion.normal.injEq] at observed
    exact ⟨chosen, observed ▸ contract⟩
  · rintro ⟨chosen, choice, equal⟩
    rw [equal, parses_selection, Option.map_some, run_choice before row method chosen bindings choice]

/-- Specialization to the actual source-derived ALL string, with import/value
correspondence and the ordinary inherited read required only if it is reached.
Even an ALL registration need not win against a truthy inherited direct value. -/
theorem parsed_choice_from_all_satisfies (before : State) (row : ObjectRef) (method : JSString) (direct : Value)
    (bindings : ChoiceBindings before row method)
    (read : getProperty propertyFuel before.objects row method = .ok direct)
    (fallback : ¬ NodeParamAssignment.Truthy direct → AllImportBinding before ∧
      ∃ chosen, getProperty propertyFuel before.objects row allKey = .ok chosen) :
    ∃ chosen after,
      (parseBlock pinnedSelectionSource selectionBindings).map (fun source => execute 32 defaultSplitLimit source
        {before with environment := withoutBindings before.environment ["handlerSet"]}) = some (.ok (.normal after)) ∧
      ChoiceContract before after row method chosen := by
  apply parsed_choice_satisfies before row method bindings
  refine ⟨direct, read, ?_⟩
  intro falsy
  obtain ⟨imported, chosen, rightRead⟩ := fallback falsy
  exact ⟨allKey, chosen, imported, rightRead⟩

/-- info: 'HonoLean.Upstream.SearchEntry.parsed_choice_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_choice_correct

end HonoLean.Upstream.SearchEntry
