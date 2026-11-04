import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SearchEntry.Generated
import HonoLean.Upstream.SearchEntry.Contract

namespace HonoLean.Upstream.SearchEntry

open SourceSubset ECMA2025

def handlerType : TypeSyntax := .application (.named "HandlerParamsSet") [.named "T"]
def collectorProgram : List Stmt :=
  [.typedDeclare "handlerSets" (.array handlerType) (.arrayLiteral [])]

set_option maxRecDepth 32768 in
theorem parses_collector : parseBlock pinnedCollectorSource [] = some collectorProgram := by cbv

/-- Actual typed local declaration, in its fresh declaration scope. All type
metadata is retained by the parser; it supplies no native runtime shape check. -/
theorem run_collector (before : State) :
    execute 32 defaultSplitLimit collectorProgram
      {before with environment := withoutBindings before.environment ["handlerSets"]} =
        .ok (.normal (collectorState before)) := by
  simp [collectorProgram, execute, evalExpression, evalLiteralElements, collectorState, boundState,
    bind, pure, Except.bind, Except.pure]

theorem parsed_collector_correct (before after : State) :
    (parseBlock pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {before with environment := withoutBindings before.environment ["handlerSets"]}) =
        some (.ok (.normal after)) ↔ CollectorContract before after := by
  rw [parses_collector, Option.map_some, run_collector]
  simp [CollectorContract, eq_comm]

theorem parsed_collector_satisfies (before : State) :
    ∃ after,
      (parseBlock pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
        {before with environment := withoutBindings before.environment ["handlerSets"]}) = some (.ok (.normal after)) ∧
      CollectorContract before after := by
  refine ⟨collectorState before, ?_, rfl, by simp⟩
  rw [parses_collector, Option.map_some, run_collector]

end HonoLean.Upstream.SearchEntry
