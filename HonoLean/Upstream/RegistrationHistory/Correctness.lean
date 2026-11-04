import HonoLean.Upstream.RegistrationHistory.Facts

namespace HonoLean.Upstream.RegistrationHistory

open SourceSubset ECMA2025

set_option maxRecDepth 32768

/-- Each actual source push is executed under entry facts derived from the
initial Seed and preceding source storage. No future successful push is assumed. -/
theorem run_source_history (before : State) (owner stamp methods : Nat) (order : Int)
    (prior : List Value) (requests : List Request)
    (seed : Seed before owner stamp methods order prior) :
    runSourceHistory NodeMethodsPush.expression owner requests before = .ok (endState before owner methods order prior requests) := by
  induction requests generalizing before order prior with
  | nil => rfl
  | cons request rest ih =>
    rw [runSourceHistory]
    rw [NodeMethodsPush.run_push (stage before owner request) request.method request.handler before.sets.length
      request.keys order owner stamp methods prior (stage_inputs before owner stamp methods order prior request seed)]
    simp only [bind, Except.bind]
    exact ih _ _ _ (step_seed before owner stamp methods order prior request seed)

theorem run_parsed_history (before : State) (owner stamp methods : Nat) (order : Int)
    (prior : List Value) (requests : List Request)
    (seed : Seed before owner stamp methods order prior) :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => runSourceHistory source owner requests before) =
        some (.ok (endState before owner methods order prior requests)) := by
  rw [NodeMethodsPush.parses_pinned_source, Option.map_some,
    run_source_history before owner stamp methods order prior requests seed]

theorem history_contract (before : State) (owner stamp methods : Nat) (order : Int)
    (prior : List Value) (requests : List Request) (seed : Seed before owner stamp methods order prior) :
    HistoryContract before (endState before owner methods order prior requests) methods order prior requests :=
  ⟨end_objects before owner methods order prior requests,
   end_heap before owner stamp methods order prior requests seed,
   end_sets before owner methods order prior requests,
   end_functions before owner methods order prior requests,
   end_privates before owner methods order prior requests,
   end_order before owner stamp methods order prior requests seed⟩

/-- Constructive exact-source history with independent structural storage,
snapshot, reference order, carried score and old-cell frame observations. -/
theorem parsed_history_satisfies (before : State) (owner stamp methods : Nat) (order : Int)
    (prior : List Value) (requests : List Request) (seed : Seed before owner stamp methods order prior) :
    ∃ after, (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
        (fun source => runSourceHistory source owner requests before) = some (.ok after) ∧
      HistoryContract before after methods order prior requests :=
  ⟨endState before owner methods order prior requests,
   run_parsed_history before owner stamp methods order prior requests seed,
   history_contract before owner stamp methods order prior requests seed⟩

/-- info: 'HonoLean.Upstream.RegistrationHistory.parsed_history_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_history_satisfies

end HonoLean.Upstream.RegistrationHistory
