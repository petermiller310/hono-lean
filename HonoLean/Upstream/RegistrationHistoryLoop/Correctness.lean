import HonoLean.Upstream.RegistrationHistoryLoop.Layout
import HonoLean.Upstream.RegistrationHistory.Correctness

namespace HonoLean.Upstream.RegistrationHistoryLoop

open SourceSubset ECMA2025 RegistrationHistory

theorem loop_inputs (before registered : State) (owner stamp methods : Nat) (order : Int)
    (requests : List Request) (searchEnvironment context : List (String × Value)) (query : JSString)
    (seed : Seed before owner stamp methods order [])
    (contract : HistoryContract before registered methods order [] requests)
    (nodeBinding : context.lookup "node" = some (.object owner))
    (methodBinding : context.lookup "method" = some (.string query))
    (capacity : requests.length ≤ 4294967295) :
    MethodsLoop.Inputs (activation registered searchEnvironment context) owner stamp methods registered.heap.length
      (storedRows before.objects.length requests) query := by
  refine ⟨?_, ?_, ?_, ?_, ?_, methods_found contract ⟨[], seed.methodsFound⟩, ?_, ?_⟩
  · rw [activation_lookup _ _ _ _ (by decide)]
    exact nodeBinding
  · rw [activation_lookup _ _ _ _ (by decide)]
    exact methodBinding
  · obtain ⟨object, found⟩ := seed.ownerFound
    refine ⟨object, ?_⟩
    rw [objects_equal contract, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  · change registered.privates.names.lookup "methods" = _
    rw [contract.privates]
    exact seed.privateName
  · change ∃ fields, registered.privates.slots.lookup owner = some fields ∧ fields.lookup stamp = some (.array methods)
    rw [contract.privates]
    exact seed.privateSlot
  · have bound := (List.getElem?_eq_some_iff.mp seed.methodsFound).1
    rw [heap_length contract]
    omega
  · simpa [stored_rows_length] using capacity

theorem collector_execution (registered : State) (searchEnvironment : List (String × Value)) :
    (parseBlock SearchEntry.pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {SearchEntry.searchActivation registered searchEnvironment with
        environment := withoutBindings searchEnvironment ["handlerSets"]}) =
      some (.ok (.normal (SearchEntry.collectorState (SearchEntry.searchActivation registered searchEnvironment)))) := by
  rw [SearchEntry.parses_collector, Option.map_some]
  exact congrArg some (SearchEntry.run_collector (SearchEntry.searchActivation registered searchEnvironment))

/-- Arbitrary actual source registration histories construct the protected
initial Layout, rather than requiring the completed storage or future loop
readiness as an assumption. The old Context supplies only caller/read/realm
facts and per-request inherited-query conditions. -/
theorem parsed_history_layout (before : State) (owner stamp methods : Nat) (order : Int)
    (requests : List Request) (searchEnvironment context : List (String × Value))
    (query : JSString) (parameterReceiver : Value) (nodeParams keyBound : Nat)
    (parameter node : JSString → Value)
    (seed : Seed before owner stamp methods order [])
    (domain : Context before requests context owner query parameterReceiver nodeParams keyBound parameter node) :
    MethodsLoopInitial.Layout
      (activation (endState before owner methods order [] requests) searchEnvironment context)
      (storedRows before.objects.length requests) query
      (endState before owner methods order [] requests).heap.length keyBound
      (storedRecords before.objects.length before.heap.length order requests parameter node)
      parameterReceiver nodeParams [] := by
  obtain ⟨root, found⟩ := seed.rootFound
  exact initial_layout (history_contract before owner stamp methods order [] requests seed)
    (List.getElem?_eq_some_iff.mp found).1 owner query parameterReceiver nodeParams keyBound parameter node domain

/-- Each push is the parsed pinned source under its explicit caller activation;
the later typed collector also executes. Their derived initial Layout then
feeds the complete parsed methods loop. Class installation, event production,
module/native-call linking and intervening traversal remain separate obligations. -/
theorem parsed_pipeline_satisfies (before : State) (owner stamp methods : Nat) (order : Int)
    (requests : List Request) (searchEnvironment context : List (String × Value))
    (query : JSString) (parameterReceiver : Value) (nodeParams keyBound : Nat)
    (parameter node : JSString → Value)
    (seed : Seed before owner stamp methods order [])
    (domain : Context before requests context owner query parameterReceiver nodeParams keyBound parameter node) :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => runSourceHistory source owner requests before) =
        some (.ok (endState before owner methods order [] requests)) ∧
    (parseBlock SearchEntry.pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {SearchEntry.searchActivation (endState before owner methods order [] requests) searchEnvironment with
        environment := withoutBindings searchEnvironment ["handlerSets"]}) =
      some (.ok (.normal (SearchEntry.collectorState
        (SearchEntry.searchActivation (endState before owner methods order [] requests) searchEnvironment)))) ∧
    ∃ after,
      (parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"]).map
        (fun source => runBlock (requests.length + keyBound + 103) source
          (activation (endState before owner methods order [] requests) searchEnvironment context)) = some (.ok (.normal after)) ∧
      MethodsLoop.LoopContract (activation (endState before owner methods order [] requests) searchEnvironment context)
        after (storedRows before.objects.length requests) query
        (endState before owner methods order [] requests).heap.length := by
  refine ⟨run_parsed_history before owner stamp methods order [] requests seed,
    collector_execution _ _, ?_⟩
  have layout := parsed_history_layout before owner stamp methods order requests searchEnvironment context query
    parameterReceiver nodeParams keyBound parameter node seed domain
  have inputs := loop_inputs before _ owner stamp methods order requests searchEnvironment context query seed
    (history_contract before owner stamp methods order [] requests seed) domain.ownerBinding domain.queryBinding domain.capacity
  simpa [stored_rows_length] using MethodsLoopInitial.parsed_initial_satisfies owner stamp methods inputs layout

/-- info: 'HonoLean.Upstream.RegistrationHistoryLoop.parsed_pipeline_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_pipeline_satisfies

end HonoLean.Upstream.RegistrationHistoryLoop
