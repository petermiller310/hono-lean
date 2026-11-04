import HonoLean.Upstream.MethodsLoopRegistration.Layout
import HonoLean.Upstream.MethodsLoopInitial.Correctness

namespace HonoLean.Upstream.MethodsLoopRegistration

open SourceSubset ECMA2025

/-- Actual registration and actual later collector creation feed the complete
source loop through an initial-state layout whose storage facts were derived.
Only caller/helper/import/old-read/realm context remains external. Insertion
event production, class initialization, native calls and intervening traversal
are not proved by this noncontiguous activation handoff. -/
theorem parsed_pipeline_satisfies (events : List JSString) (before : State) (method query : JSString) (handler : Value)
    (reference : Nat) (order : Int) (owner stamp methods : Nat)
    (searchEnvironment context : List (String × Value)) (parameterReceiver : Value) (nodeParams : Nat)
    (snapshot : NodeParamLoop.Snapshot)
    (inputs : NodeMethodsPush.Inputs before method handler reference snapshot.keys order owner stamp methods [])
    (trace : NodeKeySet.TraceContract events reference before)
    (domain : Context before context owner query parameterReceiver nodeParams snapshot)
    (queryDomain : QueryDomain before method query) :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source before) =
        some (.ok (.number 1, registered before method handler snapshot.keys order methods)) ∧
    (parseBlock SearchEntry.pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {SearchEntry.searchActivation (registered before method handler snapshot.keys order methods) searchEnvironment with
        environment := withoutBindings searchEnvironment ["handlerSets"]}) =
      some (.ok (.normal (SearchEntry.collectorState
        (SearchEntry.searchActivation (registered before method handler snapshot.keys order methods) searchEnvironment)))) ∧
    ∃ after,
      (parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"]).map
        (fun source => runBlock ((rows before).length + snapshot.keys.length + 103) source
          (activation before method handler snapshot.keys order methods searchEnvironment context)) = some (.ok (.normal after)) ∧
      MethodsLoop.LoopContract (activation before method handler snapshot.keys order methods searchEnvironment context)
        after (rows before) query (before.heap.length + 1) := by
  refine ⟨registration_execution before method handler reference snapshot.keys order owner stamp methods inputs,
    collector_execution before method handler snapshot.keys order methods searchEnvironment, ?_⟩
  exact MethodsLoopInitial.parsed_initial_satisfies owner stamp methods
    (loop_inputs before method query handler reference snapshot.keys order owner stamp methods searchEnvironment context
      inputs domain.ownerBinding domain.queryBinding)
    (initial_layout events before method query handler reference order owner stamp methods searchEnvironment context
      parameterReceiver nodeParams snapshot inputs trace domain queryDomain)

/-- info: 'HonoLean.Upstream.MethodsLoopRegistration.parsed_pipeline_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_pipeline_satisfies

end HonoLean.Upstream.MethodsLoopRegistration
