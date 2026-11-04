import HonoLean.Upstream.NodeInitialization.Freshness
import HonoLean.Upstream.RegistrationHistoryLoop.Correctness

namespace HonoLean.Upstream.NodeInitialization

open SourceSubset ECMA2025

def initializedState (before : State) (prototype : Option Nat) : State :=
  classActivation (instanceState (preambleState before) prototype (preambleState before).environment
    (initialNodeWorld before).nextIdentity (.object before.objects.length)) (initialNodeWorld before).nextIdentity

def initializedOwner (before : State) : Nat := (preambleState before).objects.length

theorem canonical_initialized_seed (before : State) (prototype : Option Nat)
    (rootFound : ∃ root, before.objects[0]? = some root) :
    RegistrationHistory.Seed (initializedState before prototype) (initializedOwner before)
      (initialNodeWorld before).nextIdentity before.heap.length 0 [] :=
  initialized_seed before _ prototype (initialNodeWorld before).nextIdentity (initializedOwner before) rootFound
    (instance_contract (preambleState before) prototype (preambleState before).environment
      (initialNodeWorld before).nextIdentity (.object before.objects.length))

/-- The source preamble and selected private DATA field initialization produce
the Seed used by arbitrary source-push histories and the full capture loop.
Remaining Context concerns reads/caller/helper/import/realm state, not desired
registration output, selected handlers or future validity. Class construction,
private methods, actual calls and insertion event production remain open. -/
theorem parsed_initialized_pipeline (before : State) (prototype : Option Nat)
    (requests : List RegistrationHistory.Request) (searchEnvironment context : List (String × Value))
    (query : JSString) (parameterReceiver : Value) (nodeParams keyBound : Nat)
    (parameter node : JSString → Value)
    (helper : HelperBinding before)
    (rootFound : ∃ root, before.objects[0]? = some root)
    (fresh : (preambleState before).privates.slots.lookup (preambleState before).objects.length = none)
    (prototypeReady : PrototypeReady (preambleState before) prototype)
    (domain : RegistrationHistoryLoop.Context (initializedState before prototype) requests context
      (initializedOwner before) query parameterReceiver nodeParams keyBound parameter node) :
    (parseBlock pinnedPreambleSource ["createNullObject"]).map
      (fun source => execute 32 defaultSplitLimit source (preambleEntry before)) =
        some (.ok (.normal (preambleState before))) ∧
    (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).map
      (fun fields => instantiateDataClass 64 defaultSplitLimit
        ⟨fields, (initialNodeWorld before).nextIdentity, (preambleState before).environment⟩ prototype (preambleState before)) =
          some (.ok (initializedOwner before,
            instanceState (preambleState before) prototype (preambleState before).environment
              (initialNodeWorld before).nextIdentity (.object before.objects.length))) ∧
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => RegistrationHistory.runSourceHistory source (initializedOwner before) requests (initializedState before prototype)) =
        some (.ok (RegistrationHistory.endState (initializedState before prototype) (initializedOwner before)
          before.heap.length 0 [] requests)) ∧
    ∃ after,
      (parseBlock MethodsLoop.pinnedSource MethodsLoop.bindings ["methods"]).map
        (fun source => runBlock (requests.length + keyBound + 103) source
          (RegistrationHistoryLoop.activation
            (RegistrationHistory.endState (initializedState before prototype) (initializedOwner before)
              before.heap.length 0 [] requests) searchEnvironment context)) = some (.ok (.normal after)) ∧
      MethodsLoop.LoopContract
        (RegistrationHistoryLoop.activation
          (RegistrationHistory.endState (initializedState before prototype) (initializedOwner before)
            before.heap.length 0 [] requests) searchEnvironment context)
        after (RegistrationHistory.storedRows (initializedState before prototype).objects.length requests) query
        (RegistrationHistory.endState (initializedState before prototype) (initializedOwner before)
          before.heap.length 0 [] requests).heap.length := by
  refine ⟨?_, ?_, ?_⟩
  · rw [parses_preamble, Option.map_some, run_preamble before helper]
  · rw [parses_fields, Option.map_some]
    exact congrArg some (instantiate_node (preambleState before) prototype (preambleState before).environment
      (initialNodeWorld before).nextIdentity (.object before.objects.length) fresh prototypeReady
      (preamble_initializer_bindings before helper))
  · obtain ⟨registration, _, loop⟩ := RegistrationHistoryLoop.parsed_pipeline_satisfies
      (initializedState before prototype) (initializedOwner before) (initialNodeWorld before).nextIdentity
      before.heap.length 0 requests searchEnvironment context query parameterReceiver nodeParams keyBound parameter node
      (canonical_initialized_seed before prototype rootFound) domain
    exact ⟨registration, loop⟩

/-- info: 'HonoLean.Upstream.NodeInitialization.parsed_initialized_pipeline' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parsed_initialized_pipeline

end HonoLean.Upstream.NodeInitialization
