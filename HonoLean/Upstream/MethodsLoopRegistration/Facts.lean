import HonoLean.Upstream.SearchEntry.Bridge
import HonoLean.Upstream.MethodsLoop.Correctness

namespace HonoLean.Upstream.MethodsLoopRegistration

open SourceSubset ECMA2025

/-- The endpoint of one actual registration into an empty private methods
array. No source-selected row or handler binding is staged here. -/
def registered (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) : State :=
  NodeMethodsPush.pushedState before method handler keys order methods []

/-- Explicit distinct search/helper activations with the actual later fresh
collector. Actual function calls, argument transport and intervening code are
not translated by this context handoff. -/
def activation (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) : State :=
  SearchEntry.pushActivation (registered before method handler keys order methods)
    searchEnvironment context

def rows (before : State) : List Value := [.object before.objects.length]

theorem registration_execution (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) (owner stamp methods : Nat)
    (inputs : NodeMethodsPush.Inputs before method handler reference keys order owner stamp methods []) :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source before) =
        some (.ok (.number 1, registered before method handler keys order methods)) := by
  rw [NodeMethodsPush.parses_pinned_source, Option.map_some,
    NodeMethodsPush.run_push before method handler reference keys order owner stamp methods [] inputs]
  rfl

theorem collector_execution (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment : List (String × Value)) :
    (parseBlock SearchEntry.pinnedCollectorSource []).map (fun source => execute 32 defaultSplitLimit source
      {SearchEntry.searchActivation (registered before method handler keys order methods) searchEnvironment with
        environment := withoutBindings searchEnvironment ["handlerSets"]}) =
      some (.ok (.normal (SearchEntry.collectorState
        (SearchEntry.searchActivation (registered before method handler keys order methods) searchEnvironment)))) := by
  rw [SearchEntry.parses_collector, Option.map_some]
  exact congrArg some (SearchEntry.run_collector
    (SearchEntry.searchActivation (registered before method handler keys order methods) searchEnvironment))

theorem activation_methods (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value))
    (found : before.heap[methods]? = some []) :
    (activation before method handler keys order methods searchEnvironment context).heap[methods]? = some (rows before) := by
  have stored := NodeMethodsPush.pushed_methods_found before method handler keys order methods [] found
  change (registered before method handler keys order methods).heap[methods]? = some (rows before) at stored
  change ((registered before method handler keys order methods).heap ++ [[]])[methods]? = _
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored).1]
  exact stored

theorem activation_collector (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) :
    (activation before method handler keys order methods searchEnvironment context).heap[before.heap.length + 1]? = some [] := by
  simp [activation, SearchEntry.pushActivation, SearchEntry.collectorState, SearchEntry.searchActivation, registered,
    NodeMethodsPush.pushedState, HandlerRecord.constructedState]

theorem activation_keys (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) :
    (activation before method handler keys order methods searchEnvironment context).heap[before.heap.length]? =
      some (keys.map Value.string) := by
  have stored := NodeMethodsPush.pushed_keys_found before method handler keys order methods []
  change (registered before method handler keys order methods).heap[before.heap.length]? = some (keys.map Value.string) at stored
  change ((registered before method handler keys order methods).heap ++ [[]])[before.heap.length]? = _
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored).1]
  exact stored

theorem activation_outer (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) :
    (activation before method handler keys order methods searchEnvironment context).objects[before.objects.length]? =
      some (HandlerRecord.outerRecord method (before.objects.length + 1)) :=
  NodeMethodsPush.pushed_outer_found before method handler keys order methods []

theorem activation_inner (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) :
    (activation before method handler keys order methods searchEnvironment context).objects[before.objects.length + 1]? =
      some (HandlerRecord.innerRecord handler before.heap.length (order + 1)) :=
  NodeMethodsPush.pushed_inner_found before method handler keys order methods []

/-- Actual source storage and later collector allocation derive the loop's
private/dense-array inputs. The query may differ from the registered method;
selection and fallback are left to the parsed loop. -/
theorem loop_inputs (before : State) (method query : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) (owner stamp methods : Nat)
    (searchEnvironment context : List (String × Value))
    (inputs : NodeMethodsPush.Inputs before method handler reference keys order owner stamp methods [])
    (nodeBinding : context.lookup "node" = some (.object owner))
    (methodBinding : context.lookup "method" = some (.string query)) :
    MethodsLoop.Inputs (activation before method handler keys order methods searchEnvironment context)
      owner stamp methods (before.heap.length + 1) (rows before) query := by
  refine ⟨?_, ?_, ?_, inputs.privateName, inputs.privateSlot,
    activation_methods before method handler keys order methods searchEnvironment context inputs.methodsFound,
    ?_, by simp [rows]⟩
  · rw [activation, SearchEntry.activation_lookup _ _ _ _ (by decide)]
    exact nodeBinding
  · rw [activation, SearchEntry.activation_lookup _ _ _ _ (by decide)]
    exact methodBinding
  · obtain ⟨object, found⟩ := inputs.ownerFound
    refine ⟨object, ?_⟩
    change (before.objects ++ [_, _])[owner]? = some object
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  · have inside := (List.getElem?_eq_some_iff.mp inputs.methodsFound).1
    omega

end HonoLean.Upstream.MethodsLoopRegistration
