import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.NodeMethodsPush.Generated
import HonoLean.Upstream.NodeMethodsPush.Contract
import HonoLean.Upstream.HandlerRecord.Correctness

namespace HonoLean.Upstream.NodeMethodsPush

open SourceSubset ECMA2025

def bindings : List String := ["curNode", "method", "handler", "possibleKeys", "order"]
def privateNames : List String := ["methods"]
def expression : Expr :=
  .call (.privateProperty (.variable "curNode") "methods") "push" [HandlerRecord.expression]

set_option maxRecDepth 32768 in
theorem parses_pinned_source : parseExpression pinnedSource bindings privateNames = some expression := by cbv

set_option maxRecDepth 32768 in
theorem parses_pinned_statement : parseBlock pinnedSource bindings privateNames = some [.evaluate expression] := by cbv

theorem eval_private_receiver (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) (owner stamp methods : Nat) (prior : List Value)
    (inputs : Inputs before method handler reference keys order owner stamp methods prior) :
    evalExpression 33 defaultSplitLimit (.privateProperty (.variable "curNode") "methods") before =
      .ok (.array methods, before) := by
  obtain ⟨object, ownerFound⟩ := inputs.ownerFound
  obtain ⟨fields, fieldsFound, slotFound⟩ := inputs.privateSlot
  simp [evalExpression, lookupVariable, inputs.ownerBinding, privateGet, inputs.privateName,
    ownerFound, fieldsFound, slotFound, bind, pure, Except.bind, Except.pure]

theorem run_push (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) (owner stamp methods : Nat) (prior : List Value)
    (inputs : Inputs before method handler reference keys order owner stamp methods prior) :
    evalExpression 34 defaultSplitLimit expression before =
      .ok (.number (Int.ofNat (prior.length + 1)), pushedState before method handler keys order methods prior) := by
  rw [expression, evalExpression]
  rw [eval_private_receiver before method handler reference keys order owner stamp methods prior inputs]
  simp only [bind, Except.bind, prepareMethod, inputs.methodsFound]
  rw [evalArguments, HandlerRecord.run_record before method handler reference keys order inputs.toInputs]
  have inside := (List.getElem?_eq_some_iff.mp inputs.methodsFound).1
  simp [evalArguments, invokePrepared, intrinsic, HandlerRecord.constructedState, pushedState,
    List.getElem?_append_left inside, inputs.methodsFound, List.set_append_left _ _ inside,
    bind, pure, Except.bind, Except.pure]

theorem methods_fresh_separate (before : State) (methods : Nat) (prior : List Value)
    (found : before.heap[methods]? = some prior) : methods ≠ before.heap.length :=
  Nat.ne_of_lt (List.getElem?_eq_some_iff.mp found).1

theorem pushed_methods_found (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value)
    (found : before.heap[methods]? = some prior) :
    (pushedState before method handler keys order methods prior).heap[methods]? =
      some (prior ++ [.object before.objects.length]) := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  rw [pushedState, List.getElem?_append_left (by simpa using inside)]
  exact List.getElem?_set_self inside

theorem pushed_keys_found (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value) :
    (pushedState before method handler keys order methods prior).heap[before.heap.length]? =
      some (keys.map Value.string) := by simp [pushedState]

theorem pushed_other_array (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value)
    (other : Nat) (inside : other < before.heap.length) (different : methods ≠ other) :
    (pushedState before method handler keys order methods prior).heap[other]? = before.heap[other]? := by
  rw [pushedState, List.getElem?_append_left (by simpa using inside)]
  exact List.getElem?_set_ne different

/-- Previous element reference values remain the same prefix. Their referents
may alias the mutated method array or other mutable cells; no deep frame is
claimed for arbitrary graphs reachable through those values. -/
theorem pushed_stored_map (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value)
    (found : before.heap[methods]? = some prior) :
    ((pushedState before method handler keys order methods prior).heap[methods]?).bind
      (fun elements => elements[prior.length]?) = some (.object before.objects.length) ∧
    (∀ index, index < prior.length →
      ((pushedState before method handler keys order methods prior).heap[methods]?).bind
        (fun elements => elements[index]?) = prior[index]?) := by
  rw [pushed_methods_found before method handler keys order methods prior found]
  constructor
  · simp
  · intro index inside
    simp [List.getElem?_append_left inside]

theorem pushed_outer_found (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value) :
    (pushedState before method handler keys order methods prior).objects[before.objects.length]? =
      some (HandlerRecord.outerRecord method (before.objects.length + 1)) :=
  HandlerRecord.constructed_outer_found before method handler keys order

theorem pushed_inner_found (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value) :
    (pushedState before method handler keys order methods prior).objects[before.objects.length + 1]? =
      some (HandlerRecord.innerRecord handler before.heap.length (order + 1)) :=
  HandlerRecord.constructed_inner_found before method handler keys order

/-- The newly stored map owns the requested method key and points to the newly
constructed handler record. This is direct storage evidence, not a proof of
the later raw method/ALL fallback expression or outer traversal. -/
theorem pushed_method_handler (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value) :
    ((pushedState before method handler keys order methods prior).objects[before.objects.length]?).bind
      (fun object => object.own.lookup method) =
        some (.data (.object (before.objects.length + 1)) true true true) := by
  rw [pushed_outer_found]
  exact (HandlerRecord.outer_method method (before.objects.length + 1)).1

/-- Exact complete private call, including receiver/brand lookup and prepared
push target before argument evaluation. Entry class/slot initialization and
native mutable builtin adequacy remain distinct obligations. -/
theorem parsed_source_correct (before after : State) (returned : Value)
    (method : JSString) (handler : Value) (reference : Nat) (keys : List JSString) (order : Int)
    (owner stamp methods : Nat) (prior : List Value)
    (inputs : Inputs before method handler reference keys order owner stamp methods prior) :
    (parseExpression pinnedSource bindings privateNames).map
      (fun source => evalExpression 34 defaultSplitLimit source before) = some (.ok (returned, after)) ↔
    PushContract before method handler keys order methods prior returned after := by
  rw [parses_pinned_source, Option.map_some, run_push before method handler reference keys order owner stamp methods prior inputs]
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, PushContract]
  exact ⟨fun ⟨value, state⟩ => ⟨value.symm, state.symm⟩,
    fun ⟨value, state⟩ => ⟨value.symm, state.symm⟩⟩

theorem parsed_source_satisfies (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) (owner stamp methods : Nat) (prior : List Value)
    (inputs : Inputs before method handler reference keys order owner stamp methods prior) :
    ∃ after,
      (parseExpression pinnedSource bindings privateNames).map
        (fun source => evalExpression 34 defaultSplitLimit source before) =
          some (.ok (.number (Int.ofNat (prior.length + 1)), after)) ∧
      PushContract before method handler keys order methods prior (.number (Int.ofNat (prior.length + 1))) after := by
  refine ⟨pushedState before method handler keys order methods prior, ?_, rfl, rfl⟩
  rw [parses_pinned_source, Option.map_some, run_push before method handler reference keys order owner stamp methods prior inputs]

theorem run_statement (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) (owner stamp methods : Nat) (prior : List Value)
    (inputs : Inputs before method handler reference keys order owner stamp methods prior) :
    execute 35 defaultSplitLimit [.evaluate expression] before =
      .ok (.normal (pushedState before method handler keys order methods prior)) := by
  rw [execute, run_push before method handler reference keys order owner stamp methods prior inputs]
  rfl

theorem parsed_statement_correct (before after : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int) (owner stamp methods : Nat) (prior : List Value)
    (inputs : Inputs before method handler reference keys order owner stamp methods prior) :
    (parseBlock pinnedSource bindings privateNames).map (fun source => execute 35 defaultSplitLimit source before) =
      some (.ok (.normal after)) ↔ StatementContract before method handler keys order methods prior after := by
  rw [parses_pinned_statement, Option.map_some, run_statement before method handler reference keys order owner stamp methods prior inputs]
  simp only [Option.some.injEq, Except.ok.injEq, Completion.normal.injEq, StatementContract]
  exact eq_comm

/-- Private brand/slot identity is retained. Any second owner referencing the
same dense methods array therefore observes its mutation through that alias. -/
theorem pushed_private_frame (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat) (prior : List Value) :
    (pushedState before method handler keys order methods prior).privates = before.privates := rfl

/-- info: 'HonoLean.Upstream.NodeMethodsPush.parsed_source_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_correct

end HonoLean.Upstream.NodeMethodsPush
