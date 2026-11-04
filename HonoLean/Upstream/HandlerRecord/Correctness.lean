import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.HandlerRecord.Generated
import HonoLean.Upstream.HandlerRecord.Contract

namespace HonoLean.Upstream.HandlerRecord

open SourceSubset ECMA2025

def bindings : List String := ["method", "handler", "possibleKeys", "order"]

def expression : Expr := .objectLiteral [(.variable "method", .objectLiteral [
  (.string handlerKey, .variable "handler"),
  (.string possibleKeysKey, .arrayLiteral [(true, .variable "possibleKeys")]),
  (.string scoreKey, .preIncrement "order")])]

set_option maxRecDepth 32768 in
theorem parses_pinned_source : parseExpression pinnedSource bindings = some expression := by cbv

/-- Structural first-binding replacement agrees with numeric prefix increment;
later shadowed bindings and unrelated bindings are left in their positions. -/
theorem increment_order (environment : List (String × Value)) (order : Int)
    (binding : environment.lookup "order" = some (.number order)) :
    incrementEnvironment "order" environment = .ok (replaceOrder environment (order + 1)) := by
  induction environment with
  | nil => simp at binding
  | cons head rest ih =>
    obtain ⟨name, value⟩ := head
    by_cases same : name = "order"
    · subst name
      have equal : value = .number order := by simpa using binding
      subst value
      simp [incrementEnvironment, replaceOrder]
    · have different : ("order" == name) = false := beq_false_of_ne (Ne.symm same)
      have tailBinding : rest.lookup "order" = some (.number order) := by
        simpa [List.lookup_cons, different] using binding
      simp [incrementEnvironment, replaceOrder, same, ih tailBinding, Except.map]

theorem replaceOrder_other (environment : List (String × Value)) (score : Int) (name : String)
    (different : name ≠ "order") :
    (replaceOrder environment score).lookup name = environment.lookup name := by
  induction environment with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    by_cases same : key = "order"
    · subst key
      simp [replaceOrder, List.lookup_cons, beq_false_of_ne different]
    · simp only [replaceOrder, same, ↓reduceIte, List.lookup_cons]
      split <;> simp_all

theorem replaceOrder_order (environment : List (String × Value)) (order score : Int)
    (binding : environment.lookup "order" = some (.number order)) :
    (replaceOrder environment score).lookup "order" = some (.number score) := by
  induction environment with
  | nil => simp at binding
  | cons head rest ih =>
    obtain ⟨name, value⟩ := head
    by_cases same : name = "order"
    · subst name
      simp [replaceOrder]
    · have different : ("order" == name) = false := beq_false_of_ne (Ne.symm same)
      have tailBinding : rest.lookup "order" = some (.number order) := by
        simpa [List.lookup_cons, different] using binding
      simp [replaceOrder, same, List.lookup_cons, different, ih tailBinding]

theorem score_safe (order : Int) (safe : SafeOrder order) :
    -9007199254740991 ≤ order + 1 ∧ order + 1 ≤ 9007199254740991 := by
  simp only [SafeOrder] at safe
  omega

theorem constructed_inner_found (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) :
    (constructedState before method handler keys order).objects[before.objects.length + 1]? =
      some (innerRecord handler before.heap.length (order + 1)) := by
  simp [constructedState]

theorem constructed_outer_found (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) :
    (constructedState before method handler keys order).objects[before.objects.length]? =
      some (outerRecord method (before.objects.length + 1)) := by simp [constructedState]

theorem constructed_keys_found (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) :
    (constructedState before method handler keys order).heap[before.heap.length]? =
      some (keys.map Value.string) := by simp [constructedState]

theorem constructed_frames (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) :
    (∀ reference, reference < before.objects.length →
      (constructedState before method handler keys order).objects[reference]? = before.objects[reference]?) ∧
    (∀ reference, reference < before.heap.length →
      (constructedState before method handler keys order).heap[reference]? = before.heap[reference]?) ∧
    (∀ name, name ≠ "order" →
      (constructedState before method handler keys order).environment.lookup name = before.environment.lookup name) ∧
    (constructedState before method handler keys order).sets = before.sets ∧
    (constructedState before method handler keys order).functions = before.functions := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro reference bound
    exact List.getElem?_append_left bound
  · intro reference bound
    exact List.getElem?_append_left bound
  · intro name different
    exact replaceOrder_other before.environment (order + 1) name different

theorem run_record (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int)
    (inputs : Inputs before method handler reference keys order) :
    evalExpression 32 defaultSplitLimit expression before =
      .ok (.object before.objects.length, constructedState before method handler keys order) := by
  obtain ⟨root, rootFound⟩ := inputs.rootFound
  simp [expression, evalExpression, evalObjectFields, createLiteralObject, ordinaryObjectPrototype,
    rootFound, lookupVariable, inputs.methodBinding, inputs.handlerBinding, inputs.setBinding,
    literalPropertyName, defineLiteralProperty, emptyLiteralObject, newDataObject, putOwn,
    evalLiteralElements, iterableValues, inputs.setFound, StringSet.values, appendLiteralElements,
    incrementVariable, increment_order before.environment order inputs.orderBinding,
    replaceOrder_order before.environment order (order + 1) inputs.orderBinding,
    innerRecord, outerRecord, constructedState, handlerKey, possibleKeysKey, scoreKey, List.lookup_cons,
    bind, pure, Except.bind, Except.pure]

/-- Complete exact object-expression contract, conditional on source inputs.
Neither private #methods.push nor a persistent cross-call order cell is modeled. -/
theorem parsed_source_correct (before after : State) (returned : Value) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int)
    (inputs : Inputs before method handler reference keys order) :
    (parseExpression pinnedSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source before) =
      some (.ok (returned, after)) ↔ RecordContract before method handler keys order returned after := by
  rw [parses_pinned_source, Option.map_some, run_record before method handler reference keys order inputs]
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, RecordContract]
  exact ⟨fun ⟨value, state⟩ => ⟨value.symm, state.symm⟩,
    fun ⟨value, state⟩ => ⟨value.symm, state.symm⟩⟩

theorem parsed_source_satisfies (before : State) (method : JSString) (handler : Value)
    (reference : Nat) (keys : List JSString) (order : Int)
    (inputs : Inputs before method handler reference keys order) :
    ∃ after,
      (parseExpression pinnedSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source before) =
        some (.ok (.object before.objects.length, after)) ∧
      RecordContract before method handler keys order (.object before.objects.length) after := by
  refine ⟨constructedState before method handler keys order, ?_, rfl, rfl⟩
  rw [parses_pinned_source, Option.map_some, run_record before method handler reference keys order inputs]

/-- info: 'HonoLean.Upstream.HandlerRecord.parsed_source_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_correct

end HonoLean.Upstream.HandlerRecord
