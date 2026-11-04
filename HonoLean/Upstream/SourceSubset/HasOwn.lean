import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset

open ECMA2025

/-! ECMA2025 §20.1.2.14,
https://tc39.es/ecma262/2025/multipage/fundamental-objects.html#sec-object.hasown
Frozen standard Object.hasOwn specialization: ordinary allocated object
and already-primitive UTF16 string key. The existing descriptor-presence model
is reused without prototype traversal or getter/value invocation. Boxing,
symbols, ToPropertyKey/coercion, proxies, mutable realm hooks and full native
error-state adequacy remain outside this fragment. -/

def OwnDescriptorPresence (object : OrdinaryObject) (key : JSString) (present : Bool) : Prop :=
  (present = true ∧ ∃ descriptor, object.own.lookup key = some descriptor) ∨
  (present = false ∧ object.own.lookup key = none)

structure HasOwnContract (before after : State) (reference : Nat) (key : JSString) (present : Bool) : Prop where
  descriptor : ∃ object, before.objects[reference]? = some object ∧ OwnDescriptorPresence object key present
  state : after = before

theorem ownDescriptorPresence_isSome (object : OrdinaryObject) (key : JSString) :
    OwnDescriptorPresence object key (object.own.lookup key).isSome := by
  cases found : object.own.lookup key with
  | none => exact Or.inr ⟨rfl, found⟩
  | some descriptor => exact Or.inl ⟨rfl, descriptor, found⟩

theorem prepare_object_hasOwn (before : State) :
    prepareMethod .objectConstructor "hasOwn" before = .ok (.standard .objectConstructor "hasOwn") := rfl

theorem intrinsic_hasOwn (before : State) (reference : Nat) (key : JSString) (object : OrdinaryObject)
    (found : before.objects[reference]? = some object) (limit : Nat) :
    intrinsic limit .objectConstructor "hasOwn" [.object reference, .string key] before =
      .ok (.boolean (object.own.lookup key).isSome, before) := by
  simp [intrinsic, ECMA2025.hasOwn, found, Except.mapError, Except.map]

theorem intrinsic_hasOwn_satisfies (before : State) (reference : Nat) (key : JSString) (object : OrdinaryObject)
    (found : before.objects[reference]? = some object) (limit : Nat) :
    ∃ present, intrinsic limit .objectConstructor "hasOwn" [.object reference, .string key] before =
      .ok (.boolean present, before) ∧ HasOwnContract before before reference key present :=
  ⟨_, intrinsic_hasOwn before reference key object found limit,
    ⟨⟨object, found, ownDescriptorPresence_isSome object key⟩, rfl⟩⟩

/-- Callee preparation occurs after receiver evaluation and before every
argument. Descriptor presence is read in the CURRENT post-argument state. -/
theorem eval_hasOwn_resolved (fuel limit : Nat) (receiver objectExpr keyExpr : Expr)
    (before receiverState argumentState : State) (reference : Nat) (key : JSString) (object : OrdinaryObject)
    (base : evalExpression fuel limit receiver before = .ok (.objectConstructor, receiverState))
    (arguments : evalArguments fuel limit [objectExpr, keyExpr] receiverState = .ok ([.object reference, .string key], argumentState))
    (found : argumentState.objects[reference]? = some object) :
    evalExpression (fuel + 1) limit (.call receiver "hasOwn" [objectExpr, keyExpr]) before =
      .ok (.boolean (object.own.lookup key).isSome, argumentState) := by
  simp [evalExpression, base, arguments, invokePrepared,
    intrinsic_hasOwn argumentState reference key object found limit, bind, Except.bind]

theorem lookup_standard_Object (before : State) (standard : StandardObjectBinding before) :
    lookupVariable before "Object" = .ok .objectConstructor := by
  rcases standard with missing | bound
  · simp [lookupVariable, missing]
  · simp [lookupVariable, bound]

theorem eval_hasOwn_standard (extra limit : Nat) (before : State) (objectName keyName : String)
    (reference : Nat) (key : JSString) (object : OrdinaryObject)
    (standard : StandardObjectBinding before)
    (binding : before.environment.lookup objectName = some (.object reference))
    (keyBinding : before.environment.lookup keyName = some (.string key))
    (found : before.objects[reference]? = some object) :
    evalExpression (extra + 5) limit (.call (.variable "Object") "hasOwn" [.variable objectName, .variable keyName]) before =
      .ok (.boolean (object.own.lookup key).isSome, before) := by
  have objectBinding := lookup_standard_Object before standard
  refine eval_hasOwn_resolved (extra + 4) limit (.variable "Object") (.variable objectName) (.variable keyName)
    before before before reference key object ?_ ?_ found
  · simp only [evalExpression, objectBinding, bind, Except.bind, pure, Except.pure]
  · simp [evalArguments, evalExpression, lookupVariable, binding, keyBinding, bind, Except.bind, pure, Except.pure]

end HonoLean.Upstream.SourceSubset
