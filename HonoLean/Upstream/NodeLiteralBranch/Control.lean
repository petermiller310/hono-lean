import HonoLean.Upstream.NodeLiteralBranch.Evaluation

namespace HonoLean.Upstream.NodeLiteralBranch

open SourceSubset ECMA2025

theorem execute_last_direct (extra : Nat) (before after : State) (table : PrivateMethodTable)
    (target children receiver : Nat) (wildcard : Value)
    (targetBinding : before.environment.lookup "nextNode" = some (.object target))
    (thisValue : before.thisValue = .object receiver)
    (childrenRead : privateGet (.object target) "children" before = .ok (.object children))
    (wildcardRead : getProperty propertyFuel before.objects children [42] = .ok wildcard)
    (falsy : truthy wildcard = false)
    (direct : runPrivateMethodCall (extra + 17) defaultSplitLimit table ⟨.object receiver⟩ NodePrivateCall.fourCall before =
      .ok (.undefined, after)) :
    executePrivateControl (extra + 20) defaultSplitLimit table lastBody before = .ok (.normal after) := by
  have guard := eval_wildcard (extra + 10) defaultSplitLimit before target children wildcard targetBinding childrenRead wildcardRead
  simp only [lastBody, executePrivateControl, executePrivateControlStmt]
  rw [guard]
  simp only [bind, Except.bind, falsy, Bool.false_eq_true, ↓reduceIte, executePrivateControl]
  rw [thisValue, direct]
  simp [pure, Except.pure]

theorem execute_last_wildcard (extra : Nat) (before middle after : State) (table : PrivateMethodTable)
    (target children receiver wildcardTarget : Nat)
    (targetBinding : before.environment.lookup "nextNode" = some (.object target))
    (thisValue : before.thisValue = .object receiver)
    (middleThis : middle.thisValue = .object receiver)
    (childrenRead : privateGet (.object target) "children" before = .ok (.object children))
    (wildcardRead : getProperty propertyFuel before.objects children [42] = .ok (.object wildcardTarget))
    (wildcard : runPrivateMethodCall (extra + 16) defaultSplitLimit table ⟨.object receiver⟩ wildcardCall before =
      .ok (.undefined, middle))
    (direct : runPrivateMethodCall (extra + 17) defaultSplitLimit table ⟨.object receiver⟩ NodePrivateCall.fourCall middle =
      .ok (.undefined, after)) :
    executePrivateControl (extra + 20) defaultSplitLimit table lastBody before = .ok (.normal after) := by
  have guard := eval_wildcard (extra + 10) defaultSplitLimit before target children (.object wildcardTarget) targetBinding childrenRead wildcardRead
  simp only [lastBody, executePrivateControl, executePrivateControlStmt]
  rw [guard]
  simp only [bind, Except.bind, truthy, ↓reduceIte, executePrivateControl, executePrivateControlStmt]
  rw [thisValue, wildcard]
  simp only [pure, Except.pure]
  rw [middleThis, direct]

theorem execute_child_last (extra : Nat) (before after : State) (table : PrivateMethodTable)
    (parent children target receiver stamp collector temp nodeParams : Nat)
    (part query : JSString) (last old : Value)
    (entry : ChildEntry before parent children target receiver stamp collector temp nodeParams part query last old)
    (lastTruthy : truthy last = true)
    (lastRun : executePrivateControl (extra + 194) defaultSplitLimit table lastBody
      (writtenState before target stamp nodeParams) = .ok (.normal after)) :
    executePrivateControl (extra + 200) defaultSplitLimit table program before = .ok (.normal after) := by
  have declared := execute_declaration (extra + 188) defaultSplitLimit before parent children part (.object target) entry.lookup
  have propagated := execute_propagation (extra + 161) defaultSplitLimit before parent children target receiver stamp collector temp nodeParams
    part query last old entry
  simp only [program, childBody, executePrivateControl, executePrivateControlStmt]
  rw [declared]
  simp only [bind, Except.bind]
  have nextEval : evalExpression (extra + 197) defaultSplitLimit (.variable "nextNode") (declaredState before (.object target)) =
      .ok (.object target, declaredState before (.object target)) := by
    simp [evalExpression, lookupVariable, declaredState, bind, Except.bind, pure, Except.pure]
  rw [nextEval]
  simp only [pure, Except.pure, show truthy (.object target) = true from rfl, ↓reduceIte]
  simp only [executePrivateControl, executePrivateControlStmt]
  rw [propagated]
  simp only [bind, Except.bind]
  have lastBinding : (writtenState before target stamp nodeParams).environment.lookup "isLast" = some last := by
    simpa [writtenState, writePrivateDataState, declaredState, List.lookup] using entry.lastBinding
  rw [show evalExpression (extra + 194) defaultSplitLimit (.variable "isLast")
      (writtenState before target stamp nodeParams) = .ok (last, writtenState before target stamp nodeParams) by
    simp [evalExpression, lookupVariable, lastBinding, bind, Except.bind, pure, Except.pure]]
  simp only [lastTruthy, ↓reduceIte]
  rw [lastRun]

end HonoLean.Upstream.NodeLiteralBranch
