import HonoLean.Upstream.NodeCaptureGuard.Correctness

set_option autoImplicit false

namespace HonoLean.Upstream.NodeCaptureGuard
open SourceSubset ECMA2025

/-- Explicit ordinary-object preparation fixture. This is the actual parsed
`const params = {}` declaration; it does not erase/claim the spread arm of
source123 or the intervening search reachability. -/
def literalParamsSource : String := "const params = {}\n"
def literalParamsProgram : List Stmt := [.declare "params" (.objectLiteral [])]
def literalParamsState (before : State) : State :=
  {before with
    environment := ("params", .object before.objects.length) :: before.environment
    objects := before.objects ++ [emptyLiteralObject]}

theorem parses_literal_params : parseBlock literalParamsSource [] = some literalParamsProgram := by cbv

theorem execute_literal_params (extra : Nat) (before : State) (root : OrdinaryObject)
    (found : before.objects[0]? = some root) :
    execute (extra + 16) defaultSplitLimit literalParamsProgram before = .ok (.normal (literalParamsState before)) := by
  simp [literalParamsProgram, execute, evalExpression, createLiteralObject, ordinaryObjectPrototype, found,
    evalObjectFields, literalParamsState, bind, Except.bind, pure, Except.pure]

theorem descriptor_path_append (heap extra : ObjectHeap) (key : JSString) (reference : Nat)
    (descriptor : Option PropertyDescriptor) (depth : Nat) (path : DescriptorPath heap key reference descriptor depth) :
    DescriptorPath (heap ++ extra) key reference descriptor depth := by
  induction path with
  | own found property =>
    exact .own ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found) property
  | absent found property prototype =>
    exact .absent ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found) property prototype
  | parent found property prototype rest ih =>
    exact .parent ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found) property prototype ih

theorem literal_absent_inputs (before : State) (root : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (_rootFound : before.objects[0]? = some root) (standard : StandardObjectBinding before)
    (nameBinding : before.environment.lookup "name" = some (.string name))
    (matchedBinding : before.environment.lookup "m" = some (.array matched))
    (matchedFound : before.heap[matched]? = some values) (capturedFound : values[0]? = some (.string captured))
    (lengthBound : values.length ≤ maximumArrayLength)
    (path : DescriptorPath before.objects name 0 descriptor depth) (pathBound : depth + 1 ≤ propertyFuel) :
    AbsentInputs (literalParamsState before) before.objects.length emptyLiteralObject name matched values captured descriptor (depth + 1) := by
  refine ⟨⟨?_, rfl, ?_, by simp [literalParamsState], by simp [WellFormedObject, emptyLiteralObject]⟩,
    rfl, ?_, matchedFound, capturedFound, lengthBound, ?_, pathBound⟩
  · simpa [StandardObjectBinding, literalParamsState, List.lookup_cons] using standard
  · simpa [literalParamsState, List.lookup_cons] using nameBinding
  · simpa [literalParamsState, List.lookup_cons] using matchedBinding
  · exact .parent (object := emptyLiteralObject) (by simp [literalParamsState]) rfl rfl (descriptor_path_append _ _ _ _ _ _ path)

/-- Ordinary `{}` is created by execution before the actual source guard. The
caller supplies only initial m/string and root prototype descriptor structure;
no params object, Set result or future capture is an input. -/
theorem literal_then_capture_satisfies (extra : Nat) (before : State) (root : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (rootFound : before.objects[0]? = some root) (standard : StandardObjectBinding before)
    (nameBinding : before.environment.lookup "name" = some (.string name))
    (matchedBinding : before.environment.lookup "m" = some (.array matched))
    (matchedFound : before.heap[matched]? = some values) (capturedFound : values[0]? = some (.string captured))
    (lengthBound : values.length ≤ maximumArrayLength)
    (path : DescriptorPath before.objects name 0 descriptor depth) (pathBound : depth + 1 ≤ propertyFuel) :
    (parseBlock literalParamsSource []).map (fun source => execute (extra + 16) defaultSplitLimit source before) =
      some (.ok (.normal (literalParamsState before))) ∧
    ∃ outcome, sourceGuard (extra + 27) (literalParamsState before) = some outcome ∧
      GuardContract (literalParamsState before) before.objects.length emptyLiteralObject name outcome := by
  refine ⟨?_, source_absent_satisfies extra _ _ _ name matched values captured descriptor (depth + 1)
    (literal_absent_inputs before root name matched values captured descriptor depth rootFound standard nameBinding matchedBinding
      matchedFound capturedFound lengthBound path pathBound)⟩
  rw [parses_literal_params, Option.map_some, execute_literal_params extra before root rootFound]

/-- info: 'HonoLean.Upstream.NodeCaptureGuard.literal_then_capture_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms literal_then_capture_satisfies

end HonoLean.Upstream.NodeCaptureGuard
