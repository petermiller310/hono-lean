import HonoLean.Upstream.NodeCaptureGuard.Contract

set_option autoImplicit false

namespace HonoLean.Upstream.NodeCaptureGuard
open SourceSubset ECMA2025

theorem descriptor_path_lookup (heap : ObjectHeap) (key : JSString) (reference : Nat)
    (descriptor : Option PropertyDescriptor) (depth fuel : Nat) (path : DescriptorPath heap key reference descriptor depth)
    (bound : depth ≤ fuel) : lookupProperty fuel heap reference key = .ok descriptor := by
  induction path generalizing fuel with
  | own found property =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [lookupProperty, found, property]
  | absent found property prototype =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [lookupProperty, found, property, prototype]
  | parent found property prototype rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel => simpa [lookupProperty, found, property, prototype] using ih fuel (by omega)

/-- Pure RHS reads preserve the initial descriptor path until actual Set.
Every outcome is derived from that path, never supplied as successful Set. -/
theorem set_from_initial_descriptors (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : AbsentInputs before params object name matched values captured descriptor depth) :
    setProperty propertyFuel before.objects params name (.string captured) =
      match action descriptor object.extensible with
      | .create => .ok (writtenState before params object name captured).objects
      | .ignore => .ok before.objects
      | .reject error => .error error
      | .unsupported => .error .unsupported := by
  have resolved := descriptor_path_lookup _ _ _ _ _ propertyFuel inputs.path inputs.pathBound
  unfold setProperty
  rw [resolved]
  cases descriptor with
  | none =>
    simp only [action, writeOwnData, inputs.found, inputs.absent, writtenState, bind, Except.bind]
    split <;> rfl
  | some descriptor =>
    cases descriptor with
    | data value writable enumerable configurable =>
      cases writable <;> simp [action, writeOwnData, inputs.found, inputs.absent, writtenState, bind, Except.bind]
      split <;> rfl
    | accessor getter setter enumerable configurable =>
      cases setter <;> simp [action, callSetter, inputs.found, bind, Except.bind]

theorem created_contract (before : State) (params : Nat) (object : OrdinaryObject) (name captured : JSString)
    (found : before.objects[params]? = some object) :
    CreatedContract before (writtenState before params object name captured) params object name captured := by
  have allocated := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨rfl, ⟨newDataObject object name (.string captured), ?_, putOwn_self _ _ _, rfl⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact List.getElem?_set_self allocated
  · intro reference different
    exact data_write_preserves_other_cells before.objects params reference _ different

theorem eval_condition (extra : Nat) (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (inputs : HeaderInputs before params object name) :
    evalExpression (extra + 8) defaultSplitLimit condition before =
      .ok (.boolean (!(object.own.lookup name).isSome), before) := by
  have tested := eval_hasOwn_standard (extra + 2) defaultSplitLimit before "params" "name" params name object
    inputs.standardObject inputs.paramsBinding inputs.nameBinding inputs.found
  change evalExpression ((extra + 7) + 1) defaultSplitLimit (.logicalNot (.call (.variable "Object") "hasOwn" [.variable "params", .variable "name"])) before = _
  rw [evalExpression, tested]
  rfl

/-- An existing own descriptor skips the entire assignment, including its RHS.
No matched-array, mutability, getter or extensibility premise appears. -/
theorem source_owned_satisfies (extra : Nat) (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (descriptor : PropertyDescriptor) (inputs : OwnInputs before params object name descriptor) :
    sourceGuard (extra + 32) before = some (.ok (.normal before)) ∧
      GuardContract before params object name (.ok (.normal before)) := by
  have guard := eval_condition (extra + 23) before params object name inputs.toHeaderInputs
  simp only [inputs.own, Option.isSome_some, Bool.not_true] at guard
  have run : execute (extra + 32) defaultSplitLimit program before = .ok (.normal before) := by
    simp only [program, execute]
    rw [guard]
    rfl
  exact ⟨by simpa [sourceGuard, parses_source] using congrArg some run, .skipped descriptor inputs⟩

/-- The target reference is captured before the pure match-array read; the
actual initial descriptor path then determines Set or its precise rejection. -/
theorem execute_assignment (extra : Nat) (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : AbsentInputs before params object name matched values captured descriptor depth) :
    executeAssignment (extra + 24) defaultSplitLimit assignment before =
      match action descriptor object.extensible with
      | .create => .ok (.string captured, writtenState before params object name captured)
      | .ignore => .ok (.string captured, before)
      | .reject error => .error (.objectError error)
      | .unsupported => .error (.objectError .unsupported) := by
  have write := set_from_initial_descriptors before params object name matched values captured descriptor depth inputs
  simp only [executeAssignment, assignment, evalAssignmentReference, evalReference, evalExpression, lookupVariable,
    inputs.paramsBinding, inputs.nameBinding, inputs.matchedBinding, readProperty, inputs.matchedFound, inputs.captured,
    putAssignmentReference, putReference, Option.getD_some, bind, Except.bind, pure, Except.pure]
  rw [write]
  cases action descriptor object.extensible <;> rfl

/-- A fresh own capture has exactly the attributes of ordinary data creation. -/
theorem source_created_satisfies (extra : Nat) (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : AbsentInputs before params object name matched values captured descriptor depth)
    (classified : action descriptor object.extensible = .create) :
    sourceGuard (extra + 27) before = some (.ok (.normal (writtenState before params object name captured))) ∧
      CreatedContract before (writtenState before params object name captured) params object name captured ∧
      GuardContract before params object name (.ok (.normal (writtenState before params object name captured))) := by
  have guard := eval_condition (extra + 18) before params object name inputs.toHeaderInputs
  simp only [inputs.absent, Option.isSome_none, Bool.not_false] at guard
  have assigned := execute_assignment (extra + 1) before params object name matched values captured descriptor depth inputs
  rw [classified] at assigned
  have run : execute (extra + 27) defaultSplitLimit program before = .ok (.normal (writtenState before params object name captured)) := by
    simp only [program, execute]
    rw [guard]
    simp only [bind, Except.bind, truthy, ite_true]
    rw [assigned]
  have contract := created_contract before params object name captured inputs.found
  exact ⟨by simpa [sourceGuard, parses_source] using congrArg some run, contract,
    .created matched values captured descriptor depth inputs classified _ contract⟩

/-- The inherited legacy prototype setter can leave capture absent, including
on nonextensible params. No assumed new property or null-prototype shortcut. -/
theorem source_ignored_satisfies (extra : Nat) (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : AbsentInputs before params object name matched values captured descriptor depth)
    (classified : action descriptor object.extensible = .ignore) :
    sourceGuard (extra + 27) before = some (.ok (.normal before)) ∧
      GuardContract before params object name (.ok (.normal before)) := by
  have guard := eval_condition (extra + 18) before params object name inputs.toHeaderInputs
  simp only [inputs.absent, Option.isSome_none, Bool.not_false] at guard
  have assigned := execute_assignment (extra + 1) before params object name matched values captured descriptor depth inputs
  rw [classified] at assigned
  have run : execute (extra + 27) defaultSplitLimit program before = .ok (.normal before) := by
    simp only [program, execute]
    rw [guard]
    simp only [bind, Except.bind, truthy, ite_true]
    rw [assigned]
  exact ⟨by simpa [sourceGuard, parses_source] using congrArg some run, .ignored matched values captured descriptor depth inputs classified⟩

/-- Rejections still evaluate a valid m[0] before descriptor dispatch. Error
results do not claim a native exception-state trace. -/
theorem source_rejected_satisfies (extra : Nat) (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : AbsentInputs before params object name matched values captured descriptor depth)
    (error : ObjectError) (classified : action descriptor object.extensible = .reject error) :
    sourceGuard (extra + 27) before = some (.error (.objectError error)) ∧
      GuardContract before params object name (.error (.objectError error)) := by
  have guard := eval_condition (extra + 18) before params object name inputs.toHeaderInputs
  simp only [inputs.absent, Option.isSome_none, Bool.not_false] at guard
  have assigned := execute_assignment (extra + 1) before params object name matched values captured descriptor depth inputs
  rw [classified] at assigned
  have run : execute (extra + 27) defaultSplitLimit program before = .error (.objectError error) := by
    simp only [program, execute]
    rw [guard]
    simp only [bind, Except.bind, truthy, ite_true]
    rw [assigned]
  exact ⟨by simpa [sourceGuard, parses_source] using congrArg some run, .rejected matched values captured descriptor depth inputs error classified⟩

/-- Unsupported custom setters fail closed in this model. This is not a
claim that every corresponding native setter rejects or preserves state. -/
theorem source_unsupported_satisfies (extra : Nat) (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : AbsentInputs before params object name matched values captured descriptor depth)
    (classified : action descriptor object.extensible = .unsupported) :
    sourceGuard (extra + 27) before = some (.error (.objectError .unsupported)) ∧
      GuardContract before params object name (.error (.objectError .unsupported)) := by
  have guard := eval_condition (extra + 18) before params object name inputs.toHeaderInputs
  simp only [inputs.absent, Option.isSome_none, Bool.not_false] at guard
  have assigned := execute_assignment (extra + 1) before params object name matched values captured descriptor depth inputs
  rw [classified] at assigned
  have run : execute (extra + 27) defaultSplitLimit program before = .error (.objectError .unsupported) := by
    simp only [program, execute]
    rw [guard]
    simp only [bind, Except.bind, truthy, ite_true]
    rw [assigned]
  exact ⟨by simpa [sourceGuard, parses_source] using congrArg some run,
    .unsupported matched values captured descriptor depth inputs classified⟩

theorem source_absent_satisfies (extra : Nat) (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (matched : Nat) (values : List Value) (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : AbsentInputs before params object name matched values captured descriptor depth) :
    ∃ outcome, sourceGuard (extra + 27) before = some outcome ∧ GuardContract before params object name outcome := by
  cases classified : action descriptor object.extensible with
  | create =>
    obtain ⟨run, _, contract⟩ := source_created_satisfies extra before params object name matched values captured descriptor depth inputs classified
    exact ⟨_, run, contract⟩
  | ignore =>
    obtain ⟨run, contract⟩ := source_ignored_satisfies extra before params object name matched values captured descriptor depth inputs classified
    exact ⟨_, run, contract⟩
  | reject error =>
    obtain ⟨run, contract⟩ := source_rejected_satisfies extra before params object name matched values captured descriptor depth inputs error classified
    exact ⟨_, run, contract⟩
  | unsupported =>
    obtain ⟨run, contract⟩ := source_unsupported_satisfies extra before params object name matched values captured descriptor depth inputs classified
    exact ⟨_, run, contract⟩

/-- Supported rejection codes are separate from the unsupported-setter model
gap, whose native execution is not characterized by this slice. -/
theorem rejection_codes (descriptor : Option PropertyDescriptor) (extensible : Bool) (error : ObjectError)
    (classified : action descriptor extensible = .reject error) : error = .notWritable ∨ error = .notExtensible := by
  cases descriptor with
  | none => cases extensible <;> simp_all [action]
  | some descriptor =>
    cases descriptor with
    | data value writable enumerable configurable => cases writable <;> cases extensible <;> simp_all [action]
    | accessor getter setter enumerable configurable => cases setter <;> simp_all [action]

/-- info: 'HonoLean.Upstream.NodeCaptureGuard.source_owned_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_owned_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureGuard.source_absent_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_absent_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureGuard.source_rejected_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_rejected_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureGuard.source_unsupported_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_unsupported_satisfies

end HonoLean.Upstream.NodeCaptureGuard
