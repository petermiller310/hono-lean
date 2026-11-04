import HonoLean.Upstream.NodeExecCall.Correctness
import HonoLean.Upstream.NodeCaptureCollect.Composition

set_option autoImplicit false
namespace HonoLean.Upstream.NodeExecCall
open SourceSubset ECMA2025

/-- Initial capture target/path facts. There is deliberately no m binding,
match-array cell, future successful Set or completed guard here. -/
structure GuardTarget (before : State) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop extends NodeCaptureGuard.HeaderInputs before params object name where
  absent : object.own.lookup name = none
  path : NodeCaptureGuard.DescriptorPath before.objects name params descriptor depth
  bound : depth ≤ propertyFuel

theorem guard_header_after_exec (before : State) (matcher : Nat) (input : JSString) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (header : NodeCaptureGuard.HeaderInputs before params object name) :
    NodeCaptureGuard.HeaderInputs (resultState .singleton before matcher input) params object name := by
  refine ⟨?_, ?_, ?_, header.found, header.wellFormed⟩
  · simpa [StandardObjectBinding, resultState, List.lookup_cons] using header.standardObject
  · simpa [resultState, List.lookup_cons] using header.paramsBinding
  · simpa [resultState, List.lookup_cons] using header.nameBinding

theorem computed_match_inputs (before : State) (matcher : Nat) (input : JSString) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (descriptor : Option PropertyDescriptor) (depth : Nat) (target : GuardTarget before params object name descriptor depth) :
    NodeCaptureGuard.AbsentInputs (resultState .singleton before matcher input) params object name before.heap.length [.string input] input descriptor depth := by
  refine ⟨guard_header_after_exec before matcher input params object name target.toHeaderInputs, target.absent, rfl,
    ?_, rfl, ?_, target.path, target.bound⟩
  · simp [resultState, callState, returnedHeap]
  · change 1 ≤ maximumArrayLength
    decide

/-- Source156 computes the fresh m array from its real argument, then the
existing exact158–160 guard executes with that produced cell. The157 result
is only the bound header test: no synthetic if-body or containing-if execution
is claimed. Initial descriptors still determine create/ignore/rejection/gap. -/
theorem source_singleton_then_guard_satisfies (extra : Nat) (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (closure : MemberClosure) (matcher handle : Nat) (input : JSString) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : Inputs before methods functions members closure matcher handle input)
    (body : closure.program.body = shapeBody .singleton closure.program.parameter)
    (target : GuardTarget before params object name descriptor depth) :
    let computed := resultState .singleton before matcher input
    sourceExec (extra + 20) methods functions members before = some (.ok computed) ∧
    Contract (extra + 20) before computed closure matcher handle input .singleton ∧
    evalExpression (extra + 1) defaultSplitLimit guardCondition computed = .ok (.array before.heap.length, computed) ∧
    truthy (.array before.heap.length) = true ∧
    ∃ outcome, NodeCaptureGuard.sourceGuard (extra + 27) computed = some outcome ∧ NodeCaptureGuard.GuardContract computed params object name outcome := by
  dsimp only
  obtain ⟨run, contract⟩ := source_exec_satisfies extra before methods functions members closure matcher handle input .singleton inputs body
  exact ⟨run, contract, (produced_guard_test extra before matcher input .singleton).1, rfl,
    NodeCaptureGuard.source_absent_satisfies extra _ params object name before.heap.length [.string input] input descriptor depth
      (computed_match_inputs before matcher input params object name descriptor depth target)⟩

/-- Even the computed match is irrelevant to an existing own property's guard:
source156 runs, then158–160 skips without invoking getters or overwriting data. -/
theorem source_singleton_then_owned_guard_satisfies (extra : Nat) (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (closure : MemberClosure) (matcher handle : Nat) (input : JSString) (params : Nat) (object : OrdinaryObject) (name : JSString)
    (descriptor : PropertyDescriptor)
    (inputs : Inputs before methods functions members closure matcher handle input)
    (body : closure.program.body = shapeBody .singleton closure.program.parameter)
    (target : NodeCaptureGuard.OwnInputs before params object name descriptor) :
    let computed := resultState .singleton before matcher input
    sourceExec (extra + 20) methods functions members before = some (.ok computed) ∧
    Contract (extra + 20) before computed closure matcher handle input .singleton ∧
    NodeCaptureGuard.sourceGuard (extra + 32) computed = some (.ok (.normal computed)) ∧
    NodeCaptureGuard.GuardContract computed params object name (.ok (.normal computed)) := by
  dsimp only
  obtain ⟨run, contract⟩ := source_exec_satisfies extra before methods functions members closure matcher handle input .singleton inputs body
  exact ⟨run, contract, NodeCaptureGuard.source_owned_satisfies extra _ params object name descriptor
    ⟨guard_header_after_exec before matcher input params object name target.toHeaderInputs, target.own⟩⟩

theorem inputs_after_init (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (closure : MemberClosure) (matcher handle : Nat) (input : JSString) (object : OrdinaryObject)
    (inputs : Inputs before methods functions members closure matcher handle input) :
    Inputs (NodeParamsInit.mapState before object) methods functions members closure matcher handle input := by
  refine ⟨?_, ?_, ?_, inputs.noArgBefore, inputs.privateBefore, inputs.functionsBefore, inputs.handleBound, inputs.closureFound⟩
  · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.matcherBinding
  · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.inputBinding
  · obtain ⟨writable, enumerable, configurable, depth, path, bound⟩ := inputs.current
    exact ⟨writable, enumerable, configurable, depth, NodeCaptureGuard.descriptor_path_append before.objects [object] execKey matcher _ depth path, bound⟩

/-- Correct causal order: actual123 FIRST, actual156 computes m NEXT, then the
actual guard158–160 consumes it. Both initializer arms remain. No early staged
m is slipped into the older before123 theorem. Omitted146–154/path production,
157's enclosing body,161 collection and traversal remain separate obligations. -/
theorem source_init_exec_guard_satisfies (extra : Nat) (before : State) (methods : PrivateMethodTable) (functions : FunctionTable) (members : MemberTable)
    (closure : MemberClosure) (matcher handle node identity parent empty initFuel : Nat) (input name : JSString) (object : OrdinaryObject)
    (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : Inputs before methods functions members closure matcher handle input)
    (body : closure.program.body = shapeBody .singleton closure.program.parameter)
    (initializer : NodeCaptureCollect.InitInputs before node identity parent empty object initFuel)
    (standard : StandardObjectBinding before) (nameBinding : before.environment.lookup "name" = some (.string name))
    (absent : object.own.lookup name = none)
    (rootPath : NodeCaptureGuard.DescriptorPath before.objects name 0 descriptor depth) (rootBound : depth + 1 ≤ propertyFuel) :
    let initialized := NodeParamsInit.mapState before object
    let computed := resultState .singleton initialized matcher input
    NodeParamsInit.sourceInit initFuel before = some (.ok initialized) ∧ NodeParamsInit.InitContract before initialized node identity parent empty ∧
    sourceExec (extra + 20) methods functions members initialized = some (.ok computed) ∧
    Contract (extra + 20) initialized computed closure matcher handle input .singleton ∧
    evalExpression (extra + 1) defaultSplitLimit guardCondition computed = .ok (.array before.heap.length, computed) ∧
    truthy (.array before.heap.length) = true ∧
    ∃ outcome, NodeCaptureGuard.sourceGuard (extra + 27) computed = some outcome ∧ NodeCaptureGuard.GuardContract computed before.objects.length object name outcome := by
  dsimp only
  obtain ⟨initRun, initContract, _, well, prototype⟩ := NodeCaptureCollect.init_inputs_satisfies before node identity parent empty object initFuel initializer
  have target : GuardTarget (NodeParamsInit.mapState before object) before.objects.length object name descriptor (depth + 1) :=
    ⟨NodeCaptureCollect.map_guard_header before object name well standard nameBinding, absent,
      .parent (by simp [NodeParamsInit.mapState]) absent prototype
        (NodeCaptureGuard.descriptor_path_append before.objects [object] name 0 descriptor depth rootPath), rootBound⟩
  exact ⟨initRun, initContract, source_singleton_then_guard_satisfies extra _ methods functions members closure matcher handle input _ object name descriptor (depth + 1)
    (inputs_after_init before methods functions members closure matcher handle input object inputs) body target⟩

/-- info: 'HonoLean.Upstream.NodeExecCall.source_singleton_then_guard_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_singleton_then_guard_satisfies
/-- info: 'HonoLean.Upstream.NodeExecCall.source_singleton_then_owned_guard_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_singleton_then_owned_guard_satisfies
/-- info: 'HonoLean.Upstream.NodeExecCall.source_init_exec_guard_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_init_exec_guard_satisfies

end HonoLean.Upstream.NodeExecCall
