import HonoLean.Upstream.NodePatternBinding.Correctness
import HonoLean.Upstream.PatternConstruct.Correctness
import HonoLean.Upstream.NodeRegExpExec.Correctness

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
namespace HonoLean.Upstream.NodePatternBinding
open SourceSubset ECMA2025

/-- A selected activation handoff after actual url68 evaluation. Binding the
produced tuple as pattern is explicit; private child.#pattern installation and
cache/Node.insert reachability are not consequences of this handoff. -/
def constructedActivation (before : ArrayBindingState) (prototype : Nat) (lower upper : UInt16) (label name : JSString) : ArrayBindingState :=
  let world := PatternConstruct.resultState before.regexp prototype lower upper label name
  {before with regexp := {world with ambient := {world.ambient with
    environment := ("pattern", .array before.regexp.ambient.heap.length) :: world.ambient.environment}}}

theorem closed_append_object (heap : ObjectHeap) (object : OrdinaryObject)
    (closed : IteratorPrototypeClosed heap)
    (parents : ∀ parent, object.prototype = some parent → parent < heap.length) :
    IteratorPrototypeClosed (heap ++ [object]) := by
  intro reference foundObject found parent prototype
  by_cases old : reference < heap.length
  · have oldFound : heap[reference]? = some foundObject := (List.getElem?_append_left old).symm.trans found
    exact Nat.lt_trans (closed reference foundObject oldFound parent prototype) (by simp)
  · have refBound := (List.getElem?_eq_some_iff.mp found).1
    have equal : reference = heap.length := by simp only [List.length_append, List.length_singleton] at refBound; omega
    subst reference
    have objectEqual : object = foundObject := by simpa using found
    subst foundObject
    exact Nat.lt_trans (parents parent prototype) (by simp)

theorem realm_constructed (before : ArrayBindingState) (context : ArrayIteratorContext)
    (valuesHandle nextHandle : Nat) (returned : Value) (prototype : Nat) (lower upper : UInt16) (label name : JSString)
    (realm : Realm before context valuesHandle nextHandle returned)
    (prototypeOld : prototype < before.regexp.ambient.objects.length) :
    Realm (constructedActivation before prototype lower upper label name) context valuesHandle nextHandle returned := by
  have appended := fun (reference : Nat) (object : OrdinaryObject)
    (found : before.regexp.ambient.objects[reference]? = some object) =>
      ((List.getElem?_append_left (l₂ := [initializedRegExpObject prototype]) (List.getElem?_eq_some_iff.mp found).1).trans found :
        (before.regexp.ambient.objects ++ [initializedRegExpObject prototype])[reference]? = some object)
  refine ⟨?_, ?_, ?_, ?_, realm.symbol, realm.noArgBefore, realm.methodsBefore, realm.functionsBefore,
    realm.membersBefore, realm.regexpBefore, realm.constructorsBefore, realm.valuesBound, realm.valuesIdentity,
    realm.nextBound, realm.nextIdentity, ?_, ?_, realm.nullish⟩
  · exact closed_append_object _ _ realm.closed (by intro parent equal; cases equal; exact prototypeOld)
  · obtain ⟨object, found⟩ := realm.arrayPrototypeFound
    exact ⟨object, appended _ object found⟩
  · obtain ⟨object, found⟩ := realm.iteratorPrototypeFound
    exact ⟨object, appended _ object found⟩
  · obtain ⟨object, found⟩ := realm.resultPrototypeFound
    exact ⟨object, appended _ object found⟩
  · obtain ⟨depth, path, bound⟩ := realm.nextPath
    exact ⟨depth, NodeCaptureGuard.descriptor_path_append _ _ _ _ _ _ path, bound⟩
  · obtain ⟨descriptor, depth, path, bound, pureRead⟩ := realm.returnPath
    exact ⟨descriptor, depth, NodeCaptureGuard.descriptor_path_append _ _ _ _ _ _ path, bound, pureRead⟩

theorem constructed_inputs (before : ArrayBindingState) (context : ArrayIteratorContext)
    (valuesHandle nextHandle : Nat) (returned : Value) (prototype : Nat) (lower upper : UInt16) (label name : JSString)
    (realm : Realm before context valuesHandle nextHandle returned)
    (allocated : ArraySymbolsAllocated before)
    (prototypeOld : prototype < before.regexp.ambient.objects.length) :
    Inputs (constructedActivation before prototype lower upper label name) context before.regexp.ambient.heap.length
      valuesHandle nextHandle (PatternConstruct.tupleValues before.regexp label name) returned := by
  refine ⟨realm_constructed before context valuesHandle nextHandle returned prototype lower upper label name realm prototypeOld,
    ?_, ?_, (by change 3 ≤ 3; decide), (by change 3 ≤ 4294967295; decide), ?_⟩
  · simp [constructedActivation, PatternConstruct.resultState, regExpConstructedState]
  · simp [constructedActivation, PatternConstruct.resultState, PatternConstruct.tupleStage, regExpConstructedState]
  · exact symbolOwn_fresh_array before allocated before.regexp.ambient.heap.length (by omega)

/-- Both exact source expressions execute in their causal order. The second
selected activation receives the actual computed tuple, not staged name/matcher
or an assumed branded record. Arbitrary safe ordered ranges are retained. -/
theorem source_construct_then_binding_satisfies (extraConstruct extraBinding : Nat)
    (before : ArrayBindingState) (context : ArrayIteratorContext) (label name : JSString)
    (matched constructorHandle valuesHandle nextHandle : Nat) (values : List Value) (lower upper : UInt16)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (returned : Value)
    (construct : PatternConstruct.Inputs before.regexp context.constructors label name matched constructorHandle values lower upper constructor prototypeObject)
    (realm : Realm before context valuesHandle nextHandle returned) (allocated : ArraySymbolsAllocated before) :
    PatternConstruct.sourceConstruct (extraConstruct + 16) context.constructors before.regexp =
      some (.ok (.array before.regexp.ambient.heap.length, PatternConstruct.resultState before.regexp constructor.prototype lower upper label name)) ∧
    PatternConstruct.Contract before.regexp (PatternConstruct.resultState before.regexp constructor.prototype lower upper label name)
      (.array before.regexp.ambient.heap.length) label name constructor.prototype lower upper ∧
    sourceBinding (extraBinding + 4) context (constructedActivation before constructor.prototype lower upper label name) =
      some (.ok (record (constructedActivation before constructor.prototype lower upper label name) nextHandle,
        resultState (constructedActivation before constructor.prototype lower upper label name) context before.regexp.ambient.heap.length
          valuesHandle nextHandle (PatternConstruct.tupleValues before.regexp label name) returned)) ∧
    Contract (constructedActivation before constructor.prototype lower upper label name)
      (resultState (constructedActivation before constructor.prototype lower upper label name) context before.regexp.ambient.heap.length
        valuesHandle nextHandle (PatternConstruct.tupleValues before.regexp label name) returned)
      context before.regexp.ambient.heap.length nextHandle (PatternConstruct.tupleValues before.regexp label name)
        (record (constructedActivation before constructor.prototype lower upper label name) nextHandle) := by
  obtain ⟨runConstruct, constructed, _⟩ := PatternConstruct.source_construct_satisfies extraConstruct before.regexp context.constructors label name
    matched constructorHandle values lower upper constructor prototypeObject construct
  have inputs := constructed_inputs before context valuesHandle nextHandle returned constructor.prototype lower upper label name realm allocated
    (List.getElem?_eq_some_iff.mp construct.prototypeFound).1
  obtain ⟨runBinding, bound⟩ := source_binding_satisfies extraBinding _ context before.regexp.ambient.heap.length valuesHandle nextHandle
    (PatternConstruct.tupleValues before.regexp label name) returned inputs
  exact ⟨runConstruct, constructed, runBinding, bound⟩

/-- Additional OLD realm facts for CURRENT inherited exec and the initial query.
The query is an input boundary: node138 does not execute source146–154. -/
structure ExecRealm (before : ArrayBindingState) (context : ArrayIteratorContext) (prototype handle : Nat) (input : JSString) : Prop where
  query : before.regexp.ambient.environment.lookup "restPathString" = some (.string input)
  current : ∃ writable enumerable configurable depth,
    NodeCaptureGuard.DescriptorPath before.regexp.ambient.objects NodeExecCall.execKey prototype
      (some (.data (.function handle) writable enumerable configurable)) depth ∧ depth + 1 ≤ propertyFuel
  noArgBeforeMember : before.regexp.ambient.functions.length ≤ context.constructors.members.base
  privateBeforeMember : context.constructors.methods.base + context.constructors.methods.entries.length ≤ context.constructors.members.base
  functionsBeforeMember : context.constructors.functions.base + context.constructors.functions.entries.length ≤ context.constructors.members.base
  membersBeforeBuiltin : context.constructors.members.base + context.constructors.members.entries.length ≤ context.constructors.builtins.base
  handleBound : context.constructors.builtins.base ≤ handle
  identity : context.constructors.builtins.entries[handle - context.constructors.builtins.base]? = some .regexpExec

def boundState (before : ArrayBindingState) (context : ArrayIteratorContext) (prototype : Nat) (lower upper : UInt16)
    (label name : JSString) (valuesHandle nextHandle : Nat) (returned : Value) : ArrayBindingState :=
  resultState (constructedActivation before prototype lower upper label name) context before.regexp.ambient.heap.length
    valuesHandle nextHandle (PatternConstruct.tupleValues before.regexp label name) returned

theorem bound_objects (before : ArrayBindingState) (context : ArrayIteratorContext) (prototype : Nat) (lower upper : UInt16)
    (label name : JSString) (valuesHandle nextHandle : Nat) (returned : Value) :
    (boundState before context prototype lower upper label name valuesHandle nextHandle returned).regexp.ambient.objects =
      before.regexp.ambient.objects ++ (initializedRegExpObject prototype ::
        addedObjects (constructedActivation before prototype lower upper label name) context (PatternConstruct.tupleValues before.regexp label name)) := by
  unfold boundState resultState
  dsimp only
  rw [beforeClose_objects]
  simp [constructedActivation, PatternConstruct.resultState, regExpConstructedState, PatternConstruct.tupleStage, List.append_assoc]

theorem bound_exec_inputs (before : ArrayBindingState) (context : ArrayIteratorContext) (prototype handle : Nat)
    (label name input : JSString) (valuesHandle nextHandle : Nat) (returned : Value)
    (exec : ExecRealm before context prototype handle input) :
    NodeRegExpExec.Inputs (boundState before context prototype 48 57 label name valuesHandle nextHandle returned).regexp
      context.constructors.methods context.constructors.functions context.constructors.members context.constructors.builtins
      before.regexp.ambient.objects.length handle input (constructedRangeRecord 48 57) (initializedRegExpObject prototype) 0 true := by
  let after := boundState before context prototype 48 57 label name valuesHandle nextHandle returned
  have found : after.regexp.ambient.objects[before.regexp.ambient.objects.length]? = some (initializedRegExpObject prototype) := by
    rw [bound_objects]
    simp
  refine ⟨?_, ?_, ?_, exec.noArgBeforeMember, exec.privateBeforeMember, exec.functionsBeforeMember,
    exec.membersBeforeBuiltin, exec.handleBound, exec.identity, ?_, ?_, found, by rfl, by decide⟩
  · rfl
  · change List.lookup "restPathString" (("matcher", _) :: ("name", _) :: ("pattern", _) :: before.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using exec.query
  · obtain ⟨writable, enumerable, configurable, depth, path, bound⟩ := exec.current
    refine ⟨writable, enumerable, configurable, depth + 1, ?_, bound⟩
    have appended := NodeCaptureGuard.descriptor_path_append before.regexp.ambient.objects
      (initializedRegExpObject prototype :: addedObjects (constructedActivation before prototype 48 57 label name) context (PatternConstruct.tupleValues before.regexp label name))
      NodeExecCall.execKey prototype _ depth path
    rw [← bound_objects before context prototype 48 57 label name valuesHandle nextHandle returned] at appended
    exact .parent found (by rfl) (by rfl) appended
  · simp [boundState, resultState, beforeClose, initialized, stepState, iteratorYieldState,
      iteratorResultState, setArrayIteratorCursor, firstState, secondState, acquired, arrayIteratorAcquiredState,
      allocateArrayIterator, constructedActivation, PatternConstruct.resultState, PatternConstruct.tupleStage, regExpConstructedState]
  · exact initialize_digits

/-- Causal selected url68 →node138 →node156 pipeline for the digit profile.
Both tuple/brand and matcher/name are computed. Constructor/cache/tree selection,
query production and omitted search control remain separate open obligations. -/
theorem source_construct_binding_digits_exec_satisfies (extraConstruct extraBinding extraExec : Nat)
    (before : ArrayBindingState) (context : ArrayIteratorContext) (label name input : JSString)
    (matched constructorHandle valuesHandle nextHandle execHandle : Nat) (values : List Value)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (returned : Value)
    (construct : PatternConstruct.Inputs before.regexp context.constructors label name matched constructorHandle values 48 57 constructor prototypeObject)
    (realm : Realm before context valuesHandle nextHandle returned) (allocated : ArraySymbolsAllocated before)
    (exec : ExecRealm before context constructor.prototype execHandle input) :
    PatternConstruct.sourceConstruct (extraConstruct + 16) context.constructors before.regexp =
      some (.ok (.array before.regexp.ambient.heap.length, PatternConstruct.resultState before.regexp constructor.prototype 48 57 label name)) ∧
    sourceBinding (extraBinding + 4) context (constructedActivation before constructor.prototype 48 57 label name) =
      some (.ok (record (constructedActivation before constructor.prototype 48 57 label name) nextHandle,
        boundState before context constructor.prototype 48 57 label name valuesHandle nextHandle returned)) ∧
    NodeRegExpExec.sourceExec (extraExec + 20) context.constructors.methods context.constructors.functions context.constructors.members context.constructors.builtins
      (boundState before context constructor.prototype 48 57 label name valuesHandle nextHandle returned).regexp =
      some (.ok (NodeRegExpExec.resultState (boundState before context constructor.prototype 48 57 label name valuesHandle nextHandle returned).regexp input)) ∧
    NodeRegExpExec.Contract (extraExec + 20) (boundState before context constructor.prototype 48 57 label name valuesHandle nextHandle returned).regexp
      (NodeRegExpExec.resultState (boundState before context constructor.prototype 48 57 label name valuesHandle nextHandle returned).regexp input)
      before.regexp.ambient.objects.length execHandle input (initializedRegExpObject constructor.prototype) 0 true := by
  obtain ⟨constructed, _, bound, _⟩ := source_construct_then_binding_satisfies extraConstruct extraBinding before context label name matched constructorHandle
    valuesHandle nextHandle values 48 57 constructor prototypeObject returned construct realm allocated
  obtain ⟨executed, result⟩ := NodeRegExpExec.source_exec_satisfies extraExec _ context.constructors.methods context.constructors.functions
    context.constructors.members context.constructors.builtins before.regexp.ambient.objects.length execHandle input
    (constructedRangeRecord 48 57) (initializedRegExpObject constructor.prototype) 0 true
    (bound_exec_inputs before context constructor.prototype execHandle label name input valuesHandle nextHandle returned exec)
  exact ⟨constructed, bound, executed, result⟩

end HonoLean.Upstream.NodePatternBinding
