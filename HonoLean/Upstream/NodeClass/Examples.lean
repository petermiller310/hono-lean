import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodeClass.Examples

open SourceSubset ECMA2025 RegistrationHistory

private def getKey : JSString := [71, 69, 84]
private def postKey : JSString := [80, 79, 83, 84]
private def idKey : JSString := [105, 100]
private def secondKey : JSString := [115, 101, 99, 111, 110, 100]
private def temp0 : Value := .string [116, 101, 109, 112, 48]
private def temp1 : Value := .string [116, 101, 109, 112, 49]
private def temporaryParams : OrdinaryObject :=
  newDataObject (newDataObject emptyNullObject idKey temp0) secondKey temp1

/-- An older represented definition has no instances but still reserves private
identity1000. The next class must avoid this table-captured name as well as the
existing owner2/name31 in the ordinary state. -/
private def olderClosure : PrivateMethodClosure :=
  ⟨⟨"older", [], .named "void", []⟩, [], [("older", 1000)]⟩
private def oldTable : PrivateMethodTable := ⟨1, [olderClosure]⟩
private def before : State :=
  {environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string SearchEntry.allKey),
      ("outer", .number 41)],
    objects := [objectPrototypeProjection [], temporaryParams, {prototype := some 0}],
    functions := [⟨CreateNullObject.createProgram, []⟩],
    privates := PrivateStore.ofData [("old", 31)] [(2, [(31, .number 9)])]}
private def moduleState : State := NodeInitialization.preambleState before
private def world : PrivateWorld := initialNodeWorld before oldTable
private def firstClass : SelectedPrivateClass := definition moduleState.environment world.nextIdentity 2
private def firstTable : PrivateMethodTable := extendedTable oldTable moduleState.environment world.nextIdentity
private def secondClass : SelectedPrivateClass := definition moduleState.environment (world.nextIdentity + 6) 3
private def secondTable : PrivateMethodTable :=
  extendedTable firstTable moduleState.environment (world.nextIdentity + 6)
private def firstInstance : State := instanceState moduleState (some 0) moduleState.environment 1001 2 (.object 3)
private def secondInstance : State := instanceState firstInstance (some 0) moduleState.environment 1001 2 (.object 3)
private def initialized : State := classActivation secondInstance 1001
private def requests : List Request :=
  [⟨getKey, .number 10, [idKey, secondKey, idKey]⟩,
   ⟨SearchEntry.allKey, .number 11, [idKey, secondKey]⟩,
   ⟨postKey, .number 12, [secondKey]⟩]
private def registered : State := endState initialized 6 2 0 [] requests
private def caller : List (String × Value) :=
  [("node", .object 4), ("child", .object 6), ("nextNode", .object 6),
   ("method", .string getKey), ("params", .object 1), ("outer", .number 99)]
private def entry : State := callEntry registered caller

theorem joint_fresh_source_definitions :
    world.nextIdentity = 1001 ∧
    defineSource moduleState world oldTable = some (firstClass, ⟨1007⟩, firstTable) ∧
    defineSource moduleState ⟨1007⟩ firstTable = some (secondClass, ⟨1013⟩, secondTable) ∧
    firstClass.firstHandle = 2 ∧ secondClass.firstHandle = 3 ∧
    secondTable.entries[0]? = some olderClosure := by
  rw [parsed_define_node moduleState world oldTable (by decide),
    parsed_define_node moduleState ⟨1007⟩ firstTable (by decide)]
  cbv

set_option maxRecDepth 32768 in
theorem source_two_instances :
    instantiatePrivateClass 64 defaultSplitLimit firstClass (some 0) moduleState = .ok (4, firstInstance) ∧
    instantiatePrivateClass 64 defaultSplitLimit firstClass (some 0) firstInstance = .ok (6, secondInstance) ∧
    privateGet (.object 4) "pushHandlerSets" initialized = .ok (.function 2) ∧
    privateGet (.object 6) "pushHandlerSets" initialized = .ok (.function 2) ∧
    privateGet (.object 4) "methods" initialized = .ok (.array 0) ∧
    privateGet (.object 6) "methods" initialized = .ok (.array 2) ∧
    privateGet (.object 6) "pushHandlerSets"
      {initialized with privates := {initialized.privates with names := secondClass.names}} = .error .privateBrand := by
  cbv

private theorem seed : Seed initialized 6 1001 2 0 [] := by
  exact ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨⟨[], some 0, true⟩, rfl⟩,
    rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩
private theorem callable : NodePrivateCall.Callable initialized secondTable
    (closure moduleState.environment 1001) 4 2 := by
  exact ⟨rfl, by decide, by decide, rfl, rfl⟩

private def parameter : JSString → Value := fun _ => .undefined
private def node : JSString → Value := fun key => if key = idKey then temp0 else temp1
private def context : List (String × Value) :=
  methodContext (closure moduleState.environment 1001) 6 getKey 1 (.object 3)

private theorem closed : NodeParamLoop.PrototypeClosed initialized.objects initialized.objects.length := by
  intro reference _ object found parent prototype
  have member := List.mem_of_getElem? found
  change object ∈ [objectPrototypeProjection [], temporaryParams, {prototype := some 0}, emptyNullObject,
    ⟨[], some 0, true⟩, emptyNullObject, ⟨[], some 0, true⟩, emptyNullObject] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [objectPrototypeProjection, temporaryParams, newDataObject, emptyNullObject] at prototype <;>
    subst parent <;> decide

private theorem request_key_cases (request : Request) (member : request ∈ requests)
    (key : JSString) (used : key ∈ request.keys) : key = idKey ∨ key = secondKey := by
  change request ∈ [_, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change key ∈ [idKey, secondKey] at used
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using used
  · change key ∈ [idKey, secondKey] at used
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using used
  · change key ∈ [secondKey] at used
    exact Or.inr (by simpa using used)

private theorem domain : RegistrationHistoryLoop.Context initialized requests context 6 getKey (.object 3) 1 2 parameter node := by
  refine {
    ownerBinding := rfl, queryBinding := rfl, allBinding := rfl, parameterBinding := rfl, nodeBinding := rfl,
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩,
    closed := closed, rootDispatch := Or.inl rfl, nodeBound := by decide,
    parameterBound := ?_, capacity := by decide, keyBounds := ?_, reads := ?_, queries := ?_ }
  · intro reference equal
    have same : reference = 3 := (Value.object.inj equal).symm
    subst reference
    decide
  · intro request member
    change request ∈ [_, _, _] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide
  · intro request member key used
    rcases request_key_cases request member key used with rfl | rfl <;>
      exact ⟨.object 3 _ rfl, rfl⟩
  · intro request member
    change request ∈ [_, _, _] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, by decide, rfl⟩)
    · exact Or.inr (Or.inr ⟨by decide, by decide, rfl, rfl⟩)

private theorem five_reads : NodePrivateCall.FiveReads entry 7 6 getKey 1 (.object 3) :=
  ⟨rfl, rfl, rfl, rfl, .object 4, rfl, rfl⟩

/-- The general independent capture contract has a nonempty initialized/source
registration domain. The method receiver4 and registration target6 differ;
the installed source method is still shared by both instances. -/
theorem initialized_source_history_has_call_contract :
    ∃ after,
      (parsePrivateMethodCall NodePrivateCall.pinnedFiveSource NodePrivateCall.fiveBindings
        NodePrivateCall.classPrivateNames).map
        (fun call => runPrivateMethodCall 108 defaultSplitLimit secondTable ⟨.object 4⟩ call entry) =
          some (.ok (.undefined, after)) ∧
      NodePrivateCall.CallContract entry (NodePrivateCall.bodyState entry (closure moduleState.environment 1001) (.object 4)
        7 6 getKey 1 (.object 3)) [.object 8, .object 10, .object 12] getKey 7 .undefined after := by
  exact (parsed_history_five_satisfies initialized secondTable (closure moduleState.environment 1001)
    6 4 2 1001 2 2 0 requests caller getKey (.object 3) 1 parameter node seed callable
    ⟨⟨[], some 0, true⟩, rfl⟩ rfl five_reads domain).2.2

theorem source_registration_preserves_installed_handle :
    (parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames).map
      (fun source => runSourceHistory source 6 requests initialized) = some (.ok registered) ∧
    NodePrivateCall.Callable registered secondTable (closure moduleState.environment 1001) 4 2 ∧
    registered.heap[0]? = some [] ∧ registered.heap[2]? = some [.object 8, .object 10, .object 12] := by
  refine ⟨run_parsed_history initialized 6 1001 2 0 [] requests seed, ?_, ?_, ?_⟩
  · obtain ⟨object, found⟩ := seed.ownerFound
    refine ⟨callable.sourceProgram, ?_, callable.handleBound, callable.closureFound, ?_⟩
    · simpa [registered, end_functions] using callable.tableSeparate
    · simpa only [registered, privateGet, end_privates,
        end_old_object initialized 6 2 0 [] requests 4 (by decide)] using callable.privateRead
  · cbv
  · cbv

private structure Observation where
  returned : Value
  collector : Option (List Value)
  firstCapture : Except EvalError Value
  secondCapture : Except EvalError Value
  callerRestored : Bool
  privateFrames : Bool
  methodShared : Bool
  arraysSeparate : Bool
  foreignBrandRejected : Bool
  reservation : Nat × Nat × Nat
  deriving Repr

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state
  | .returned _ _ => .error .unsupported

private def equalReads : Except EvalError Value → Except EvalError Value → Bool
  | .ok a, .ok b => decide (a = b)
  | _, _ => false

private def differentArrays : Except EvalError Value → Except EvalError Value → Bool
  | .ok (.array a), .ok (.array b) => decide (a ≠ b)
  | _, _ => false

private def rejectsBrand : Except EvalError Value → Bool
  | .error .privateBrand => true
  | _ => false

/-- Explicit execution of parsed preamble, factory, two same-definition
instances, supplied-event registrations, real collector declaration and actual
five-argument source call. Temporary caller params remain an admitted input;
their production by surrounding search traversal is not assumed proved. -/
private def sourcePipeline : Option (Except EvalError Observation) := do
  let preamble ← parseBlock pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let collector ← parseBlock SearchEntry.pinnedCollectorSource []
  let call ← parsePrivateMethodCall NodePrivateCall.pinnedFiveSource NodePrivateCall.fiveBindings NodePrivateCall.classPrivateNames
  return do
    let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry before))
    let (first, next, table) ← match definePrivateClass fields [method] module
        (initialPrivateClassWorld module oldTable) oldTable with
      | some result => .ok result | none => .error .unsupported
    let (second, final, table) ← match definePrivateClass fields [method] module next table with
      | some result => .ok result | none => .error .unsupported
    let (root, one) ← instantiatePrivateClass 64 defaultSplitLimit first (some 0) module
    let (target, two) ← instantiatePrivateClass 64 defaultSplitLimit first (some 0) one
    let active := {two with privates := {two.privates with names := first.names}}
    let registered ← runSourceHistory push target requests active
    let callBefore ← normalState (← execute 32 defaultSplitLimit collector
      {registered with environment := withoutBindings caller ["handlerSets"]})
    let (returned, after) ← runPrivateMethodCall 108 defaultSplitLimit table ⟨.object root⟩ call callBefore
    return ⟨returned, after.heap[7]?,
      (getProperty propertyFuel after.objects 15 idKey).mapError .objectError,
      (getProperty propertyFuel after.objects 15 secondKey).mapError .objectError,
      decide (after.environment = callBefore.environment), decide (after.privates = callBefore.privates),
      equalReads (privateGet (.object root) "pushHandlerSets" active) (privateGet (.object target) "pushHandlerSets" active),
      differentArrays (privateGet (.object root) "methods" active) (privateGet (.object target) "methods" active),
      rejectsBrand (privateGet (.object root) "pushHandlerSets"
        {active with privates := {active.privates with names := second.names}}),
      (first.firstIdentity, final.nextIdentity, first.firstHandle)⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem source_initialized_registration_and_actual_call :
    sourcePipeline = some (.ok ⟨.undefined, some [.object 9, .object 11], .ok temp0, .ok temp1,
      true, true, true, true, true, (1001, 1013, 2)⟩) := by
  unfold sourcePipeline
  rw [parses_preamble, parses_fields, parses_method, NodeMethodsPush.parses_pinned_source,
    SearchEntry.parses_collector, NodePrivateCall.parses_five]
  cbv

end HonoLean.Upstream.NodeClass.Examples
