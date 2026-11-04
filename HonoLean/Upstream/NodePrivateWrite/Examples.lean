import HonoLean.Upstream.NodePrivateWrite.Flow
import HonoLean.Upstream.NodeClass.History

namespace HonoLean.Upstream.NodePrivateWrite.Examples

open SourceSubset ECMA2025 RegistrationHistory

private def getKey : JSString := [71, 69, 84]
private def postKey : JSString := [80, 79, 83, 84]
private def idKey : JSString := [105, 100]
private def nameKey : JSString := [110, 97, 109, 101]
private def old0 : Value := .string [111, 108, 100, 48]
private def old1 : Value := .string [111, 108, 100, 49]
private def oldParams : OrdinaryObject := newDataObject (newDataObject emptyNullObject idKey old0) nameKey old1
private def before : State :=
  {environment := [("createNullObject", .function 0), ("METHOD_NAME_ALL", .string SearchEntry.allKey)],
   objects := [objectPrototypeProjection [], oldParams, emptyNullObject],
   functions := [⟨CreateNullObject.createProgram, []⟩]}
private def moduleState : State := NodeInitialization.preambleState before
private def definition : SelectedPrivateClass := NodeClass.definition moduleState.environment 1 1
private def table : PrivateMethodTable := NodeClass.extendedTable ⟨1, []⟩ moduleState.environment 1
private def one : State := NodeClass.instanceState moduleState (some 0) moduleState.environment 1 1 (.object 3)
private def two : State := NodeClass.instanceState one (some 0) moduleState.environment 1 1 (.object 3)
private def three : State := NodeClass.instanceState two (some 0) moduleState.environment 1 1 (.object 3)
private def initialized : State := NodeClass.classActivation three 1
private def requests : List Request :=
  [⟨getKey, .number 10, [idKey, nameKey, idKey]⟩,
   ⟨SearchEntry.allKey, .number 11, [idKey, nameKey]⟩,
   ⟨postKey, .number 12, [nameKey]⟩]
private def registered : State := endState initialized 8 4 0 [] requests
private def caller : List (String × Value) :=
  [("node", .object 6), ("nextNode", .object 8), ("child", .object 6),
   ("method", .string getKey), ("params", .object 1), ("emptyParams", .object 3)]
private def entry : State := {NodeClass.callEntry registered caller with thisValue := .object 4}
private def resetState : State := writePrivateDataState entry 4 5 (.object 3)
private def parentWritten : State := writePrivateDataState resetState 6 5 (.object 1)

private theorem seed : Seed initialized 8 1 4 0 [] := by
  exact ⟨rfl, ⟨objectPrototypeProjection [], rfl⟩, ⟨⟨[], some 0, true⟩, rfl⟩,
    rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl⟩

private theorem rootWritable : Writable entry 4 5 (.object 3) := by
  exact ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
private theorem parentWritable : Writable resetState 6 5 (.object 3) := by
  exact ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩
private theorem targetWritable : Writable parentWritten 8 5 (.object 3) := by
  exact ⟨rfl, ⟨⟨[], some 0, true⟩, rfl⟩, by refine ⟨_, rfl, ?_⟩; rfl⟩

theorem source_reset_and_earlier_parameter_write :
    (parseAssignment pinnedResetSource resetBindings NodePrivateCall.classPrivateNames true).map
      (fun assignment => executeAssignment 32 defaultSplitLimit assignment entry) = some (.ok (.object 3, resetState)) ∧
    (parseAssignment pinnedParameterSource parameterBindings NodePrivateCall.classPrivateNames).map
      (fun assignment => executeAssignment 32 defaultSplitLimit assignment resetState) = some (.ok (.object 1, parentWritten)) ∧
    privateGet (.object 6) "params" parentWritten = .ok (.object 1) := by
  rw [parses_reset, parses_parameter]
  cbv

private def node : JSString → Value := fun key => if key = idKey then old0 else old1
private def methodContext : List (String × Value) := NodeClass.methodContext (NodeClass.closure moduleState.environment 1)
  8 getKey 1 .undefined

private theorem closed : NodeParamLoop.PrototypeClosed initialized.objects initialized.objects.length := by
  intro reference _ object found parent prototype
  have member := List.mem_of_getElem? found
  change object ∈ [objectPrototypeProjection [], oldParams, emptyNullObject, emptyNullObject,
    ⟨[], some 0, true⟩, emptyNullObject, ⟨[], some 0, true⟩, emptyNullObject,
    ⟨[], some 0, true⟩, emptyNullObject] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [objectPrototypeProjection, oldParams, newDataObject, emptyNullObject] at prototype <;>
    subst parent <;> decide

private theorem request_keys (request : Request) (member : request ∈ requests)
    (key : JSString) (used : key ∈ request.keys) : key = idKey ∨ key = nameKey := by
  change request ∈ [_, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change key ∈ [idKey, nameKey] at used
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using used
  · change key ∈ [idKey, nameKey] at used
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using used
  · change key ∈ [nameKey] at used
    exact Or.inr (by simpa using used)

private theorem domain : RegistrationHistoryLoop.Context initialized requests methodContext 8 getKey .undefined 1 2
    (fun _ => .undefined) node := by
  refine {
    ownerBinding := rfl, queryBinding := rfl, allBinding := rfl, parameterBinding := rfl, nodeBinding := rfl,
    helper := ⟨0, [], rfl, rfl, Or.inl rfl⟩, closed := closed, rootDispatch := Or.inl rfl,
    nodeBound := by decide, parameterBound := ?_, capacity := by decide, keyBounds := ?_, reads := ?_, queries := ?_ }
  · intro reference equal; cases equal
  · intro request member
    change request ∈ [_, _, _] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide
  · intro request member key used
    rcases request_keys request member key used with rfl | rfl <;> exact ⟨.nullish _ (Or.inr rfl), rfl⟩
  · intro request member
    change request ∈ [_, _, _] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, by decide, rfl⟩)
    · exact Or.inr (Or.inr ⟨by decide, by decide, rfl, rfl⟩)

private theorem callLayout : MethodsLoopInitial.Layout
    (NodePrivateCall.bodyState parentWritten (NodeClass.closure moduleState.environment 1) (.object 4) 9 8 getKey 1 .undefined)
    [.object 10, .object 12, .object 14] getKey 9 2
    (RegistrationHistoryLoop.storedRecords 10 6 0 requests (fun _ => .undefined) node) .undefined 1 [] := by
  have layout := RegistrationHistoryLoop.parsed_history_layout initialized 8 1 4 0 requests caller methodContext
    getKey .undefined 1 2 (fun _ => .undefined) node seed domain
  exact layout_frame layout rfl rfl rfl rfl

/-- The current literal-child propagation109 and actual call115 have a nonempty
contract domain. The earlier202 write used a separate explicit activation; this
does not assert traversal reachability or a contiguous202-to191 branch. -/
theorem source_propagation_has_call_contract :
    ∃ after,
      (parsePrivateMethodCall NodePrivateCall.pinnedFourSource NodePrivateCall.fourBindings NodePrivateCall.classPrivateNames).map
        (fun call => runPrivateMethodCall 108 defaultSplitLimit table ⟨.object 4⟩ call
          (writePrivateDataState parentWritten 8 5 (.object 1))) = some (.ok (.undefined, after)) ∧
      NodePrivateCall.CallContract (writePrivateDataState parentWritten 8 5 (.object 1))
        (NodePrivateCall.bodyState (writePrivateDataState parentWritten 8 5 (.object 1))
          (NodeClass.closure moduleState.environment 1) (.object 4) 9 8 getKey 1 .undefined)
        [.object 10, .object 12, .object 14] getKey 9 .undefined after := by
  exact (parsed_propagation_four_satisfies parentWritten table (NodeClass.closure moduleState.environment 1)
    8 6 4 1 1 4 9 2 [.object 10, .object 12, .object 14] getKey 1 (.object 3)
    (RegistrationHistoryLoop.storedRecords 10 6 0 requests (fun _ => .undefined) node) [] rfl targetWritable
    ⟨rfl, by decide, by decide, rfl, rfl⟩
    ⟨⟨⟨[], some 0, true⟩, rfl⟩, rfl, by refine ⟨_, rfl, ?_⟩; rfl, rfl, by decide, by decide⟩
    rfl rfl rfl rfl rfl callLayout).2

private def normalState : Completion → Except EvalError State
  | .normal state => .ok state | _ => .error .unsupported
private def tagAt (state : State) (owner identity : Nat) : Option PrivateElement :=
  (state.privates.elements.lookup owner).bind (fun fields => fields.lookup identity)
private def readonly : Except EvalError State → Bool
  | .error .privateReadOnly => true | _ => false

private def sourcePipeline : Option (Except EvalError (Value × Option (List Value) × Except ObjectError Value × Except ObjectError Value × Bool × Bool × Bool)) := do
  let preamble ← parseBlock NodeClass.pinnedPreambleSource ["createNullObject"]
  let fields ← parsePrivateFields NodeClass.pinnedFieldsSource ["createNullObject", "emptyParams"]
  let method ← parsePrivateMethod NodeClass.pinnedMethodSource NodePrivateCall.lexicalBindings NodePrivateCall.classPrivateNames
  let collector ← parseBlock SearchEntry.pinnedCollectorSource []
  let resetSource ← parseAssignment pinnedResetSource resetBindings NodePrivateCall.classPrivateNames true
  let earlier ← parseAssignment pinnedParameterSource parameterBindings NodePrivateCall.classPrivateNames
  let propagate ← parseAssignment pinnedPropagationSource propagationBindings NodePrivateCall.classPrivateNames
  let push ← parseExpression NodeMethodsPush.pinnedSource NodeMethodsPush.bindings NodeMethodsPush.privateNames
  let call ← parsePrivateMethodCall NodePrivateCall.pinnedFourSource NodePrivateCall.fourBindings NodePrivateCall.classPrivateNames
  return do
    let module ← normalState (← execute 32 defaultSplitLimit preamble (NodeInitialization.preambleEntry before))
    let (definition, _, table) ← match definePrivateClass fields [method] module (initialPrivateClassWorld module ⟨1, []⟩) ⟨1, []⟩ with
      | some x => .ok x | none => .error .unsupported
    let (root, first) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) module
    let (parent, second) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) first
    let (target, third) ← instantiatePrivateClass 64 defaultSplitLimit definition (some 0) second
    let active := {third with privates := {third.privates with names := definition.names}}
    let registered ← runSourceHistory push target requests active
    let sourceCaller := [("node", .object parent), ("nextNode", .object target), ("child", .object parent),
      ("method", .string getKey), ("params", .object 1), ("emptyParams", .object before.objects.length)]
    let start := {registered with environment := sourceCaller, thisValue := .object root}
    let collected ← normalState (← execute 32 defaultSplitLimit collector start)
    let (_, reset) ← executeAssignment 32 defaultSplitLimit resetSource collected
    -- The earlier parameter-continuation entry and the later literal entry
    -- have separate supplied lexical activations; their traversal link is open.
    let previous := {reset with environment := ("node", .object root) :: withoutBindings reset.environment ["node"]}
    let (_, prepared) ← executeAssignment 32 defaultSplitLimit earlier previous
    let current := {prepared with environment := reset.environment}
    let (_, propagated) ← executeAssignment 32 defaultSplitLimit propagate current
    let (returned, after) ← runPrivateMethodCall 108 defaultSplitLimit table ⟨.object root⟩ call propagated
    let firstCapture := getProperty propertyFuel after.objects 16 idKey
    let secondCapture := getProperty propertyFuel after.objects 16 nameKey
    return (returned, after.heap[9]?, firstCapture, secondCapture,
      decide (tagAt after target 5 = some (.data (.object 1))),
      readonly (privateSet (.object root) 6 .null after),
      decide (after.environment = propagated.environment) && decide (after.thisValue = propagated.thisValue))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
/-- Every private slot write here executes parsed source. Old parameter values
are an explicit input object; no private params slot is manually staged. -/
theorem source_initialized_writes_and_actual_call :
    sourcePipeline = some (.ok (.undefined, some [.object 11, .object 13], .ok old0, .ok old1, true, true, true)) := by
  simp only [sourcePipeline, NodeClass.parses_preamble, NodeClass.parses_fields, NodeClass.parses_method,
    SearchEntry.parses_collector, parses_reset, parses_parameter, parses_propagation,
    NodeMethodsPush.parses_pinned_source, NodePrivateCall.parses_four]
  cbv

end HonoLean.Upstream.NodePrivateWrite.Examples
