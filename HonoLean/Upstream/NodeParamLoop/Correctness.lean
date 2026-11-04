import HonoLean.Upstream.NodeParamLoop.Generated
import HonoLean.Upstream.NodeParamLoop.Setup
import HonoLean.Upstream.NodeParamLoop.Header
import HonoLean.Upstream.NodeParamLoop.Determinism

namespace HonoLean.Upstream.NodeParamLoop

set_option maxHeartbeats 1000000

open SourceSubset ECMA2025

def program : List Stmt :=
  [.assign allocation, .evaluate pushExpr, .countedFor initializers condition "i" body]
def bindings : List String :=
  ["handlerSet", "handlerSets", "params", "nodeParams", "createNullObject", "i", "len", "key", "Object"]

set_option maxRecDepth 32768 in
/-- Actual contiguous lines75–81, including helper invocation/push and the
complete counted loop. The containing method and raw handler lookup are outside. -/
theorem parses_pinned_source : parseBlock pinnedSource bindings = some program := by cbv

/-- Conditional normal chosen-handler domain. Snapshot read premises describe
one post-reset/push state, never future successful iterations or desired output.
Prototype closure and receiver bounds will establish their stability across
fresh-output writes. Nodup is awaiting the separate Set-producer source link. -/
structure Entry (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets keysArray : Nat) (priorHandlers : List Value) (parameterReceiver : Value)
    (nodeParams : ObjectRef) (snapshot : Snapshot) : Prop
    extends SetupFacts before handlerSet handler handlerSets priorHandlers where
  possibleKeys : handler.own.lookup possibleKeysKey = some (.data (.array keysArray) true true true)
  keysFound : before.heap[keysArray]? = some (snapshot.keys.map Value.string)
  arraysSeparate : handlerSets ≠ keysArray
  parameterBinding : before.environment.lookup "params" = some parameterReceiver
  nodeBinding : before.environment.lookup "nodeParams" = some (.object nodeParams)
  parameterBound : ∀ reference, parameterReceiver = .object reference → reference < before.objects.length
  nodeBound : nodeParams < before.objects.length
  unique : snapshot.keys.Nodup
  legalKeys : snapshot.keys.length ≤ 4294967295
  pushCapacity : priorHandlers.length < 4294967295
  reads : ∀ key ∈ snapshot.keys,
    NodeParamAssignment.ParameterRead (setupState before handlerSet handler handlerSets priorHandlers)
        key parameterReceiver (snapshot.parameter key) ∧
    getProperty propertyFuel (setupState before handlerSet handler handlerSets priorHandlers).objects
        nodeParams key = .ok (snapshot.node key)

/-- Local normalization helper; public endpoint remains the independent
Captured/Selected relation. This is not used to define the contract. -/
private def slotValue (parameter node : Value) (index : Int) : Value :=
  if truthy parameter && decide (index = 0) then parameter
  else if isNullish node then parameter else node

private theorem slotValue_selected (parameter node : Value) (index : Int) :
    NodeParamAssignment.Selected parameter node index (slotValue parameter node index) := by
  simp only [NodeParamAssignment.Selected, ← NodeParamAssignment.truthy_iff,
    ← NodeParamAssignment.isNullish_iff]
  cases parameterTruthy : truthy parameter <;> cases nodeNullish : isNullish node <;>
    by_cases zero : index = 0 <;>
    simp [slotValue, parameterTruthy, nodeNullish, zero, -truthy, -isNullish]

theorem reference_padded (extra limit : Nat) (state : State)
    (handlerSet output nodeParams : ObjectRef) (parameterReceiver : Value) (key : JSString) (index : Int)
    (context : NodeParamAssignment.LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet NodeParamAssignment.paramsKey = .ok (.object output)) :
    evalReference (extra + 31) limit NodeParamAssignment.assignment.target state =
      .ok (⟨.object output, .string key⟩, state) := by
  simp [NodeParamAssignment.assignment, evalReference, evalExpression, lookupVariable,
    context.handler, context.keyValue, handlerRead, readProperty, Except.mapError,
    bind, pure, Except.bind, Except.pure]

private theorem rhs_object_padded (extra limit : Nat) (state : State)
    (handlerSet parameterRef nodeParams : ObjectRef) (key : JSString) (index : Int) (parameter node : Value)
    (context : NodeParamAssignment.LocalBindings state handlerSet (.object parameterRef) nodeParams key index)
    (parameterRead : getProperty propertyFuel state.objects parameterRef key = .ok parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node) :
    evalExpression (extra + 31) limit NodeParamAssignment.assignment.value state =
      .ok (slotValue parameter node index, state) := by
  have truthyBoolean (value : Bool) : truthy (.boolean value) = value := rfl
  have truthyNumber (integer : Int) : truthy (.number integer) = decide (integer ≠ 0) := rfl
  have objectNotNullish (reference : ObjectRef) : isNullish (.object reference) = false := rfl
  cases parameterTruthy : truthy parameter <;> cases nodeNullish : isNullish node <;>
    by_cases zero : index = 0 <;>
    simp [NodeParamAssignment.assignment, evalExpression, lookupVariable, context.parameter, context.keyValue,
      context.node, context.iteration, parameterRead, nodeRead, readProperty, Except.mapError,
      slotValue, parameterTruthy, nodeNullish, zero, bind, pure, Except.bind, Except.pure,
      -truthy, -isNullish, truthyBoolean, truthyNumber, objectNotNullish]

private theorem rhs_nullish_padded (extra limit : Nat) (state : State)
    (handlerSet nodeParams : ObjectRef) (parameterReceiver : Value) (key : JSString) (index : Int) (node : Value)
    (context : NodeParamAssignment.LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (nullish : NodeParamAssignment.Nullish parameterReceiver)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node) :
    evalExpression (extra + 31) limit NodeParamAssignment.assignment.value state =
      .ok (slotValue .undefined node index, state) := by
  have nullishParameter := (NodeParamAssignment.isNullish_iff parameterReceiver).mpr nullish
  have undefinedFalsy : truthy .undefined = false := rfl
  cases nodeNullish : isNullish node <;>
    simp [NodeParamAssignment.assignment, evalExpression, lookupVariable, context.parameter, context.keyValue,
      context.node, nodeRead, readProperty, Except.mapError, slotValue, nullishParameter,
      undefinedFalsy, nodeNullish, bind, pure, Except.bind, Except.pure, -truthy, -isNullish]

private theorem rhs_padded (extra limit : Nat) (state : State)
    (handlerSet nodeParams : ObjectRef) (parameterReceiver : Value) (key : JSString) (index : Int) (parameter node : Value)
    (context : NodeParamAssignment.LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (parameterRead : NodeParamAssignment.ParameterRead state key parameterReceiver parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node) :
    evalExpression (extra + 31) limit NodeParamAssignment.assignment.value state =
      .ok (slotValue parameter node index, state) := by
  cases parameterRead with
  | object reference _ read =>
    exact rhs_object_padded extra limit state handlerSet reference nodeParams key index parameter node context read nodeRead
  | nullish _ missing =>
    exact rhs_nullish_padded extra limit state handlerSet nodeParams parameterReceiver key index node context missing nodeRead

theorem assignment_padded (extra limit : Nat) (state : State)
    (handlerSet output nodeParams : ObjectRef) (parameterReceiver : Value) (key : JSString) (index : Int)
    (parameter node : Value) (object : OrdinaryObject)
    (context : NodeParamAssignment.LocalBindings state handlerSet parameterReceiver nodeParams key index)
    (handlerRead : getProperty propertyFuel state.objects handlerSet NodeParamAssignment.paramsKey = .ok (.object output))
    (parameterRead : NodeParamAssignment.ParameterRead state key parameterReceiver parameter)
    (nodeRead : getProperty propertyFuel state.objects nodeParams key = .ok node)
    (found : state.objects[output]? = some object) (prototype : object.prototype = none)
    (absent : object.own.lookup key = none) (extensible : object.extensible = true) :
    executeAssignment (extra + 32) limit NodeParamAssignment.assignment state =
      .ok (slotValue parameter node index,
        {state with objects := state.objects.set output (newDataObject object key (slotValue parameter node index))}) := by
  simp only [executeAssignment, evalAssignmentReference, NodeParamAssignment.assignment]
  have captured := reference_padded extra limit state handlerSet output nodeParams parameterReceiver key index context handlerRead
  simp only [NodeParamAssignment.assignment] at captured
  simp only [Nat.add_assoc] at *
  rw [captured]
  simp only [bind, Except.bind, pure, Except.pure]
  have selected := rhs_padded extra limit state handlerSet nodeParams parameterReceiver key index parameter node context parameterRead nodeRead
  simp only [NodeParamAssignment.assignment] at selected
  rw [selected]
  have write := NodeParamAssignment.setProperty_null_framed state.objects output 31 object key
    (slotValue parameter node index) found prototype absent extensible
  change setProperty 32 state.objects output key (slotValue parameter node index) = _ at write
  simp [putAssignmentReference, putReference, propertyFuel, write, Except.mapError, bind, pure, Except.bind, Except.pure]

/-- Facts at the established post-reset/push state. The loop theorem derives
future reads from this one state and its closed existing-reference frame. -/
structure LoopFacts (base : State) (handlerSet output keysArray nodeParams : Nat)
    (parameterReceiver : Value) (snapshot : Snapshot) : Prop where
  handlerBinding : base.environment.lookup "handlerSet" = some (.object handlerSet)
  parameterBinding : base.environment.lookup "params" = some parameterReceiver
  nodeBinding : base.environment.lookup "nodeParams" = some (.object nodeParams)
  handlerParams : getProperty propertyFuel base.objects handlerSet NodeParamAssignment.paramsKey = .ok (.object output)
  handlerKeys : getProperty propertyFuel base.objects handlerSet possibleKeysKey = .ok (.array keysArray)
  keysFound : base.heap[keysArray]? = some (snapshot.keys.map Value.string)
  outputBound : output < base.objects.length
  outputEmpty : base.objects[output]? = some emptyNullObject
  handlerInside : handlerSet < output
  nodeInside : nodeParams < output
  parameterInside : ∀ reference, parameterReceiver = .object reference → reference < output
  closed : PrototypeClosed base.objects output
  reads : ∀ key ∈ snapshot.keys,
    NodeParamAssignment.ParameterRead base key parameterReceiver (snapshot.parameter key) ∧
    getProperty propertyFuel base.objects nodeParams key = .ok (snapshot.node key)
  unique : snapshot.keys.Nodup

theorem entry_loopFacts (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets keysArray : Nat) (priorHandlers : List Value) (parameterReceiver : Value)
    (nodeParams : ObjectRef) (snapshot : Snapshot)
    (entry : Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot) :
    LoopFacts (setupState before handlerSet handler handlerSets priorHandlers)
      handlerSet before.objects.length keysArray nodeParams parameterReceiver snapshot := by
  have handlerFound := setup_handler before handlerSet handler handlerSets priorHandlers entry.handlerFound
  have paramsRead : getProperty 32 (setupState before handlerSet handler handlerSets priorHandlers).objects
      handlerSet NodeParamAssignment.paramsKey = .ok (.object before.objects.length) :=
    getProperty_data _ _ 31 _ _ _ true true true handlerFound (putOwn_self _ _ _)
  have possibleLookup : (newDataObject handler NodeParamAssignment.paramsKey (.object before.objects.length)).own.lookup
      possibleKeysKey = some (.data (.array keysArray) true true true) := by
    rw [newDataObject, putOwn_other _ _ _ _ (by decide)]
    exact entry.possibleKeys
  have keysRead : getProperty 32 (setupState before handlerSet handler handlerSets priorHandlers).objects
      handlerSet possibleKeysKey = .ok (.array keysArray) :=
    getProperty_data _ _ 31 _ _ _ true true true handlerFound possibleLookup
  refine ⟨entry.handlerBinding, entry.parameterBinding, entry.nodeBinding, paramsRead, keysRead, ?_, ?_,
    setup_fresh_cell before handlerSet handler handlerSets priorHandlers, ?_, entry.nodeBound,
    entry.parameterBound, setup_prototype_closed before handlerSet handler handlerSets priorHandlers
      entry.handlerFound entry.closed, entry.reads, entry.unique⟩
  · rw [setup_heap_other before handlerSet handler handlerSets keysArray priorHandlers entry.arraysSeparate]
    exact entry.keysFound
  · rw [setup_length]
    exact Nat.lt_succ_self _
  · exact (List.getElem?_eq_some_iff.mp entry.handlerFound).1

theorem existing_read_after_output (base : State) (output : Nat) (object : OrdinaryObject)
    (closed : PrototypeClosed base.objects output) (reference : Nat) (inside : reference < output)
    (key : JSString) :
    getProperty propertyFuel (base.objects.set output object) reference key =
      getProperty propertyFuel base.objects reference key := by
  apply Eq.symm
  apply getProperty_frame propertyFuel base.objects (base.objects.set output object) output
  · intro other bound
    exact (List.getElem?_set_ne (Ne.symm (Nat.ne_of_lt bound))).symm
  · exact closed
  · exact inside

theorem parameter_read_after_output (base current : State) (output : Nat) (object : OrdinaryObject)
    (sameObjects : current.objects = base.objects.set output object)
    (closed : PrototypeClosed base.objects output) (receiver parameter : Value) (key : JSString)
    (inside : ∀ reference, receiver = .object reference → reference < output)
    (read : NodeParamAssignment.ParameterRead base key receiver parameter) :
    NodeParamAssignment.ParameterRead current key receiver parameter := by
  cases read with
  | object reference _ found =>
    apply NodeParamAssignment.ParameterRead.object reference parameter
    rw [sameObjects, existing_read_after_output base output object closed reference (inside reference rfl) key]
    exact found
  | nullish _ missing => exact .nullish receiver missing

def loopState (base : State) (output count length : Nat) (object : OrdinaryObject) : State :=
  {base with
    environment := headerEnvironment base.environment count length
    objects := base.objects.set output object}

def bodyStart (base : State) (output count length : Nat) (object : OrdinaryObject) : State :=
  let state := loopState base output count length object
  {state with environment := withoutBindings state.environment ["key"]}

def bodySlot (base : State) (output count length : Nat) (object : OrdinaryObject) (key : JSString) : State :=
  {loopState base output count length object with environment := bodyEnvironment base.environment count length key}

theorem loop_output_found (base : State) (output count length : Nat) (object : OrdinaryObject)
    (inside : output < base.objects.length) :
    (loopState base output count length object).objects[output]? = some object :=
  List.getElem?_set_self inside

theorem body_context (base : State) (handlerSet output keysArray nodeParams count : Nat)
    (parameterReceiver : Value) (snapshot : Snapshot) (object : OrdinaryObject) (key : JSString)
    (facts : LoopFacts base handlerSet output keysArray nodeParams parameterReceiver snapshot) :
    NodeParamAssignment.LocalBindings (bodySlot base output count snapshot.keys.length object key)
      handlerSet parameterReceiver nodeParams key (count : Int) := by
  constructor
  · change (bodyEnvironment base.environment count snapshot.keys.length key).lookup "handlerSet" = _
    rw [body_lookup_other _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact facts.handlerBinding
  · exact body_lookup_key _ _ _ _
  · change (bodyEnvironment base.environment count snapshot.keys.length key).lookup "params" = _
    rw [body_lookup_other _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact facts.parameterBinding
  · change (bodyEnvironment base.environment count snapshot.keys.length key).lookup "nodeParams" = _
    rw [body_lookup_other _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact facts.nodeBinding
  · exact body_lookup_i _ _ _ _

theorem execute_body (extra limit : Nat) (base : State)
    (handlerSet output keysArray nodeParams count : Nat) (parameterReceiver : Value)
    (snapshot : Snapshot) (object : OrdinaryObject) (key : JSString)
    (facts : LoopFacts base handlerSet output keysArray nodeParams parameterReceiver snapshot)
    (invariant : Prefix snapshot count object) (atKey : snapshot.keys[count]? = some key) :
    execute (extra + 61) limit body (bodyStart base output count snapshot.keys.length object) =
      .ok (.normal (bodySlot base output count snapshot.keys.length
        (newDataObject object key (slotValue (snapshot.parameter key) (snapshot.node key) (count : Int))) key)) := by
  have member := List.mem_of_getElem? atKey
  have stableHandler : getProperty propertyFuel (bodyStart base output count snapshot.keys.length object).objects
      handlerSet possibleKeysKey = .ok (.array keysArray) := by
    rw [show (bodyStart base output count snapshot.keys.length object).objects = base.objects.set output object from rfl,
      existing_read_after_output base output object facts.closed handlerSet facts.handlerInside possibleKeysKey]
    exact facts.handlerKeys
  have startHandler : (bodyStart base output count snapshot.keys.length object).environment.lookup "handlerSet" =
      some (.object handlerSet) := by
    rw [show (bodyStart base output count snapshot.keys.length object).environment =
      withoutBindings (headerEnvironment base.environment count snapshot.keys.length) ["key"] from rfl,
      lookup_withoutBindings _ _ _ (by decide), header_lookup_other _ _ _ _ (by decide) (by decide)]
    exact facts.handlerBinding
  have startIndex : (bodyStart base output count snapshot.keys.length object).environment.lookup "i" =
      some (.number (Int.ofNat count)) := by
    rw [show (bodyStart base output count snapshot.keys.length object).environment =
      withoutBindings (headerEnvironment base.environment count snapshot.keys.length) ["key"] from rfl,
      lookup_withoutBindings _ _ _ (by decide), header_lookup_i]
  have keyEval := eval_current_key (extra + 56) limit (bodyStart base output count snapshot.keys.length object)
    handlerSet keysArray count snapshot.keys key startHandler startIndex stableHandler facts.keysFound atKey
  have context := body_context base handlerSet output keysArray nodeParams count parameterReceiver snapshot object key facts
  have handlerRead : getProperty propertyFuel (bodySlot base output count snapshot.keys.length object key).objects
      handlerSet NodeParamAssignment.paramsKey = .ok (.object output) := by
    rw [show (bodySlot base output count snapshot.keys.length object key).objects = base.objects.set output object from rfl,
      existing_read_after_output base output object facts.closed handlerSet facts.handlerInside NodeParamAssignment.paramsKey]
    exact facts.handlerParams
  have parameterRead := parameter_read_after_output base (bodySlot base output count snapshot.keys.length object key)
    output object rfl facts.closed parameterReceiver (snapshot.parameter key) key facts.parameterInside (facts.reads key member).1
  have nodeRead : getProperty propertyFuel (bodySlot base output count snapshot.keys.length object key).objects
      nodeParams key = .ok (snapshot.node key) := by
    rw [show (bodySlot base output count snapshot.keys.length object key).objects = base.objects.set output object from rfl,
      existing_read_after_output base output object facts.closed nodeParams facts.nodeInside key]
    exact (facts.reads key member).2
  have assigned := assignment_padded (extra + 27) limit (bodySlot base output count snapshot.keys.length object key)
    handlerSet output nodeParams parameterReceiver key (count : Int) (snapshot.parameter key) (snapshot.node key) object
    context handlerRead parameterRead nodeRead (loop_output_found base output count snapshot.keys.length object facts.outputBound)
    (prefix_null_extensible invariant).1 (prefix_next_absent invariant facts.unique key atKey)
    (prefix_null_extensible invariant).2
  simp only [body, execute]
  rw [keyEval]
  simp only [bind, Except.bind]
  change (do
    let (_, state) ← executeAssignment (extra + 59) limit NodeParamAssignment.assignment
      (bodySlot base output count snapshot.keys.length object key)
    execute (extra + 59) limit [] state) = _
  rw [assigned]
  simp [execute, bodySlot, loopState, bodyEnvironment, bind, Except.bind, List.set_set]

/-- The actual tested counter, condition, key read, body scope and increment
execute every remaining slot. Fuel grows with key count; no fixed32 cap or
assumed iteration trace is used. -/
theorem execute_iterations (remaining limit : Nat) (base : State)
    (handlerSet output keysArray nodeParams count : Nat) (parameterReceiver : Value)
    (snapshot : Snapshot) (object : OrdinaryObject)
    (facts : LoopFacts base handlerSet output keysArray nodeParams parameterReceiver snapshot)
    (invariant : Prefix snapshot count object) (total : count + remaining = snapshot.keys.length) :
    ∃ finalObject, Prefix snapshot snapshot.keys.length finalObject ∧
      executeFor (remaining + 61) limit condition "i" body
        (loopState base output count snapshot.keys.length object) =
        .ok (.normal (loopState base output snapshot.keys.length snapshot.keys.length finalObject)) := by
  induction remaining generalizing count object with
  | zero =>
    have done : count = snapshot.keys.length := by omega
    subst count
    refine ⟨object, invariant, ?_⟩
    rw [executeFor, eval_condition 57 limit _ base.environment snapshot.keys.length snapshot.keys.length rfl]
    simp [truthy, bind, pure, Except.bind, Except.pure]
  | succ remaining ih =>
    have beforeEnd : count < snapshot.keys.length := by omega
    let key := snapshot.keys[count]'beforeEnd
    have atKey : snapshot.keys[count]? = some key := by simp [key]
    let nextObject := newDataObject object key (slotValue (snapshot.parameter key) (snapshot.node key) (count : Int))
    have nextPrefix : Prefix snapshot (count + 1) nextObject :=
      prefix_step invariant facts.unique key _ atKey (slotValue_selected _ _ _)
    obtain ⟨finalObject, finalPrefix, iterated⟩ := ih (count + 1) nextObject nextPrefix (by omega)
    refine ⟨finalObject, finalPrefix, ?_⟩
    rw [executeFor, eval_condition (remaining + 58) limit _ base.environment count snapshot.keys.length rfl]
    simp only [bind, Except.bind, truthy, beforeEnd, decide_true, ↓reduceIte]
    change (do
      let completion ← execute (remaining + 61) limit body (bodyStart base output count snapshot.keys.length object)
      match restoreCompletion (headerEnvironment base.environment count snapshot.keys.length) completion with
      | .returned value state => pure (Completion.returned value state)
      | .normal state => do
        let state ← incrementVariable "i" state
        executeFor (remaining + 61) limit condition "i" body state) = _
    rw [execute_body remaining limit base handlerSet output keysArray nodeParams count parameterReceiver snapshot object
      key facts invariant atKey]
    simp only [bind, Except.bind, restoreCompletion]
    change (do
      let state ← incrementVariable "i" (loopState base output count snapshot.keys.length nextObject)
      executeFor (remaining + 61) limit condition "i" body state) = _
    rw [increment_header _ base.environment count snapshot.keys.length rfl]
    simp only [bind, Except.bind]
    exact iterated

/-- The same key-prefix argument with arbitrary extra evaluation fuel. This
permits the actual block to run beneath larger enclosing source loops without
assuming successful future evaluations or changing its captured observations. -/
theorem execute_iterations_padded (extra remaining limit : Nat) (base : State)
    (handlerSet output keysArray nodeParams count : Nat) (parameterReceiver : Value)
    (snapshot : Snapshot) (object : OrdinaryObject)
    (facts : LoopFacts base handlerSet output keysArray nodeParams parameterReceiver snapshot)
    (invariant : Prefix snapshot count object) (total : count + remaining = snapshot.keys.length) :
    ∃ finalObject, Prefix snapshot snapshot.keys.length finalObject ∧
      executeFor (extra + remaining + 61) limit condition "i" body
        (loopState base output count snapshot.keys.length object) =
        .ok (.normal (loopState base output snapshot.keys.length snapshot.keys.length finalObject)) := by
  induction remaining generalizing count object with
  | zero =>
    have done : count = snapshot.keys.length := by omega
    subst count
    refine ⟨object, invariant, ?_⟩
    rw [show extra + 0 + 61 = (extra + 60) + 1 by omega, executeFor]
    rw [eval_condition (extra + 57) limit _ base.environment snapshot.keys.length snapshot.keys.length rfl]
    simp [truthy, bind, pure, Except.bind, Except.pure]
  | succ remaining ih =>
    have beforeEnd : count < snapshot.keys.length := by omega
    let key := snapshot.keys[count]'beforeEnd
    have atKey : snapshot.keys[count]? = some key := by simp [key]
    let nextObject := newDataObject object key (slotValue (snapshot.parameter key) (snapshot.node key) (count : Int))
    have nextPrefix : Prefix snapshot (count + 1) nextObject :=
      prefix_step invariant facts.unique key _ atKey (slotValue_selected _ _ _)
    obtain ⟨finalObject, finalPrefix, iterated⟩ := ih (count + 1) nextObject nextPrefix (by omega)
    refine ⟨finalObject, finalPrefix, ?_⟩
    rw [show extra + (remaining + 1) + 61 = (extra + remaining + 61) + 1 by omega, executeFor]
    rw [eval_condition (extra + remaining + 58) limit _ base.environment count snapshot.keys.length rfl]
    simp only [bind, Except.bind, truthy, beforeEnd, decide_true, ↓reduceIte]
    change (do
      let completion ← execute (extra + remaining + 61) limit body (bodyStart base output count snapshot.keys.length object)
      match restoreCompletion (headerEnvironment base.environment count snapshot.keys.length) completion with
      | .returned value state => pure (Completion.returned value state)
      | .normal state => do
        let state ← incrementVariable "i" state
        executeFor (extra + remaining + 61) limit condition "i" body state) = _
    rw [execute_body (extra + remaining) limit base handlerSet output keysArray nodeParams count parameterReceiver snapshot object
      key facts invariant atKey]
    simp only [bind, Except.bind, restoreCompletion]
    change (do
      let state ← incrementVariable "i" (loopState base output count snapshot.keys.length nextObject)
      executeFor (extra + remaining + 61) limit condition "i" body state) = _
    rw [increment_header _ base.environment count snapshot.keys.length rfl]
    simp only [bind, Except.bind]
    exact iterated

theorem loopState_empty (base : State) (output length : Nat)
    (empty : base.objects[output]? = some emptyNullObject) :
    loopState base output 0 length emptyNullObject =
      {base with environment := headerEnvironment base.environment 0 length} := by
  obtain ⟨inside, equal⟩ := List.getElem?_eq_some_iff.mp empty
  have unchanged : base.objects.set output emptyNullObject = base.objects := by
    rw [← equal, List.set_getElem_self inside]
  simp [loopState, unchanged]

theorem execute_counted_loop (limit : Nat) (base : State)
    (handlerSet output keysArray nodeParams : Nat) (parameterReceiver : Value) (snapshot : Snapshot)
    (facts : LoopFacts base handlerSet output keysArray nodeParams parameterReceiver snapshot) :
    ∃ finalObject, Prefix snapshot snapshot.keys.length finalObject ∧
      execute (snapshot.keys.length + 62) limit [.countedFor initializers condition "i" body] base =
        .ok (.normal {base with objects := base.objects.set output finalObject}) := by
  obtain ⟨finalObject, complete, iterated⟩ := execute_iterations snapshot.keys.length limit base
    handlerSet output keysArray nodeParams 0 parameterReceiver snapshot emptyNullObject facts
    (prefix_empty snapshot) (by omega)
  refine ⟨finalObject, complete, ?_⟩
  have initialized := initialize_header (snapshot.keys.length + 53) limit base handlerSet keysArray snapshot.keys
    facts.handlerBinding facts.handlerKeys facts.keysFound
  rw [execute]
  change (do
    let state ← initializeBindings (snapshot.keys.length + 61) limit initializers
      {base with environment := withoutBindings base.environment ["i", "len"]}
    let completion ← executeFor (snapshot.keys.length + 61) limit condition "i" body state
    match restoreCompletion base.environment completion with
    | .normal state => execute (snapshot.keys.length + 61) limit [] state
    | .returned value state => pure (Completion.returned value state)) = _
  rw [initialized]
  simp only [bind, Except.bind]
  rw [← loopState_empty base output snapshot.keys.length facts.outputEmpty, iterated]
  simp [restoreCompletion, execute, loopState]

/-- Universal normal-completion result for the actual parsed block. Key count
determines a sufficient budget, and the source establishes fresh reset/append
and all prefix facts. Only the external selected-handler/domain/read/unique-key
premises are assumed; neither a desired endpoint nor a successful trace is. -/
theorem parsed_source_satisfies (before : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets keysArray : Nat) (priorHandlers : List Value) (parameterReceiver : Value)
    (nodeParams : ObjectRef) (snapshot : Snapshot)
    (entry : Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot) :
    ∃ after,
      (parseBlock pinnedSource bindings).map (fun source => runBlock (snapshot.keys.length + 64) source before) =
        some (.ok (.normal after)) ∧
      BlockContract before after handlerSet handler handlerSets priorHandlers snapshot := by
  let base := setupState before handlerSet handler handlerSets priorHandlers
  have facts := entry_loopFacts before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot entry
  obtain ⟨finalObject, complete, executed⟩ := execute_counted_loop defaultSplitLimit base
    handlerSet before.objects.length keysArray nodeParams parameterReceiver snapshot facts
  let after := {base with objects := base.objects.set before.objects.length finalObject}
  refine ⟨after, ?_, finalObject, complete, rfl⟩
  have filtered : before.environment.filter (fun _ => true) = before.environment :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  rw [parses_pinned_source, Option.map_some]
  simp only [runBlock, program, declaredNames, List.filterMap_cons, List.filterMap_nil,
    withoutBindings, List.contains_nil, Bool.not_false, filtered]
  rw [execute_leading (snapshot.keys.length + 52) defaultSplitLimit _ before handlerSet handler handlerSets priorHandlers entry.toSetupFacts]
  rw [executed]
  simp [restoreCompletion, after, base, setupState, resetState, bind, pure, Except.bind, Except.pure]

/-- The independent endpoint relation characterizes execution of the pinned
seven-line source block on the declared conditional domain. Set-producer and
whole-Node reachability/handler-selection/native-adequacy obligations remain. -/
theorem parsed_source_correct (before after : State) (handlerSet : ObjectRef) (handler : OrdinaryObject)
    (handlerSets keysArray : Nat) (priorHandlers : List Value) (parameterReceiver : Value)
    (nodeParams : ObjectRef) (snapshot : Snapshot)
    (entry : Entry before handlerSet handler handlerSets keysArray priorHandlers parameterReceiver nodeParams snapshot) :
    (parseBlock pinnedSource bindings).map (fun source => runBlock (snapshot.keys.length + 64) source before) =
      some (.ok (.normal after)) ↔
      BlockContract before after handlerSet handler handlerSets priorHandlers snapshot := by
  obtain ⟨completed, execution, contract⟩ := parsed_source_satisfies before handlerSet handler handlerSets keysArray
    priorHandlers parameterReceiver nodeParams snapshot entry
  constructor
  · intro observed
    rw [execution] at observed
    simp only [Option.some.injEq, Except.ok.injEq, Completion.normal.injEq] at observed
    exact observed ▸ contract
  · intro desired
    have equal := block_contract_unique before completed after handlerSet handler handlerSets priorHandlers snapshot contract desired
    rw [← equal]
    exact execution

/-- info: 'HonoLean.Upstream.NodeParamLoop.parsed_source_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parsed_source_correct

end HonoLean.Upstream.NodeParamLoop
