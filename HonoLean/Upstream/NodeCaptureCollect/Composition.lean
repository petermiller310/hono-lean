import HonoLean.Upstream.NodeCaptureCollect.Correctness

set_option autoImplicit false
namespace HonoLean.Upstream.NodeCaptureCollect
open SourceSubset ECMA2025 MethodsLoopInitial

/-- Facts at the entry BEFORE123, with no generated params binding required or future read matrix.
Only initial parent Gets and root descriptor paths are recorded. The actual
initializer and guard will determine q's own properties and read values. -/
structure EntryInputs (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent keyBound : Nat)
    (rows initial : List Value) (query : JSString) (records : List Record) (root : JSString → Value) : Prop where
  installed : Nonempty (Installed before table closure receiver handle)
  thisValue : before.thisValue = .object receiver
  collectorBinding : before.environment.lookup "handlerSets" = some (.array collector)
  childBinding : before.environment.lookup "child" = some (.object child)
  methodBinding : before.environment.lookup "method" = some (.string query)
  nodeBinding : before.environment.lookup "node" = some (.object node)
  parentData : NodePrivateWrite.Writable before node parentIdentity (.object parent)
  stored : Storage before closure child slot methods collector rows
  frame : TwoSourceFrame before closure.environment rows query collector keyBound records initial
  parentProtected : Protected before records parent
  rootProtected : Protected before records 0
  parentReads : ParentReads before records parent
  rootReads : RootReads before records root

theorem fresh_map_get (before : State) (object : OrdinaryObject) (key : JSString) (value : Value)
    (ready : SpreadTargetReady object) (prototype : object.prototype = some 0)
    (descriptor : Option PropertyDescriptor) (depth : Nat)
    (path : NodeCaptureGuard.DescriptorPath before.objects key 0 descriptor depth)
    (bound : depth + 1 ≤ propertyFuel) (inherited : FreshInherited descriptor value) :
    getProperty propertyFuel (NodeParamsInit.mapState before object).objects before.objects.length key = .ok (mapValue object (fun _ => value) key) := by
  have found : (NodeParamsInit.mapState before object).objects[before.objects.length]? = some object := by simp [NodeParamsInit.mapState]
  cases own : object.own.lookup key with
  | some descriptor =>
    obtain ⟨stored, rfl⟩ := ready.ownData key descriptor own
    simpa [mapValue, own, propertyFuel] using getProperty_data _ _ (propertyFuel - 1) key object stored true true true found own
  | none =>
    have resolved := NodeCaptureGuard.descriptor_path_lookup _ _ _ _ _ (propertyFuel - 1)
      (NodeCaptureGuard.descriptor_path_append before.objects [object] key 0 descriptor depth path) (by omega)
    have lookup : lookupProperty propertyFuel (NodeParamsInit.mapState before object).objects before.objects.length key = .ok descriptor := by
      change lookupProperty (31 + 1) _ _ _ = _
      rw [lookupProperty, found]
      dsimp only
      rw [own]
      dsimp only
      rw [prototype]
      exact resolved
    cases inherited <;> simp [mapValue, own, getProperty, lookup, callGetter, found, prototype, bind, Except.bind, pure, Except.pure]

theorem fresh_map_sources (before : State) (object : OrdinaryObject) (closure : PrivateMethodClosure)
    (rows initial : List Value) (query : JSString) (collector keyBound parent : Nat) (records : List Record) (root : JSString → Value)
    (frame : TwoSourceFrame before closure.environment rows query collector keyBound records initial)
    (parentProtected : Protected before records parent) (rootProtected : Protected before records 0)
    (parentReads : ParentReads before records parent) (rootReads : RootReads before records root)
    (ready : SpreadTargetReady object) (prototype : object.prototype = some 0) :
    TwoSource (NodeParamsInit.mapState before object) closure.environment rows query collector keyBound (readRecords records object root)
      parent (.object before.objects.length) initial := by
  let after := NodeParamsInit.mapState before object
  have objects : after.objects = before.objects ++ [object] := rfl
  have oldObjects : ∀ reference, reference < before.objects.length → after.objects[reference]? = before.objects[reference]? := by
    intro reference inside
    exact List.getElem?_append_left inside
  have physical := frame_after_fresh_object before after closure.environment rows query collector keyBound records initial object frame rfl rfl rfl
    (fun ref same => by have equal := Option.some.inj (prototype.symm.trans same); subst ref; exact rootProtected)
  have reframed := frame_withReadValues after closure.environment rows query collector keyBound records initial
    (fun _ => mapValue object root) (fun record => record.snapshot.node) physical
  refine ⟨reframed, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · apply (protected_revalueRecords after records _ _ parent).mpr
    exact ⟨by simpa [after, NodeParamsInit.mapState] using Nat.lt_succ_of_lt parentProtected.1, parentProtected.2⟩
  · intro reference same
    cases Value.object.inj same
    apply (protected_revalueRecords after records _ _ before.objects.length).mpr
    exact fresh_parameter_protected frame (by simp [after, NodeParamsInit.mapState])
  · intro record member key used
    change record ∈ records.map (fun record => withReadValues record (mapValue object root) record.snapshot.node) at member
    obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨descriptor, depth, path, bound, inherited⟩ := rootReads original oldMember key used
    constructor
    · apply NodeParamAssignment.ParameterRead.object
      exact fresh_map_get before object key (root key) ready prototype descriptor depth path bound inherited
    · rw [get_after_fresh_object propertyFuel before after parent key frame.closed parentProtected.1 oldObjects]
      exact parentReads original oldMember key used

def installed_map (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure) (receiver handle : Nat)
    (object : OrdinaryObject) (installed : Installed before table closure receiver handle) :
    Installed (NodeParamsInit.mapState before object) table closure receiver handle := by
  refine ⟨installed.identity, installed.scope, ?_, installed.method, installed.source, installed.separate, installed.handleBound, installed.closureFound⟩
  obtain ⟨receiverObject, found⟩ := installed.receiverFound
  exact ⟨receiverObject, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found⟩

theorem storage_map (before : State) (closure : PrivateMethodClosure) (child slot methods collector : Nat)
    (rows : List Value) (object : OrdinaryObject) (stored : Storage before closure child slot methods collector rows) :
    Storage (NodeParamsInit.mapState before object) closure child slot methods collector rows := by
  obtain ⟨childObject, found⟩ := stored.childFound
  exact ⟨⟨childObject, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found⟩,
    stored.scope, stored.data, stored.rowsFound, stored.separate, stored.legal⟩

/-- Internal transport for an ACTUALLY produced fresh map. Public source
protocols below discharge object/descriptor readiness from123 and158–160. -/
theorem call_after_map (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent keyBound : Nat)
    (rows initial : List Value) (query : JSString) (records : List Record) (root : JSString → Value) (object : OrdinaryObject)
    (inputs : EntryInputs before table closure receiver handle node parentIdentity child slot methods collector parent keyBound rows initial query records root)
    (ready : SpreadTargetReady object) (prototype : object.prototype = some 0) :
    ∃ after, sourceCall (rows.length + keyBound + 103) table (NodeParamsInit.mapState before object) = some (.ok (.undefined, after)) ∧
      Contract (NodeParamsInit.mapState before object) after closure receiver child slot methods collector parent before.objects.length rows initial query := by
  obtain ⟨installed⟩ := inputs.installed
  have reads : CallReads (NodeParamsInit.mapState before object) receiver node parentIdentity child collector parent before.objects.length query := by
    refine ⟨inputs.thisValue, ?_, ?_, ?_, ?_, NodeParamsInit.map_child_writable before node parentIdentity (.object parent) object inputs.parentData, rfl⟩
    · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.collectorBinding
    · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.childBinding
    · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.methodBinding
    · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.nodeBinding
  exact source_call_satisfies _ table closure receiver handle node parentIdentity child slot methods collector parent before.objects.length keyBound rows initial query
    (readRecords records object root) (installed_map before table closure receiver handle object installed) reads
    (storage_map before closure child slot methods collector rows object inputs.stored)
    (fresh_map_sources before object closure rows initial query collector keyBound parent records root inputs.frame inputs.parentProtected inputs.rootProtected
      inputs.parentReads inputs.rootReads ready prototype)

theorem collect_after_guard (budget : Nat) (table : PrivateMethodTable) (before guarded after : State) (test : Bool)
    (condition : evalExpression (budget + 104) defaultSplitLimit NodeCaptureGuard.condition before = .ok (.boolean test, before))
    (selected : if test then ∃ value, executeAssignment (budget + 101) defaultSplitLimit NodeCaptureGuard.assignment before = .ok (value, guarded) else guarded = before)
    (called : sourceCall (budget + 103) table guarded = some (.ok (.undefined, after))) :
    sourceCollect (budget + 106) table before = some (.ok (.normal after)) := by
  have callRun : runPrivateMethodCall (budget + 103) defaultSplitLimit table ⟨guarded.thisValue⟩ call guarded = .ok (.undefined, after) := by
    simpa [sourceCall, parses_call] using called
  have head : executePrivateControlStmt (budget + 105) defaultSplitLimit table
      (.branch NodeCaptureGuard.condition [.ordinary (.assign NodeCaptureGuard.assignment)] []) before = .ok (.normal guarded) := by
    change (do
      let (value, state) ← evalExpression (budget + 104) defaultSplitLimit NodeCaptureGuard.condition before
      executePrivateControl (budget + 104) defaultSplitLimit table (if truthy value then [.ordinary (.assign NodeCaptureGuard.assignment)] else []) state) = _
    rw [condition]
    cases test with
    | false =>
      subst guarded
      rfl
    | true =>
      obtain ⟨value, assigned⟩ := selected
      change (do
        match ← execute (budget + 102) defaultSplitLimit [.assign NodeCaptureGuard.assignment] before with
        | .normal state => executePrivateControl (budget + 103) defaultSplitLimit table [] state
        | .returned value state => pure (.returned value state)) = _
      rw [execute, assigned]
      rfl
  have tail : executePrivateControl (budget + 105) defaultSplitLimit table [.privateCall call] guarded = .ok (.normal after) := by
    change (do
      match ← (do let (_, state) ← runPrivateMethodCall (budget + 103) defaultSplitLimit table ⟨guarded.thisValue⟩ call guarded; pure (Completion.normal state)) with
      | .normal state => executePrivateControl (budget + 104) defaultSplitLimit table [] state
      | .returned value state => pure (.returned value state)) = _
    rw [callRun]
    rfl
  have run : executePrivateControl (budget + 106) defaultSplitLimit table program before = .ok (.normal after) := by
    change (do
      match ← executePrivateControlStmt (budget + 105) defaultSplitLimit table (.branch NodeCaptureGuard.condition [.ordinary (.assign NodeCaptureGuard.assignment)] []) before with
      | .normal state => executePrivateControl (budget + 105) defaultSplitLimit table [.privateCall call] state
      | .returned value state => pure (.returned value state)) = _
    rw [head]
    exact tail
  simpa [sourceCollect, parses_source] using congrArg some run

/-- Standalone188B with an existing own property. Any own descriptor skips the
RHS, so no matched-array prerequisite appears. The call still uses actual
parent-fourth/local-q-fifth reads and source-installed method/row storage. -/
theorem source_owned_collect_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent q keyBound : Nat)
    (rows initial : List Value) (query name : JSString) (records : List Record) (object : OrdinaryObject) (descriptor : PropertyDescriptor)
    (installed : Installed before table closure receiver handle)
    (reads : CallReads before receiver node parentIdentity child collector parent q query)
    (stored : Storage before closure child slot methods collector rows)
    (facts : TwoSource before closure.environment rows query collector keyBound records parent (.object q) initial)
    (guard : NodeCaptureGuard.OwnInputs before q object name descriptor) :
    ∃ after, sourceCollect (rows.length + keyBound + 106) table before = some (.ok (.normal after)) ∧
      NodeCaptureGuard.GuardContract before q object name (.ok (.normal before)) ∧
      Contract before after closure receiver child slot methods collector parent q rows initial query := by
  obtain ⟨after, called, contract⟩ := source_call_satisfies before table closure receiver handle node parentIdentity child slot methods collector parent q keyBound rows initial query records installed reads stored facts
  have condition := NodeCaptureGuard.eval_condition (rows.length + keyBound + 96) before q object name guard.toHeaderInputs
  simp only [guard.own, Option.isSome_some, Bool.not_true] at condition
  exact ⟨after, collect_after_guard (rows.length + keyBound) table before before after false condition rfl called, .skipped descriptor guard, contract⟩

/-- Both source123 arms. The object index is a pure construction from the
INITIAL source descriptor list, not a supplied completed clone or future heap.
The shared arm requires no copy/getter readiness on its shared source object. -/
inductive InitInputs (before : State) (node identity parent empty : Nat) : OrdinaryObject → Nat → Prop where
  | shared (header : NodeParamsInit.HeaderInputs before node identity parent empty) (same : parent = empty) :
      InitInputs before node identity parent empty emptyLiteralObject 16
  | copied (source : OrdinaryObject) (inputs : NodeParamsInit.CopyInputs before node identity parent empty source) :
      InitInputs before node identity parent empty (NodeParamsInit.copiedObject source) ((ownStringKeys source).length + 16)

set_option maxRecDepth 32768 in
theorem init_inputs_satisfies (before : State) (node identity parent empty : Nat) (object : OrdinaryObject) (fuel : Nat)
    (inputs : InitInputs before node identity parent empty object fuel) :
    NodeParamsInit.sourceInit fuel before = some (.ok (NodeParamsInit.mapState before object)) ∧
    NodeParamsInit.InitContract before (NodeParamsInit.mapState before object) node identity parent empty ∧
    SpreadTargetReady object ∧ WellFormedObject object ∧ object.prototype = some 0 := by
  cases inputs with
  | shared header same =>
    obtain ⟨run, contract⟩ := NodeParamsInit.source_shared_satisfies 0 before node identity parent empty header same
    exact ⟨run, contract, emptyLiteral_spreadReady, by simp [WellFormedObject, emptyLiteralObject], rfl⟩
  | copied source inputs =>
    obtain ⟨run, contract⟩ := NodeParamsInit.source_copy_satisfies 0 before node identity parent empty source inputs
    rw [Nat.zero_add] at run
    exact ⟨run, contract, spreadFold_ready source (ownStringKeys source) emptyLiteralObject emptyLiteral_spreadReady,
      (NodeParamsInit.copied_object_eligible source).1, spreadFold_prototype source (ownStringKeys source) emptyLiteralObject⟩

/-- All facts precede123. In particular the RHS m[0] remains an explicit
matched-array input boundary; source156 and enclosing if(m) are not claimed. -/
structure MatchInputs (before : State) (name : JSString) (matched : Nat) (values : List Value) (captured : JSString)
    (descriptor : Option PropertyDescriptor) (depth : Nat) : Prop where
  standard : StandardObjectBinding before
  nameBinding : before.environment.lookup "name" = some (.string name)
  matchedBinding : before.environment.lookup "m" = some (.array matched)
  matchedFound : before.heap[matched]? = some values
  capturedFound : values[0]? = some (.string captured)
  legal : values.length ≤ maximumArrayLength
  path : NodeCaptureGuard.DescriptorPath before.objects name 0 descriptor depth
  bound : depth + 1 ≤ propertyFuel

theorem map_guard_header (before : State) (object : OrdinaryObject) (name : JSString)
    (well : WellFormedObject object) (standard : StandardObjectBinding before)
    (nameBinding : before.environment.lookup "name" = some (.string name)) :
    NodeCaptureGuard.HeaderInputs (NodeParamsInit.mapState before object) before.objects.length object name :=
  ⟨by simpa [StandardObjectBinding, NodeParamsInit.mapState, List.lookup_cons] using standard, rfl,
    by simpa [NodeParamsInit.mapState, List.lookup_cons] using nameBinding, by simp [NodeParamsInit.mapState], well⟩

theorem map_absent_inputs (before : State) (object : OrdinaryObject) (name : JSString) (matched : Nat) (values : List Value)
    (captured : JSString) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (well : WellFormedObject object) (prototype : object.prototype = some 0) (absent : object.own.lookup name = none)
    (inputs : MatchInputs before name matched values captured descriptor depth) :
    NodeCaptureGuard.AbsentInputs (NodeParamsInit.mapState before object) before.objects.length object name matched values captured descriptor (depth + 1) := by
  refine ⟨map_guard_header before object name well inputs.standard inputs.nameBinding, absent, ?_, inputs.matchedFound,
    inputs.capturedFound, inputs.legal, ?_, inputs.bound⟩
  · simpa [NodeParamsInit.mapState, List.lookup_cons] using inputs.matchedBinding
  · exact .parent (by simp [NodeParamsInit.mapState]) absent prototype
      (NodeCaptureGuard.descriptor_path_append before.objects [object] name 0 descriptor depth inputs.path)

theorem written_map_eq (before : State) (object : OrdinaryObject) (name captured : JSString) :
    NodeCaptureGuard.writtenState (NodeParamsInit.mapState before object) before.objects.length object name captured =
      NodeParamsInit.mapState before (newDataObject object name (.string captured)) := by
  simp [NodeCaptureGuard.writtenState, NodeParamsInit.mapState, List.set_append_right]

/-- Actual123 followed by contiguous158–161, with ordinary capture creation.
The initial copied/empty object determines own absence; descriptor paths and m
are initial facts. q, its Gets, helper Layout, and captures are all conclusions. -/
theorem source_init_created_collect_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent empty keyBound initFuel : Nat)
    (rows initial : List Value) (query name captured : JSString) (records : List Record) (root : JSString → Value)
    (object : OrdinaryObject) (matched : Nat) (values : List Value) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : EntryInputs before table closure receiver handle node parentIdentity child slot methods collector parent keyBound rows initial query records root)
    (initializer : InitInputs before node parentIdentity parent empty object initFuel)
    (matchedInputs : MatchInputs before name matched values captured descriptor depth)
    (absent : object.own.lookup name = none) (classified : NodeCaptureGuard.action descriptor true = .create) :
    let initialized := NodeParamsInit.mapState before object
    let guarded := NodeParamsInit.mapState before (newDataObject object name (.string captured))
    NodeParamsInit.sourceInit initFuel before = some (.ok initialized) ∧ NodeParamsInit.InitContract before initialized node parentIdentity parent empty ∧
    ∃ after, sourceCollect (rows.length + keyBound + 106) table initialized = some (.ok (.normal after)) ∧
      NodeCaptureGuard.GuardContract initialized before.objects.length object name (.ok (.normal guarded)) ∧
      Contract guarded after closure receiver child slot methods collector parent before.objects.length rows initial query := by
  dsimp only
  obtain ⟨initRun, initContract, ready, well, prototype⟩ := init_inputs_satisfies before node parentIdentity parent empty object initFuel initializer
  have guard := map_absent_inputs before object name matched values captured descriptor depth well prototype absent matchedInputs
  have condition := NodeCaptureGuard.eval_condition (rows.length + keyBound + 96) _ before.objects.length object name guard.toHeaderInputs
  simp only [absent, Option.isSome_none, Bool.not_false] at condition
  have assigned := NodeCaptureGuard.execute_assignment (rows.length + keyBound + 77) _ before.objects.length object name matched values captured descriptor (depth + 1) guard
  rw [ready.extensible, classified, written_map_eq] at assigned
  obtain ⟨after, called, contract⟩ := call_after_map before table closure receiver handle node parentIdentity child slot methods collector parent keyBound rows initial query records root
    (newDataObject object name (.string captured)) inputs (newDataObject_spreadReady object name (.string captured) ready) prototype
  have created := NodeCaptureGuard.created_contract _ before.objects.length object name captured guard.found
  rw [written_map_eq] at created
  exact ⟨initRun, initContract, after, collect_after_guard (rows.length + keyBound) table _ _ after true condition ⟨.string captured, assigned⟩ called,
    .created matched values captured descriptor (depth + 1) guard (by simpa [ready.extensible] using classified) _ created, contract⟩

/-- The legacy primitive-string prototype setter may leave capture absent.
The subsequent source161 nevertheless gets the actual empty/copied q, rather
than inventing an own __proto__ value or repairing the source behavior. -/
theorem source_init_ignored_collect_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent empty keyBound initFuel : Nat)
    (rows initial : List Value) (query name captured : JSString) (records : List Record) (root : JSString → Value)
    (object : OrdinaryObject) (matched : Nat) (values : List Value) (descriptor : Option PropertyDescriptor) (depth : Nat)
    (inputs : EntryInputs before table closure receiver handle node parentIdentity child slot methods collector parent keyBound rows initial query records root)
    (initializer : InitInputs before node parentIdentity parent empty object initFuel)
    (matchedInputs : MatchInputs before name matched values captured descriptor depth)
    (absent : object.own.lookup name = none) (classified : NodeCaptureGuard.action descriptor true = .ignore) :
    let initialized := NodeParamsInit.mapState before object
    NodeParamsInit.sourceInit initFuel before = some (.ok initialized) ∧ NodeParamsInit.InitContract before initialized node parentIdentity parent empty ∧
    ∃ after, sourceCollect (rows.length + keyBound + 106) table initialized = some (.ok (.normal after)) ∧
      NodeCaptureGuard.GuardContract initialized before.objects.length object name (.ok (.normal initialized)) ∧
      Contract initialized after closure receiver child slot methods collector parent before.objects.length rows initial query := by
  dsimp only
  obtain ⟨initRun, initContract, ready, well, prototype⟩ := init_inputs_satisfies before node parentIdentity parent empty object initFuel initializer
  have guard := map_absent_inputs before object name matched values captured descriptor depth well prototype absent matchedInputs
  have condition := NodeCaptureGuard.eval_condition (rows.length + keyBound + 96) _ before.objects.length object name guard.toHeaderInputs
  simp only [absent, Option.isSome_none, Bool.not_false] at condition
  have assigned := NodeCaptureGuard.execute_assignment (rows.length + keyBound + 77) _ before.objects.length object name matched values captured descriptor (depth + 1) guard
  rw [ready.extensible, classified] at assigned
  obtain ⟨after, called, contract⟩ := call_after_map before table closure receiver handle node parentIdentity child slot methods collector parent keyBound rows initial query records root object inputs ready prototype
  exact ⟨initRun, initContract, after, collect_after_guard (rows.length + keyBound) table _ _ after true condition ⟨.string captured, assigned⟩ called,
    .ignored matched values captured descriptor (depth + 1) guard (by simpa [ready.extensible] using classified), contract⟩

/-- Source123 followed by own-property skip and the exact161 call. The
owned premise selects an inhabited copied arm; freshly empty {} has no own key. There
is no m prerequisite: even an absent binding cannot be read by the guard. -/
theorem source_init_owned_collect_satisfies (before : State) (table : PrivateMethodTable) (closure : PrivateMethodClosure)
    (receiver handle node parentIdentity child slot methods collector parent empty keyBound initFuel : Nat)
    (rows initial : List Value) (query name : JSString) (records : List Record) (root : JSString → Value)
    (object : OrdinaryObject) (descriptor : PropertyDescriptor)
    (inputs : EntryInputs before table closure receiver handle node parentIdentity child slot methods collector parent keyBound rows initial query records root)
    (initializer : InitInputs before node parentIdentity parent empty object initFuel)
    (standard : StandardObjectBinding before) (nameBinding : before.environment.lookup "name" = some (.string name))
    (owned : object.own.lookup name = some descriptor) :
    let initialized := NodeParamsInit.mapState before object
    NodeParamsInit.sourceInit initFuel before = some (.ok initialized) ∧ NodeParamsInit.InitContract before initialized node parentIdentity parent empty ∧
    ∃ after, sourceCollect (rows.length + keyBound + 106) table initialized = some (.ok (.normal after)) ∧
      NodeCaptureGuard.GuardContract initialized before.objects.length object name (.ok (.normal initialized)) ∧
      Contract initialized after closure receiver child slot methods collector parent before.objects.length rows initial query := by
  dsimp only
  obtain ⟨initRun, initContract, ready, well, prototype⟩ := init_inputs_satisfies before node parentIdentity parent empty object initFuel initializer
  have guard : NodeCaptureGuard.OwnInputs (NodeParamsInit.mapState before object) before.objects.length object name descriptor :=
    ⟨map_guard_header before object name well standard nameBinding, owned⟩
  have condition := NodeCaptureGuard.eval_condition (rows.length + keyBound + 96) _ before.objects.length object name guard.toHeaderInputs
  simp only [owned, Option.isSome_some, Bool.not_true] at condition
  obtain ⟨after, called, contract⟩ := call_after_map before table closure receiver handle node parentIdentity child slot methods collector parent keyBound rows initial query records root object inputs ready prototype
  exact ⟨initRun, initContract, after, collect_after_guard (rows.length + keyBound) table _ _ after false condition rfl called, .skipped descriptor guard, contract⟩

/- The executable/parser proofs and every causal headline use only Lean's
standard logical axioms. No native_decide, source-result oracle or sorry. -/
/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_init_created_collect_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_init_created_collect_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_init_ignored_collect_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_init_ignored_collect_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_init_owned_collect_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_init_owned_collect_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureCollect.source_owned_collect_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_owned_collect_satisfies
/-- info: 'HonoLean.Upstream.NodeCaptureCollect.fresh_map_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fresh_map_sources
end HonoLean.Upstream.NodeCaptureCollect
