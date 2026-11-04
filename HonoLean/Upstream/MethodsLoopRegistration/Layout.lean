import HonoLean.Upstream.MethodsLoopRegistration.Facts
import HonoLean.Upstream.MethodsLoopInitial.Contract

namespace HonoLean.Upstream.MethodsLoopRegistration

open SourceSubset ECMA2025

def record (before : State) (handler : Value) (order : Int) (snapshot : NodeParamLoop.Snapshot) :
    MethodsLoopInitial.Record :=
  ⟨before.objects.length + 1, HandlerRecord.innerRecord handler before.heap.length (order + 1),
    before.heap.length, snapshot⟩

/-- Caller/helper/module and stable old-object reads. This one-state remainder
has no source-selected handler, copied key cell, collector, future Entry,
NormalPrefixes or completed execution as a premise. -/
structure Context (before : State) (context : List (String × Value)) (owner : Nat)
    (query : JSString) (parameterReceiver : Value) (nodeParams : Nat)
    (snapshot : NodeParamLoop.Snapshot) : Prop where
  ownerBinding : context.lookup "node" = some (.object owner)
  queryBinding : context.lookup "method" = some (.string query)
  allBinding : context.lookup "METHOD_NAME_ALL" = some (.string SearchEntry.allKey)
  parameterBinding : context.lookup "params" = some parameterReceiver
  nodeBinding : context.lookup "nodeParams" = some (.object nodeParams)
  helper : ∃ reference environment,
    context.lookup "createNullObject" = some (.function reference) ∧
    before.functions[reference]? = some ⟨CreateNullObject.createProgram, environment⟩ ∧
    StandardObjectBinding {before with environment}
  closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length
  rootDispatch : lookupProperty 31 before.objects 0 HandlerRecord.paramsKey = .ok none ∨
    ∃ value enumerable configurable, lookupProperty 31 before.objects 0 HandlerRecord.paramsKey =
      .ok (some (.data value true enumerable configurable))
  nodeBound : nodeParams < before.objects.length
  parameterBound : ∀ reference, parameterReceiver = .object reference → reference < before.objects.length
  legalKeys : snapshot.keys.length ≤ 4294967295
  reads : ∀ key ∈ snapshot.keys,
    NodeParamAssignment.ParameterRead before key parameterReceiver (snapshot.parameter key) ∧
    getProperty propertyFuel before.objects nodeParams key = .ok (snapshot.node key)

/-- Exact own-key hits, own ALL fallback, and genuine misses are distinguished.
Root lookup absence is explicit when needed: key inequality alone cannot rule
out truthy inherited constructor/prototype values. -/
def QueryDomain (before : State) (method query : JSString) : Prop :=
  query = method ∨
    (method = SearchEntry.allKey ∧ query ≠ method ∧ lookupProperty 31 before.objects 0 query = .ok none) ∨
    (query ≠ method ∧ SearchEntry.allKey ≠ method ∧
      lookupProperty 31 before.objects 0 query = .ok none ∧
      lookupProperty 31 before.objects 0 SearchEntry.allKey = .ok none)

theorem activation_old_cell (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) (reference : Nat) (inside : reference < before.objects.length) :
    (activation before method handler keys order methods searchEnvironment context).objects[reference]? =
      before.objects[reference]? := List.getElem?_append_left inside

theorem activation_length (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) :
    (activation before method handler keys order methods searchEnvironment context).objects.length = before.objects.length + 2 := by
  simp [activation, SearchEntry.pushActivation, SearchEntry.collectorState, SearchEntry.searchActivation,
    SearchEntry.boundState, registered, NodeMethodsPush.pushedState, HandlerRecord.constructedState]

theorem old_lookup_frame (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) (fuel reference : Nat) (key : JSString)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (inside : reference < before.objects.length) :
    lookupProperty fuel (activation before method handler keys order methods searchEnvironment context).objects reference key =
      lookupProperty fuel before.objects reference key := by
  symm
  exact NodeParamLoop.lookupProperty_frame fuel _ _ before.objects.length
    (fun ref bound => (activation_old_cell before method handler keys order methods searchEnvironment context ref bound).symm)
    closed reference inside key

theorem old_get_frame (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) (reference : Nat) (key : JSString)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (inside : reference < before.objects.length) :
    getProperty propertyFuel (activation before method handler keys order methods searchEnvironment context).objects reference key =
      getProperty propertyFuel before.objects reference key := by
  symm
  exact NodeParamLoop.getProperty_frame propertyFuel _ _ before.objects.length
    (fun ref bound => (activation_old_cell before method handler keys order methods searchEnvironment context ref bound).symm)
    closed reference inside key

theorem old_protected (before : State) (method : JSString) (handler : Value)
    (snapshot : NodeParamLoop.Snapshot) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) (reference : Nat) (inside : reference < before.objects.length) :
    MethodsLoopInitial.Protected (activation before method handler snapshot.keys order methods searchEnvironment context)
      [record before handler order snapshot] reference := by
  constructor
  · rw [activation_length]
    omega
  · intro candidate member
    have equal : candidate = record before handler order snapshot := by simpa using member
    subst candidate
    change reference ≠ before.objects.length + 1
    omega

theorem row_protected (before : State) (method : JSString) (handler : Value)
    (snapshot : NodeParamLoop.Snapshot) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) :
    MethodsLoopInitial.Protected (activation before method handler snapshot.keys order methods searchEnvironment context)
      [record before handler order snapshot] before.objects.length := by
  constructor
  · rw [activation_length]
    omega
  · intro candidate member
    have equal : candidate = record before handler order snapshot := by simpa using member
    subst candidate
    change before.objects.length ≠ before.objects.length + 1
    omega

theorem activation_closed (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value))
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (rootBound : 0 < before.objects.length) :
    NodeParamLoop.PrototypeClosed
      (activation before method handler keys order methods searchEnvironment context).objects
      (activation before method handler keys order methods searchEnvironment context).objects.length := by
  intro reference inside object found parent prototype
  have length := activation_length before method handler keys order methods searchEnvironment context
  by_cases old : reference < before.objects.length
  · rw [activation_old_cell before method handler keys order methods searchEnvironment context reference old] at found
    have bound := closed reference old object found parent prototype
    rw [activation_length before method handler keys order methods searchEnvironment context]
    exact Nat.lt_trans bound (Nat.lt_succ_of_le (Nat.le_succ _))
  · have cases : reference = before.objects.length ∨ reference = before.objects.length + 1 := by omega
    rcases cases with rfl | rfl
    · have same := (activation_outer before method handler keys order methods searchEnvironment context).symm.trans found
      cases Option.some.inj same
      have equal : parent = 0 := by simpa [HandlerRecord.outerRecord] using prototype.symm
      subst parent
      rw [activation_length before method handler keys order methods searchEnvironment context]
      exact Nat.lt_trans rootBound (Nat.lt_succ_of_le (Nat.le_succ _))
    · have same := (activation_inner before method handler keys order methods searchEnvironment context).symm.trans found
      cases Option.some.inj same
      have equal : parent = 0 := by simpa [HandlerRecord.innerRecord] using prototype.symm
      subst parent
      rw [activation_length before method handler keys order methods searchEnvironment context]
      exact Nat.lt_trans rootBound (Nat.lt_succ_of_le (Nat.le_succ _))

theorem protected_parents (before : State) (method : JSString) (handler : Value)
    (snapshot : NodeParamLoop.Snapshot) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value))
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (rootBound : 0 < before.objects.length) :
    ∀ reference, MethodsLoopInitial.Protected
      (activation before method handler snapshot.keys order methods searchEnvironment context)
      [record before handler order snapshot] reference →
    ∀ object, (activation before method handler snapshot.keys order methods searchEnvironment context).objects[reference]? = some object →
    ∀ parent, object.prototype = some parent → MethodsLoopInitial.Protected
      (activation before method handler snapshot.keys order methods searchEnvironment context)
      [record before handler order snapshot] parent := by
  intro reference guarded object found parent prototype
  have length := activation_length before method handler snapshot.keys order methods searchEnvironment context
  have notHandler : reference ≠ before.objects.length + 1 :=
    guarded.2 (record before handler order snapshot) (by simp)
  by_cases old : reference < before.objects.length
  · rw [activation_old_cell before method handler snapshot.keys order methods searchEnvironment context reference old] at found
    exact old_protected before method handler snapshot order methods searchEnvironment context parent
      (closed reference old object found parent prototype)
  · have equal : reference = before.objects.length := by have := guarded.1; omega
    subst reference
    have same := (activation_outer before method handler snapshot.keys order methods searchEnvironment context).symm.trans found
    cases Option.some.inj same
    have equal : parent = 0 := by simpa [HandlerRecord.outerRecord] using prototype.symm
    subst parent
    exact old_protected before method handler snapshot order methods searchEnvironment context 0 rootBound

theorem outer_own_read (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) :
    getProperty propertyFuel (activation before method handler keys order methods searchEnvironment context).objects
      before.objects.length method = .ok (.object (before.objects.length + 1)) :=
  getProperty_data _ _ 31 _ _ _ true true true
    (activation_outer before method handler keys order methods searchEnvironment context)
    (HandlerRecord.outer_method method (before.objects.length + 1)).1

theorem outer_missing_read (before : State) (method query : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value))
    (different : query ≠ method)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (rootBound : 0 < before.objects.length)
    (rootMiss : lookupProperty 31 before.objects 0 query = .ok none) :
    getProperty propertyFuel (activation before method handler keys order methods searchEnvironment context).objects
      before.objects.length query = .ok .undefined := by
  have lookup : lookupProperty propertyFuel
      (activation before method handler keys order methods searchEnvironment context).objects before.objects.length query =
      lookupProperty 31 (activation before method handler keys order methods searchEnvironment context).objects 0 query := by
    rw [show propertyFuel = 32 from rfl, lookupProperty,
      activation_outer before method handler keys order methods searchEnvironment context]
    simp [HandlerRecord.outerRecord, List.lookup_cons, beq_false_of_ne different]
  rw [old_lookup_frame before method handler keys order methods searchEnvironment context 31 0 query closed rootBound] at lookup
  simp [getProperty, lookup, rootMiss, bind, pure, Except.bind, Except.pure]

theorem old_parameter_read (before : State) (method : JSString) (handler : Value)
    (keys : List JSString) (order : Int) (methods : Nat)
    (searchEnvironment context : List (String × Value)) (receiver value : Value) (key : JSString)
    (closed : NodeParamLoop.PrototypeClosed before.objects before.objects.length)
    (bound : ∀ ref, receiver = .object ref → ref < before.objects.length)
    (read : NodeParamAssignment.ParameterRead before key receiver value) :
    NodeParamAssignment.ParameterRead
      (activation before method handler keys order methods searchEnvironment context) key receiver value := by
  cases read with
  | object ref _ read =>
    apply NodeParamAssignment.ParameterRead.object
    rw [old_get_frame before method handler keys order methods searchEnvironment context ref key closed (bound ref rfl)]
    exact read
  | nullish _ missing => exact .nullish _ missing

/-- The source-created singleton storage satisfies a genuine one-state Layout.
Only old-object context/realm/read facts and admitted query-key conditions are
external. No current/future selected-handler or prefix readiness is supplied. -/
theorem initial_layout (events : List JSString) (before : State) (method query : JSString) (handler : Value)
    (reference : Nat) (order : Int) (owner stamp methods : Nat)
    (searchEnvironment context : List (String × Value)) (parameterReceiver : Value) (nodeParams : Nat)
    (snapshot : NodeParamLoop.Snapshot)
    (inputs : NodeMethodsPush.Inputs before method handler reference snapshot.keys order owner stamp methods [])
    (trace : NodeKeySet.TraceContract events reference before)
    (domain : Context before context owner query parameterReceiver nodeParams snapshot)
    (queryDomain : QueryDomain before method query) :
    MethodsLoopInitial.Layout (activation before method handler snapshot.keys order methods searchEnvironment context)
      (rows before) query (before.heap.length + 1) snapshot.keys.length
      [record before handler order snapshot] parameterReceiver nodeParams [] := by
  obtain ⟨root, rootFound⟩ := inputs.rootFound
  have rootBound : 0 < before.objects.length := (List.getElem?_eq_some_iff.mp rootFound).1
  have contextLookup (name : String) (different : name ≠ "handlerSets") :
      (activation before method handler snapshot.keys order methods searchEnvironment context).environment.lookup name =
        context.lookup name := SearchEntry.activation_lookup _ _ _ name different
  have rootProtected := old_protected before method handler snapshot order methods searchEnvironment context 0 rootBound
  refine {
    collectorBinding := ?_, parameterBinding := ?_, nodeBinding := ?_, allBinding := ?_, helper := ?_
    collectorFound := activation_collector before method handler snapshot.keys order methods searchEnvironment context
    capacity := by simp [rows]
    closed := activation_closed before method handler snapshot.keys order methods searchEnvironment context domain.closed rootBound
    protectedParents := protected_parents before method handler snapshot order methods searchEnvironment context domain.closed rootBound
    nodeProtected := old_protected before method handler snapshot order methods searchEnvironment context nodeParams domain.nodeBound
    parameterProtected := ?_, recordsFound := ?_, handlerParents := ?_, rowChoices := ?_}
  · change (("handlerSets", .array (registered before method handler snapshot.keys order methods).heap.length) :: context).lookup
      "handlerSets" = some (.array (before.heap.length + 1))
    simp [registered, NodeMethodsPush.pushedState]
  · rw [contextLookup _ (by decide)]
    exact domain.parameterBinding
  · rw [contextLookup _ (by decide)]
    exact domain.nodeBinding
  · change (activation before method handler snapshot.keys order methods searchEnvironment context).environment.lookup
      "METHOD_NAME_ALL" = some (.string SearchEntry.allKey)
    rw [contextLookup _ (by decide)]
    exact domain.allBinding
  · obtain ⟨ref, environment, binding, found, standard⟩ := domain.helper
    refine ⟨ref, environment, ?_, found, standard⟩
    rw [contextLookup _ (by decide)]
    exact binding
  · intro ref equal
    exact old_protected before method handler snapshot order methods searchEnvironment context ref (domain.parameterBound ref equal)
  · intro candidate member
    have equal : candidate = record before handler order snapshot := by simpa using member
    subst candidate
    obtain ⟨keys, found, ordered⟩ := trace
    have sameKeys : keys = snapshot.keys := Option.some.inj (found.symm.trans inputs.setFound)
    subst keys
    refine {
      found := activation_inner before method handler snapshot.keys order methods searchEnvironment context
      possibleKeys := (HandlerRecord.inner_fields handler before.heap.length (order + 1)).2.1
      keysFound := activation_keys before method handler snapshot.keys order methods searchEnvironment context
      separate := by change before.heap.length + 1 ≠ before.heap.length; omega
      resettable := ?_, unique := ordered.1, legalKeys := domain.legalKeys, keyBound := Nat.le_refl _
      reads := ?_}
    · constructor
      · have lookup : lookupProperty propertyFuel
            (activation before method handler snapshot.keys order methods searchEnvironment context).objects
            (before.objects.length + 1) NodeParamAssignment.paramsKey =
            lookupProperty 31 (activation before method handler snapshot.keys order methods searchEnvironment context).objects
              0 HandlerRecord.paramsKey := by
          rw [show propertyFuel = 32 from rfl, lookupProperty,
            activation_inner before method handler snapshot.keys order methods searchEnvironment context]
          rfl
        change (lookupProperty propertyFuel _ (before.objects.length + 1) NodeParamAssignment.paramsKey = .ok none ∨
          ∃ value enumerable configurable, lookupProperty propertyFuel _ (before.objects.length + 1)
            NodeParamAssignment.paramsKey = .ok (some (.data value true enumerable configurable)))
        rw [lookup, old_lookup_frame before method handler snapshot.keys order methods searchEnvironment context 31 0
          HandlerRecord.paramsKey domain.closed rootBound]
        exact domain.rootDispatch
      · exact Or.inl ⟨(HandlerRecord.inner_fields handler before.heap.length (order + 1)).2.2.2, rfl⟩
    · intro key member
      obtain ⟨parameterRead, nodeRead⟩ := domain.reads key member
      constructor
      · exact old_parameter_read before method handler snapshot.keys order methods searchEnvironment context
          parameterReceiver (snapshot.parameter key) key domain.closed domain.parameterBound parameterRead
      · rw [old_get_frame before method handler snapshot.keys order methods searchEnvironment context nodeParams key
          domain.closed domain.nodeBound]
        exact nodeRead
  · intro candidate member parent prototype
    have equal : candidate = record before handler order snapshot := by simpa using member
    subst candidate
    have equal : parent = 0 := by simpa [record, HandlerRecord.innerRecord] using prototype.symm
    subst parent
    exact rootProtected
  · intro count inside
    have zero : count = 0 := by simpa [rows] using inside
    subst count
    have directRead := outer_own_read before method handler snapshot.keys order methods searchEnvironment context
    have chooseRecord (choice : SearchEntry.Choice
          (activation before method handler snapshot.keys order methods searchEnvironment context)
          before.objects.length query (.object (before.objects.length + 1))) :
        ∃ row chosen, (rows before)[0]? = some (.object row) ∧
          MethodsLoopInitial.Protected
            (activation before method handler snapshot.keys order methods searchEnvironment context)
            [record before handler order snapshot] row ∧
          SearchEntry.Choice (activation before method handler snapshot.keys order methods searchEnvironment context) row query chosen ∧
          (NodeParamAssignment.Truthy chosen → ∃ candidate ∈ [record before handler order snapshot], chosen = .object candidate.reference) := by
      exact ⟨before.objects.length, .object (before.objects.length + 1), rfl,
        row_protected before method handler snapshot order methods searchEnvironment context, choice,
        fun _ => ⟨record before handler order snapshot, by simp, rfl⟩⟩
    rcases queryDomain with same | ⟨all, different, miss⟩ | ⟨different, notAll, miss, allMiss⟩
    · subst query
      apply chooseRecord
      exact ⟨.object (before.objects.length + 1), directRead, Or.inl ⟨by simp [NodeParamAssignment.Truthy], rfl⟩⟩
    · have missing := outer_missing_read before method query handler snapshot.keys order methods searchEnvironment context
        different domain.closed rootBound miss
      apply chooseRecord
      refine ⟨.undefined, missing, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, ?_, ?_⟩⟩
      · rw [contextLookup _ (by decide)]
        exact domain.allBinding
      · simpa only [all] using directRead
    · have missing := outer_missing_read before method query handler snapshot.keys order methods searchEnvironment context
        different domain.closed rootBound miss
      have missingAll := outer_missing_read before method SearchEntry.allKey handler snapshot.keys order methods searchEnvironment context
        notAll domain.closed rootBound allMiss
      refine ⟨before.objects.length, .undefined, rfl,
        row_protected before method handler snapshot order methods searchEnvironment context,
        ⟨.undefined, missing, Or.inr ⟨by simp [NodeParamAssignment.Truthy], SearchEntry.allKey, ?_, missingAll⟩⟩, ?_⟩
      · rw [contextLookup _ (by decide)]
        exact domain.allBinding
      · intro impossible
        simp [NodeParamAssignment.Truthy] at impossible

end HonoLean.Upstream.MethodsLoopRegistration
