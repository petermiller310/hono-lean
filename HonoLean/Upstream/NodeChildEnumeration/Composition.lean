import HonoLean.Upstream.NodeChildEnumeration.Correctness

namespace HonoLean.Upstream.NodeChildEnumeration

open SourceSubset ECMA2025

def createdRegexp (before : RegExpState) (queue : Nat) (queued : IndexedArray) (child : Value) (input : JSString) : RegExpState :=
  {NodeComponentCount.countState before input with
    arrays := NodeQueueSchedule.createdState (NodeComponentCount.countState before input).arrays queue (NodeComponentCount.slashCount input) queued child}
def reusedRegexp (before : RegExpState) (target : Nat) (initial : IndexedArray) (child : Value) (input : JSString) : RegExpState :=
  {NodeComponentCount.countState before input with
    arrays := NodeQueueSchedule.reusedState (NodeComponentCount.countState before input).arrays target initial child}
def createdCompleted (before : ForInState) (owner paramsIdentity : Nat) (params : Value)
    (queue : Nat) (queued : IndexedArray) (input : JSString) : ForInState :=
  {forInDataState before owner paramsIdentity params with regexp := createdRegexp before.regexp queue queued (.object owner) input}
def reusedCompleted (before : ForInState) (owner paramsIdentity : Nat) (params : Value)
    (target : Nat) (initial : IndexedArray) (input : JSString) : ForInState :=
  {forInDataState before owner paramsIdentity params with regexp := reusedRegexp before.regexp target initial (.object owner) input}
def createdResult (before : ForInState) (owner paramsIdentity : Nat) (params : Value)
    (queue : Nat) (queued : IndexedArray) (input : JSString) : ForInState :=
  restoreForInEnvironment before.regexp.arrays.environment (createdCompleted before owner paramsIdentity params queue queued input)
def reusedResult (before : ForInState) (owner paramsIdentity : Nat) (params : Value)
    (target : Nat) (initial : IndexedArray) (input : JSString) : ForInState :=
  restoreForInEnvironment before.regexp.arrays.environment (reusedCompleted before owner paramsIdentity params target initial input)

theorem created_scope (before : ForInState) (key : JSString) (owner paramsIdentity : Nat) (params : Value)
    (queue : Nat) (queued : IndexedArray) (input : JSString) :
    restoreForInEnvironment before.regexp.arrays.environment
      (createdCompleted (bindForInKey "_" key before) owner paramsIdentity params queue queued input) =
        createdResult before owner paramsIdentity params queue queued input := by
  simp [createdResult, createdCompleted, createdRegexp, restoreForInEnvironment, forInDataState, bindForInKey,
    NodeComponentCount.countState, NodeQueueSchedule.createdState]

theorem reused_scope (before : ForInState) (key : JSString) (owner paramsIdentity : Nat) (params : Value)
    (target : Nat) (initial : IndexedArray) (input : JSString) :
    restoreForInEnvironment before.regexp.arrays.environment
      (reusedCompleted (bindForInKey "_" key before) owner paramsIdentity params target initial input) =
        reusedResult before owner paramsIdentity params target initial input := by
  simp [reusedResult, reusedCompleted, reusedRegexp, restoreForInEnvironment, forInDataState, bindForInKey,
    NodeComponentCount.countState, NodeQueueSchedule.reusedState]

/-- Exact count/schedule ASTs followed by actual break. This equality handles
errors too; no successful future declaration or push is a premise. -/
theorem execute_regexp_tail (fuel : Nat) (before : ForInState) :
    executeForInSequence (fuel + 4) (NodeComponentCount.fullProgram.map ForInStmt.regexp ++ [.breakLoop]) before =
      (executeRegExpSequence (fuel + 4) NodeComponentCount.fullProgram before.regexp).map
        (fun regexp => .breakLoop {before with regexp}) := by
  simp only [NodeComponentCount.fullProgram, NodeComponentCount.program, NodeQueueSchedule.program,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, executeForInSequence,
    executeRegExpSequence, executeSparseSequence]
  cases counted : evalRegExpExpression (fuel + 3) NodeComponentCount.initializer before.regexp with
  | error error => simp [bind, Except.bind, Except.map]
  | ok pair =>
    obtain ⟨value, countedState⟩ := pair
    cases value with
    | regexp reference => simp [bind, Except.bind, Except.map]
    | ordinary value =>
      simp only [bind, Except.bind]
      cases selected : evalSparseInitializer (fuel + 2) NodeQueueSchedule.initializer
          {countedState.arrays with environment := ("componentCount", value) :: countedState.arrays.environment} with
      | error error => simp [Except.map]
      | ok pair =>
        obtain ⟨target, arrays⟩ := pair
        cases pushed : evalSparseExpression (fuel + 1) (.call (.variable "targetCurNodes") "push" [.variable "child"])
            {arrays with environment := ("targetCurNodes", target) :: arrays.environment} with
        | error error => simp [Except.map]
        | ok pair => obtain ⟨value, after⟩ := pair; simp [Except.map]

private theorem component_contract_of_run (extra : Nat) (before after : RegExpState) (m queue : Nat)
    (matched queued : IndexedArray) (child : Value) (input : JSString)
    (countInputs : NodeComponentCount.Inputs before m matched input)
    (queueInputs : NodeComponentCount.ScheduleInputs before queue queued child input)
    (admitted : NodeComponentCount.AdmittedTarget before queued input)
    (run : executeRegExpSequence (extra + 117) NodeComponentCount.fullProgram before = .ok after) :
    NodeComponentCount.ScheduleContract before after queue queued child input := by
  obtain ⟨_, result, parsed, contract⟩ := NodeComponentCount.source_schedule_satisfies (extra + 17) before m queue matched queued child input countInputs queueInputs admitted
  have executed : executeRegExpSequence (extra + 117) NodeComponentCount.fullProgram before = .ok result := by
    simpa [NodeComponentCount.sourceSchedule, NodeComponentCount.parses_full_source, Nat.add_assoc] using parsed
  rw [run] at executed
  have same : after = result := Except.ok.inj executed
  exact same.symm ▸ contract

theorem execute_component_created (extra : Nat) (before : RegExpState) (m queue : Nat)
    (matched queued : IndexedArray) (child : Value) (input : JSString)
    (countInputs : NodeComponentCount.Inputs before m matched input)
    (queueInputs : NodeComponentCount.ScheduleInputs before queue queued child input)
    (falsy : truthy (numericGet queued (NodeComponentCount.slashCount input)) = false) :
    executeRegExpSequence (extra + 117) NodeComponentCount.fullProgram before = .ok (createdRegexp before queue queued child input) ∧
    NodeComponentCount.ScheduleContract before (createdRegexp before queue queued child input) queue queued child input := by
  have ready := NodeComponentCount.counted_queue_inputs before queue queued child input queueInputs
  obtain ⟨parsed, _⟩ := NodeQueueSchedule.created_satisfies (extra + 106) (NodeComponentCount.countState before input).arrays
    queue (NodeComponentCount.slashCount input) queued child ready falsy
  have sparse : executeSparseSequence (extra + 116) [] NodeQueueSchedule.program (NodeComponentCount.countState before input).arrays =
      .ok (NodeQueueSchedule.createdState (NodeComponentCount.countState before input).arrays queue (NodeComponentCount.slashCount input) queued child) := by
    simpa [NodeQueueSchedule.sourceSchedule, NodeQueueSchedule.parses_source, Nat.add_assoc] using parsed
  have run := NodeComponentCount.execute_full (extra + 17) before m matched input countInputs (Nat.le_of_lt queueInputs.stringBound)
  rw [sparse] at run
  have actual : executeRegExpSequence (extra + 117) NodeComponentCount.fullProgram before = .ok (createdRegexp before queue queued child input) := by
    simpa [createdRegexp, Except.map, Nat.add_assoc] using run
  exact ⟨actual, component_contract_of_run extra before _ m queue matched queued child input countInputs queueInputs (Or.inl falsy) actual⟩

theorem execute_component_reused (extra : Nat) (before : RegExpState) (m queue target : Nat)
    (matched queued initial : IndexedArray) (child : Value) (input : JSString)
    (countInputs : NodeComponentCount.Inputs before m matched input)
    (queueInputs : NodeComponentCount.ScheduleInputs before queue queued child input)
    (selected : numericGet queued (NodeComponentCount.slashCount input) = .array target)
    (found : before.arrays.heap[target]? = some initial) (wellFormed : WellFormedIndexed initial)
    (capacity : initial.length < maximumArrayLength) :
    executeRegExpSequence (extra + 117) NodeComponentCount.fullProgram before = .ok (reusedRegexp before target initial child input) ∧
    NodeComponentCount.ScheduleContract before (reusedRegexp before target initial child input) queue queued child input := by
  have ready := NodeComponentCount.counted_queue_inputs before queue queued child input queueInputs
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have countedFound : (NodeComponentCount.countState before input).arrays.heap[target]? = some initial :=
    (List.getElem?_append_left inside).trans found
  obtain ⟨parsed, _⟩ := NodeQueueSchedule.reused_satisfies (extra + 106) (NodeComponentCount.countState before input).arrays
    queue (NodeComponentCount.slashCount input) target queued initial child ready selected countedFound wellFormed capacity
  have sparse : executeSparseSequence (extra + 116) [] NodeQueueSchedule.program (NodeComponentCount.countState before input).arrays =
      .ok (NodeQueueSchedule.reusedState (NodeComponentCount.countState before input).arrays target initial child) := by
    simpa [NodeQueueSchedule.sourceSchedule, NodeQueueSchedule.parses_source, Nat.add_assoc] using parsed
  have run := NodeComponentCount.execute_full (extra + 17) before m matched input countInputs (Nat.le_of_lt queueInputs.stringBound)
  rw [sparse] at run
  have actual : executeRegExpSequence (extra + 117) NodeComponentCount.fullProgram before = .ok (reusedRegexp before target initial child input) := by
    simpa [reusedRegexp, Except.map, Nat.add_assoc] using run
  exact ⟨actual, component_contract_of_run extra before _ m queue matched queued child input countInputs queueInputs
    (Or.inr ⟨target, initial, selected, found, wellFormed, capacity⟩) actual⟩

theorem body_created (extra : Nat) (before : ForInState) (key : JSString) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (old params : Value) (m queue : Nat) (matched queued : IndexedArray) (input : JSString)
    (childrenInputs : ChildrenInputs before owner childrenIdentity children object)
    (inputs : BodyInputs before owner childrenIdentity paramsIdentity old params m queue matched queued input)
    (falsy : truthy (numericGet queued (NodeComponentCount.slashCount input)) = false) :
    executeForInSequence (extra + 118) body (bindForInKey "_" key before) =
      .ok (.breakLoop (createdCompleted (bindForInKey "_" key before) owner paramsIdentity params queue queued input)) := by
  let keyed := bindForInKey "_" key before
  have childrenKey := scoped_children_inputs before key owner childrenIdentity children object childrenInputs
  have bodyKey := scoped_body_inputs before key owner childrenIdentity paramsIdentity old params m queue matched queued input inputs
  have written := execute_parameter extra keyed owner childrenIdentity children paramsIdentity object old params m queue matched queued input childrenKey bodyKey
  have component := execute_component_created extra keyed.regexp m queue matched queued (.object owner) input bodyKey.count bodyKey.queue falsy
  change executeForInSequence (extra + 118) (.privateWrite NodePrivateWrite.parameter ::
    (NodeComponentCount.fullProgram.map ForInStmt.regexp ++ [.breakLoop])) keyed = _
  rw [executeForInSequence, written]
  dsimp only [bind, pure, Except.bind, Except.pure]
  rw [execute_regexp_tail (extra + 113)]
  simp only [forInDataState, Nat.add_assoc]
  rw [component.1]
  rfl

theorem body_reused (extra : Nat) (before : ForInState) (key : JSString) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (old params : Value) (m queue target : Nat) (matched queued initial : IndexedArray) (input : JSString)
    (childrenInputs : ChildrenInputs before owner childrenIdentity children object)
    (inputs : BodyInputs before owner childrenIdentity paramsIdentity old params m queue matched queued input)
    (selected : numericGet queued (NodeComponentCount.slashCount input) = .array target)
    (found : before.regexp.arrays.heap[target]? = some initial) (wellFormed : WellFormedIndexed initial)
    (capacity : initial.length < maximumArrayLength) :
    executeForInSequence (extra + 118) body (bindForInKey "_" key before) =
      .ok (.breakLoop (reusedCompleted (bindForInKey "_" key before) owner paramsIdentity params target initial input)) := by
  let keyed := bindForInKey "_" key before
  have childrenKey := scoped_children_inputs before key owner childrenIdentity children object childrenInputs
  have bodyKey := scoped_body_inputs before key owner childrenIdentity paramsIdentity old params m queue matched queued input inputs
  have written := execute_parameter extra keyed owner childrenIdentity children paramsIdentity object old params m queue matched queued input childrenKey bodyKey
  have component := execute_component_reused extra keyed.regexp m queue target matched queued initial (.object owner) input bodyKey.count bodyKey.queue selected found wellFormed capacity
  change executeForInSequence (extra + 118) (.privateWrite NodePrivateWrite.parameter ::
    (NodeComponentCount.fullProgram.map ForInStmt.regexp ++ [.breakLoop])) keyed = _
  rw [executeForInSequence, written]
  dsimp only [bind, pure, Except.bind, Except.pure]
  rw [execute_regexp_tail (extra + 113)]
  simp only [forInDataState, Nat.add_assoc]
  rw [component.1]
  rfl

private theorem contract_from_stages (before after : ForInState) (key : JSString) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (old params : Value) (m queue : Nat) (matched queued : IndexedArray) (input : JSString)
    (childrenInputs : ChildrenInputs before owner childrenIdentity children object)
    (inputs : BodyInputs before owner childrenIdentity paramsIdentity old params m queue matched queued input)
    (enumerable : EnumerableName object key) (completed : ForInState)
    (component : NodeComponentCount.ScheduleContract (bindForInKey "_" key before).regexp completed.regexp queue queued (.object owner) input)
    (ambient : completed.ambient = (forInDataState (bindForInKey "_" key before) owner paramsIdentity params).ambient)
    (restored : after = restoreForInEnvironment before.regexp.arrays.environment completed) :
    EnteredContract before after owner childrenIdentity children paramsIdentity object old params queue queued input := by
  let active := bindForInKey "_" key before
  let written := forInDataState active owner paramsIdentity params
  have scopedInputs := scoped_body_inputs before key owner childrenIdentity paramsIdentity old params m queue matched queued input inputs
  have changed := private_write_contract before owner paramsIdentity old params inputs.writable
  have ambientFrame : after.ambient = writePrivateDataState before.ambient owner paramsIdentity params := by
    rw [restored]
    exact ambient
  refine ⟨childrenInputs, inputs.writable, inputs.paramsBinding, inputs.distinct,
    ⟨key, active, written, completed, enumerable, rfl,
      private_write_contract active owner paramsIdentity old params scopedInputs.writable, rfl, component, ambient, restored⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ambientFrame, forInStateView, embedIndexedState, forInDataState, writePrivateDataState] using changed.privateChange
  · have same : privateGet (.object owner) "children" (forInStateView after) =
        privateGet (.object owner) "children" (forInStateView (forInDataState before owner paramsIdentity params)) := by
      simp only [privateGet, forInStateView, embedIndexedState, ambientFrame, forInDataState]
    rw [same]
    exact children_read_after_write before owner childrenIdentity children paramsIdentity object params childrenInputs inputs.distinct
  · rw [restored]; rfl
  all_goals rw [ambientFrame]; rfl

private theorem source_from_derived_body (extra : Nat) (before after : ForInState) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (old params : Value) (queue : Nat) (queued : IndexedArray) (input : JSString)
    (childrenInputs : ChildrenInputs before owner childrenIdentity children object)
    (witness : ∃ key, EnumerableName object key)
    (bodyBreak : ∀ key, EnumerableName object key → ∃ completed,
      executeForInSequence (extra + 118) body (bindForInKey "_" key before) = .ok (.breakLoop completed) ∧
      restoreForInEnvironment before.regexp.arrays.environment completed = after)
    (contracts : ∀ key, EnumerableName object key → EnteredContract before after owner childrenIdentity children paramsIdentity object old params queue queued input) :
    sourceLoop (extra + 120) before = some (.ok (.normal after)) ∧
    EnteredContract before after owner childrenIdentity children paramsIdentity object old params queue queued input ∧
    (∀ keys, LegalForInOrder object keys → executeForInKeys (extra + 119) "_" body keys before = .ok after) := by
  have allOrders : ∀ keys, LegalForInOrder object keys → executeForInKeys (extra + 119) "_" body keys before = .ok after := by
    intro keys legal
    exact executeForInKeys_all_orders (extra + 118) "_" body object before after keys legal witness bodyBreak
  have contract : EnteredContract before after owner childrenIdentity children paramsIdentity object old params queue queued input := by
    cases equation : enumerableOwn object with
    | nil => exact False.elim ((enumerableOwn_empty_iff object).mp equation witness)
    | cons key rest =>
      have member : key ∈ enumerableOwn object := by rw [equation]; simp
      exact contracts key ((enumerableOwn_member object key).mp member)
  have executed := allOrders (enumerableOwn object) (enumerableOwn_legal object childrenInputs.nullPrototype childrenInputs.wellFormed)
  have header := children_keys (extra + 116) before owner childrenIdentity children object childrenInputs
  refine ⟨?_, contract, allOrders⟩
  simp only [sourceLoop, parses_source]
  dsimp only [bind, pure, Option.bind]
  apply congrArg some
  change executeForInSequence (extra + 120) [.forIn "_" collection body] before = _
  rw [executeForInSequence, header]
  dsimp only [bind, pure, Except.bind, Except.pure]
  rw [executed]
  simp [executeForInSequence]

/-- An actual enumerable own descriptor selects the entered case; neither its
key's truthiness nor its data value is tested. The body-derived proof covers
every legal order, including arbitrary empty-string/numeric-looking keys. -/
theorem source_entered_satisfies (extra : Nat) (before : ForInState) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (old params : Value) (m queue : Nat) (matched queued : IndexedArray) (input : JSString)
    (childrenInputs : ChildrenInputs before owner childrenIdentity children object)
    (inputs : BodyInputs before owner childrenIdentity paramsIdentity old params m queue matched queued input)
    (key : JSString) (descriptor : PropertyDescriptor) (found : object.own.lookup key = some descriptor)
    (enumerable : descriptorEnumerable descriptor = true) :
    pinnedSource = pinnedPrefix ++ NodeComponentCount.pinnedFullSource ++ pinnedSuffix ∧
    ∃ after, sourceLoop (extra + 120) before = some (.ok (.normal after)) ∧
      EnteredContract before after owner childrenIdentity children paramsIdentity object old params queue queued input ∧
      (∀ keys, LegalForInOrder object keys → executeForInKeys (extra + 119) "_" body keys before = .ok after) := by
  refine ⟨reassembles_source, ?_⟩
  have witness : ∃ key, EnumerableName object key := ⟨key, descriptor, found, enumerable⟩
  rcases inputs.admitted with falsy | ⟨target, initial, selected, targetFound, wellFormed, capacity⟩
  · let after := createdResult before owner paramsIdentity params queue queued input
    refine ⟨after, source_from_derived_body extra before after owner childrenIdentity children paramsIdentity object old params queue queued input childrenInputs witness ?_ ?_⟩
    · intro key _
      exact ⟨createdCompleted (bindForInKey "_" key before) owner paramsIdentity params queue queued input,
        body_created extra before key owner childrenIdentity children paramsIdentity object old params m queue matched queued input childrenInputs inputs falsy,
        created_scope before key owner paramsIdentity params queue queued input⟩
    · intro key name
      have scopedInputs := scoped_body_inputs before key owner childrenIdentity paramsIdentity old params m queue matched queued input inputs
      have component := execute_component_created extra (bindForInKey "_" key before).regexp m queue matched queued (.object owner) input
        scopedInputs.count scopedInputs.queue falsy
      exact contract_from_stages before after key owner childrenIdentity children paramsIdentity object old params m queue matched queued input childrenInputs inputs name
        (createdCompleted (bindForInKey "_" key before) owner paramsIdentity params queue queued input) component.2 rfl
        (created_scope before key owner paramsIdentity params queue queued input).symm
  · let after := reusedResult before owner paramsIdentity params target initial input
    refine ⟨after, source_from_derived_body extra before after owner childrenIdentity children paramsIdentity object old params queue queued input childrenInputs witness ?_ ?_⟩
    · intro key _
      exact ⟨reusedCompleted (bindForInKey "_" key before) owner paramsIdentity params target initial input,
        body_reused extra before key owner childrenIdentity children paramsIdentity object old params m queue target matched queued initial input childrenInputs inputs selected targetFound wellFormed capacity,
        reused_scope before key owner paramsIdentity params target initial input⟩
    · intro key name
      have scopedInputs := scoped_body_inputs before key owner childrenIdentity paramsIdentity old params m queue matched queued input inputs
      have component := execute_component_reused extra (bindForInKey "_" key before).regexp m queue target matched queued initial (.object owner) input
        scopedInputs.count scopedInputs.queue selected targetFound wellFormed capacity
      exact contract_from_stages before after key owner childrenIdentity children paramsIdentity object old params m queue matched queued input childrenInputs inputs name
        (reusedCompleted (bindForInKey "_" key before) owner paramsIdentity params target initial input) component.2 rfl
        (reused_scope before key owner paramsIdentity params target initial input).symm

/-- Descriptor inspection derives the branch. The independent empty theorem
above needs none of BodyInputs; these entered facts are used only if a real
enumerable own descriptor is found. -/
theorem source_satisfies (extra : Nat) (before : ForInState) (owner childrenIdentity children paramsIdentity : Nat)
    (object : OrdinaryObject) (old params : Value) (m queue : Nat) (matched queued : IndexedArray) (input : JSString)
    (childrenInputs : ChildrenInputs before owner childrenIdentity children object)
    (inputs : BodyInputs before owner childrenIdentity paramsIdentity old params m queue matched queued input) :
    ∃ after, sourceLoop (extra + 120) before = some (.ok (.normal after)) ∧ Contract before after owner childrenIdentity children object := by
  classical
  by_cases witness : ∃ key, EnumerableName object key
  · obtain ⟨key, descriptor, found, enumerable⟩ := witness
    obtain ⟨_, after, run, contract, _⟩ := source_entered_satisfies extra before owner childrenIdentity children paramsIdentity object old params m queue matched queued input childrenInputs inputs key descriptor found enumerable
    exact ⟨after, run, .entered paramsIdentity old params queue queued input contract⟩
  · have noneEnumerable : NoEnumerable object := by
      intro key descriptor found
      cases equation : descriptorEnumerable descriptor with
      | false => rfl
      | true => exact False.elim (witness ⟨key, descriptor, found, equation⟩)
    obtain ⟨_, run, contract⟩ := source_empty_satisfies extra before owner childrenIdentity children object childrenInputs noneEnumerable
    exact ⟨before, run, .empty contract⟩

end HonoLean.Upstream.NodeChildEnumeration
