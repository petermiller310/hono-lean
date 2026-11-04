import HonoLean.Upstream.NodeFirstLiteral.Contract

namespace HonoLean.Upstream.NodeFirstLiteral

open SourceSubset ECMA2025 MethodsLoopInitial

def selected (before : State) (owner stamp emptyParams : Nat) (path : JSString) : State :=
  NodeLoopEntry.selected before owner (stamp + 4) emptyParams path

def targetOld (owner target emptyParams : Nat) (old : Value) : Value :=
  if target = owner then .object emptyParams else old

theorem selected_objects (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).objects = before.objects := rfl

theorem selected_functions (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).functions = before.functions := rfl

theorem selected_privates (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).privates =
      (writePrivateDataState before owner (stamp + 4) (.object emptyParams)).privates := rfl

theorem selected_heap (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).heap =
      before.heap ++ [[], [.object owner], (NodeSearchSetup.producedParts path).map Value.string, [], []] := by
  simp [selected, NodeLoopEntry.selected, NodeIterationSetup.nodeState, NodeLoopEntry.innerState, NodeLoopEntry.iterated,
    NodeIterationSetup.outerState, NodeLoopEntry.outerState, NodeLoopEntry.started, NodeSearchSetup.resultState, List.append_assoc]

theorem privateGet_selected (before : State) (owner stamp emptyParams receiver : Nat) (path : JSString) (name : String) :
    privateGet (.object receiver) name (selected before owner stamp emptyParams path) =
      privateGet (.object receiver) name (writePrivateDataState before owner (stamp + 4) (.object emptyParams)) := rfl

theorem selected_node (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).environment.lookup "node" = some (.object owner) := by
  simp [selected, NodeLoopEntry.selected, NodeIterationSetup.nodeState, NodeIterationSetup.selectedNode]

theorem selected_method (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).environment.lookup "method" = before.environment.lookup "method" := by
  simp only [selected, NodeLoopEntry.selected, NodeIterationSetup.nodeState, List.lookup_cons,
    beq_false_of_ne (by decide : "method" ≠ "node")]
  rw [NodeLoopEntry.inner_other _ 1 "method" (by decide) (by decide)]
  simp only [NodeLoopEntry.iterated, NodeIterationSetup.outerState, List.cons_append, List.nil_append, List.lookup_cons,
    beq_false_of_ne (by decide : "method" ≠ "tempNodes"), beq_false_of_ne (by decide : "method" ≠ "isLast"),
    beq_false_of_ne (by decide : "method" ≠ "part")]
  rw [NodeLoopEntry.outer_other _ "method" (by decide)]
  simp [NodeLoopEntry.started, NodeSearchSetup.resultState, NodeSearchSetup.resultEnvironment, List.lookup]

theorem selected_collector (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).environment.lookup "handlerSets" = some (.array before.heap.length) := by
  simp only [selected, NodeLoopEntry.selected, NodeIterationSetup.nodeState, List.lookup_cons,
    beq_false_of_ne (by decide : "handlerSets" ≠ "node")]
  rw [NodeLoopEntry.inner_other _ 1 "handlerSets" (by decide) (by decide)]
  simp only [NodeLoopEntry.iterated, NodeIterationSetup.outerState, List.cons_append, List.nil_append, List.lookup_cons,
    beq_false_of_ne (by decide : "handlerSets" ≠ "tempNodes"), beq_false_of_ne (by decide : "handlerSets" ≠ "isLast"),
    beq_false_of_ne (by decide : "handlerSets" ≠ "part")]
  rw [NodeLoopEntry.outer_other _ "handlerSets" (by decide)]
  simp [NodeLoopEntry.started, NodeSearchSetup.resultState, NodeSearchSetup.resultEnvironment, List.lookup]

theorem selected_part (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).environment.lookup "part" = some (.string (firstPart path)) := by
  simp only [selected, NodeLoopEntry.selected, NodeIterationSetup.nodeState, List.lookup_cons,
    beq_false_of_ne (by decide : "part" ≠ "node")]
  rw [NodeLoopEntry.inner_other _ 1 "part" (by decide) (by decide)]
  simp [NodeLoopEntry.iterated, NodeIterationSetup.outerState, firstPart, List.lookup]

theorem selected_last (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).environment.lookup "isLast" =
      some (NodeIterationSetup.lastValue (NodeSearchSetup.producedParts path) 0) := by
  simp only [selected, NodeLoopEntry.selected, NodeIterationSetup.nodeState, List.lookup_cons,
    beq_false_of_ne (by decide : "isLast" ≠ "node")]
  rw [NodeLoopEntry.inner_other _ 1 "isLast" (by decide) (by decide)]
  simp [NodeLoopEntry.iterated, NodeIterationSetup.outerState, List.lookup]

theorem selected_temp (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).environment.lookup "tempNodes" = some (.array (before.heap.length + 4)) := by
  simp only [selected, NodeLoopEntry.selected, NodeIterationSetup.nodeState, List.lookup_cons,
    beq_false_of_ne (by decide : "tempNodes" ≠ "node")]
  rw [NodeLoopEntry.inner_other _ 1 "tempNodes" (by decide) (by decide)]
  simp [NodeLoopEntry.iterated, NodeIterationSetup.outerState, NodeLoopEntry.outerState, NodeLoopEntry.started, NodeSearchSetup.resultState]

theorem selected_temp_empty (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).heap[before.heap.length + 4]? = some [] := by simp [selected_heap]

theorem selected_collector_empty (before : State) (owner stamp emptyParams : Nat) (path : JSString) :
    (selected before owner stamp emptyParams path).heap[before.heap.length]? = some [] := by simp [selected_heap]

/-- The root's source88 reset changes a self-child's old DATA value. Other
children retain their old value. This case split is a derived framing fact. -/
theorem selected_writable (before : State) (owner target stamp emptyParams : Nat) (path : JSString) (old : Value)
    (writable : NodePrivateWrite.Writable before target (stamp + 4) old) :
    NodePrivateWrite.Writable (selected before owner stamp emptyParams path) target (stamp + 4)
      (targetOld owner target emptyParams old) := by
  refine ⟨writable.scope, writable.allocated, ?_⟩
  obtain ⟨fields, brand, field⟩ := writable.data
  by_cases same : target = owner
  · subst target
    refine ⟨replacePrivateData (stamp + 4) (.object emptyParams) fields, ?_, ?_⟩
    · rw [selected_privates]
      exact replacePrivateOwner_found before.privates.elements owner (stamp + 4) (.object emptyParams) fields brand
    · simpa [targetOld] using replacePrivateData_found fields (stamp + 4) (.object emptyParams) (.data old) field
  · refine ⟨fields, ?_, ?_⟩
    · rw [selected_privates]
      exact (replacePrivateOwner_other before.privates.elements owner (stamp + 4) target (.object emptyParams) same).trans brand
    · simpa [targetOld, same] using field

theorem selected_private_other (before : State) (owner receiver stamp emptyParams : Nat) (path : JSString)
    (name : String) (identity : Nat) (old value : Value)
    (writable : NodePrivateWrite.Writable before owner (stamp + 4) old)
    (lexical : before.privates.names.lookup name = some identity) (different : identity ≠ stamp + 4)
    (read : privateGet (.object receiver) name before = .ok value) :
    privateGet (.object receiver) name (selected before owner stamp emptyParams path) = .ok value := by
  rw [privateGet_selected]
  by_cases same : receiver = owner
  · subst receiver
    obtain ⟨fields, brand, _⟩ := writable.data
    rw [privateGet_write_other_identity before owner (stamp + 4) identity (.object emptyParams) name fields lexical brand different]
    exact read
  · rw [privateGet_write_other_owner before owner (stamp + 4) receiver (.object emptyParams) name same]
    exact read

theorem selected_parent_params (before : State) (owner stamp emptyParams : Nat) (path : JSString) (old : Value)
    (writable : NodePrivateWrite.Writable before owner (stamp + 4) old) :
    privateGet (.object owner) "params" (selected before owner stamp emptyParams path) = .ok (.object emptyParams) := by
  rw [privateGet_selected]
  obtain ⟨object, allocated⟩ := writable.allocated
  obtain ⟨fields, brand, field⟩ := writable.data
  exact privateGet_write_same before owner (stamp + 4) "params" (.object emptyParams) old object fields writable.scope allocated brand field

theorem selected_callable (before : State) (methods : PrivateMethodTable) (closure : PrivateMethodClosure)
    (owner stamp handle emptyParams : Nat) (path : JSString) (old : Value)
    (scope : before.privates.names = NodeClass.names stamp)
    (writable : NodePrivateWrite.Writable before owner (stamp + 4) old)
    (callable : NodePrivateCall.Callable before methods closure owner handle) :
    NodePrivateCall.Callable (selected before owner stamp emptyParams path) methods closure owner handle := by
  refine ⟨callable.sourceProgram, callable.tableSeparate, callable.handleBound, callable.closureFound, ?_⟩
  exact selected_private_other before owner owner stamp emptyParams path "pushHandlerSets" (stamp + 5) old (.function handle) writable
    (by simp [scope, NodeClass.names, NodeInitialization.nodeNames, List.lookup]) (by omega) callable.privateRead

theorem selected_installed (before : State) (owner stamp handle emptyParams : Nat) (path : JSString)
    (installed : InstalledMethod before owner stamp handle) :
    InstalledMethod (selected before owner stamp emptyParams path) owner stamp handle := by
  obtain ⟨fields, brand, tag⟩ := installed
  refine ⟨replacePrivateData (stamp + 4) (.object emptyParams) fields, ?_, ?_⟩
  · rw [selected_privates]
    exact replacePrivateOwner_found before.privates.elements owner (stamp + 4) (.object emptyParams) fields brand
  · rw [replacePrivateData_other fields (stamp + 4) (stamp + 5) (.object emptyParams) (by omega)]
    exact tag

theorem selected_storage (before : State) (closure : PrivateMethodClosure) (owner target stamp emptyParams : Nat)
    (path : JSString) (old : Value)
    (writable : NodePrivateWrite.Writable before owner (stamp + 4) old)
    (storage : Storage before closure target stamp) :
    NodePrivateCall.Storage (selected before owner stamp emptyParams path) closure target stamp storage.methods before.heap.length storage.rows := by
  have separate : before.heap.length ≠ storage.methods := by
    have := (List.getElem?_eq_some_iff.mp storage.methodsFound).1
    omega
  have initial : NodePrivateCall.Storage before closure target stamp storage.methods before.heap.length storage.rows :=
    ⟨storage.targetFound, storage.privateName, storage.privateSlot, storage.methodsFound, separate, storage.legalLength⟩
  have resetStorage := NodeLiteralBranch.storage_after_propagation before closure owner target stamp storage.methods before.heap.length emptyParams storage.rows old writable initial
  refine ⟨storage.targetFound, storage.privateName, resetStorage.privateSlot, ?_, separate, storage.legalLength⟩
  exact NodeIterationSetup.old_array_append [[], [.object owner], (NodeSearchSetup.producedParts path).map Value.string, [], []]
    (selected_heap before owner stamp emptyParams path) storage.methods storage.rows storage.methodsFound

theorem selected_layout (before : State) (closure : PrivateMethodClosure) (owner target stamp emptyParams keyBound : Nat)
    (path query : JSString) (rows : List Value) (records : List Record)
    (facts : Uncollected before closure.environment rows query keyBound records emptyParams) :
    Layout (NodePrivateCall.bodyState (selected before owner stamp emptyParams path) closure (.object owner) before.heap.length target query emptyParams .undefined)
      rows query before.heap.length keyBound records .undefined emptyParams [] :=
  body_layout_from_uncollected before (selected before owner stamp emptyParams path) closure.environment rows query keyBound records emptyParams
    closure (.object owner) target [[.object owner], (NodeSearchSetup.producedParts path).map Value.string, [], []]
    facts rfl (selected_objects before owner stamp emptyParams path) (selected_functions before owner stamp emptyParams path)
    (selected_heap before owner stamp emptyParams path)

/-- Literal processing changes only the collector array (terminal helpers)
or the temporary queue (nonlast append). No future frame is supplied. -/
theorem literal_array_frame {before after : State} {closure : PrivateMethodClosure} {next : Value}
    {owner collector temp stamp emptyParams : Nat} {query : JSString}
    (contract : NodeLiteralBranch.BranchContract before closure next owner collector temp stamp query emptyParams after) :
    ∀ reference, reference ≠ collector → reference ≠ temp → after.heap[reference]? = before.heap[reference]? := by
  cases contract with
  | missing falsy => intro reference _ _; rfl
  | nonlast target equal last lastBinding falsy old written write prior tempFound capacity =>
    intro reference _ notTemp
    have changed : (NodeLiteralBranch.enqueuedState written temp prior next).heap[reference]? = written.heap[reference]? :=
      List.getElem?_set_ne (Ne.symm notTemp)
    exact changed.trans (congrArg (fun heap => heap[reference]?) write.heap)
  | direct target equal last lastBinding lastTruthy old written write children wildcard childrenRead wildcardRead wildcardFalsy methods rows storage after call tempFrame =>
    intro reference notCollector _
    have frames := NodeLiteralBranch.call_frames call rfl rfl rfl rfl rfl
    exact (frames.2.2.2.2.2.2 reference notCollector).trans (congrArg (fun heap => heap[reference]?) write.heap)
  | wildcard target wildcardTarget equal last lastBinding lastTruthy old written write children childrenRead wildcardRead wildcardMethods literalMethods wildcardRows literalRows middle after wildcardStorage directStorage wildcardCall directCall tempFrame =>
    intro reference notCollector _
    have first := NodeLiteralBranch.call_frames wildcardCall rfl rfl rfl rfl rfl
    have second := NodeLiteralBranch.call_frames directCall rfl rfl rfl rfl rfl
    exact ((second.2.2.2.2.2.2 reference notCollector).trans (first.2.2.2.2.2.2 reference notCollector)).trans
      (congrArg (fun heap => heap[reference]?) write.heap)

theorem old_arrays_after_literal (before after : State) (closure : PrivateMethodClosure)
    (owner stamp emptyParams : Nat) (path query : JSString) (next : Value)
    (contract : NodeLiteralBranch.BranchContract (selected before owner stamp emptyParams path) closure next owner before.heap.length
      (before.heap.length + 4) stamp query emptyParams after) :
    ∀ reference, reference < before.heap.length → after.heap[reference]? = before.heap[reference]? := by
  intro reference inside
  rw [literal_array_frame contract reference (by omega) (by omega), selected_heap,
    List.getElem?_append_left inside]

/-- Actual source-produced current nodes, split parts and pending queue are
preserved by every literal path; neither h nor h+4 is one of these arrays. -/
theorem source_arrays_after_literal (before after : State) (closure : PrivateMethodClosure)
    (owner stamp emptyParams : Nat) (path query : JSString) (next : Value)
    (contract : NodeLiteralBranch.BranchContract (selected before owner stamp emptyParams path) closure next owner before.heap.length
      (before.heap.length + 4) stamp query emptyParams after) :
    after.heap[before.heap.length + 1]? = some [.object owner] ∧
    after.heap[before.heap.length + 2]? = some ((NodeSearchSetup.producedParts path).map Value.string) ∧
    after.heap[before.heap.length + 3]? = some [] := by
  have one := literal_array_frame contract (before.heap.length + 1) (by omega) (by omega)
  have two := literal_array_frame contract (before.heap.length + 2) (by omega) (by omega)
  have three := literal_array_frame contract (before.heap.length + 3) (by omega) (by omega)
  simpa [selected_heap] using And.intro one (And.intro two three)

end HonoLean.Upstream.NodeFirstLiteral
