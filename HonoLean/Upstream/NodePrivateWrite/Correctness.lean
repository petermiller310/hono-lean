import HonoLean.Upstream.NodePrivateWrite.Contract
import HonoLean.Upstream.NodeClass.Correctness

namespace HonoLean.Upstream.NodePrivateWrite

open SourceSubset ECMA2025

theorem replace_data_contract (elements : List (Nat × PrivateElement))
    (identity : Nat) (old value : Value) (found : elements.lookup identity = some (.data old)) :
    DataReplacement identity old value elements (replacePrivateData identity value elements) := by
  induction elements with
  | nil => simp at found
  | cons entry rest ih =>
    obtain ⟨key, element⟩ := entry
    by_cases equal : identity = key
    · subst key
      have same : element = .data old := by simpa [List.lookup] using found
      subst element
      exact ⟨[], rest, by simp, rfl, by simp [replacePrivateData]⟩
    · have different : (identity == key) = false := beq_eq_false_iff_ne.mpr equal
      have tail : rest.lookup identity = some (.data old) := by simpa [List.lookup, different] using found
      obtain ⟨leading, trailing, absent, prior, changed⟩ := ih tail
      refine ⟨(key, element) :: leading, trailing, ?_, ?_, ?_⟩
      · simpa using And.intro equal absent
      · simp [prior]
      · simp [replacePrivateData, different, changed]

theorem replace_owner_contract (elements : List (Nat × List (Nat × PrivateElement)))
    (owner identity : Nat) (old value : Value) (fields : List (Nat × PrivateElement))
    (found : elements.lookup owner = some fields) (field : fields.lookup identity = some (.data old)) :
    PrivateReplacement owner identity old value elements (replacePrivateOwner owner identity value elements) := by
  induction elements with
  | nil => simp at found
  | cons entry rest ih =>
    obtain ⟨key, entries⟩ := entry
    by_cases equal : owner = key
    · subst key
      have same : entries = fields := by simpa [List.lookup] using found
      subst entries
      exact ⟨[], rest, fields, replacePrivateData identity value fields, by simp, rfl,
        by simp [replacePrivateOwner], replace_data_contract fields identity old value field⟩
    · have different : (owner == key) = false := beq_eq_false_iff_ne.mpr equal
      have tail : rest.lookup owner = some fields := by simpa [List.lookup, different] using found
      obtain ⟨leading, trailing, oldFields, newFields, absent, prior, changed, relation⟩ := ih tail
      refine ⟨(key, entries) :: leading, trailing, oldFields, newFields, ?_, ?_, ?_, relation⟩
      · simpa using And.intro equal absent
      · simp [prior]
      · simp [replacePrivateOwner, different, changed]

theorem write_contract (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) :
    WriteContract before (writePrivateDataState before owner identity value) owner identity old value value := by
  obtain ⟨fields, found, field⟩ := writable.data
  exact ⟨rfl, replace_owner_contract before.privates.elements owner identity old value fields found field,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem setter (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) :
    privateSet (.object owner) identity value before = .ok (writePrivateDataState before owner identity value) := by
  obtain ⟨object, allocated⟩ := writable.allocated
  obtain ⟨fields, brand, field⟩ := writable.data
  exact privateSet_data before owner identity value old object fields allocated brand field

theorem run_reset (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) (reads : ResetReads before owner value) :
    executeAssignment 32 defaultSplitLimit reset before =
      .ok (value, writePrivateDataState before owner identity value) := by
  have set := setter before owner identity old value writable
  simp [executeAssignment, reset, evalAssignmentReference, evalExpression, reads.receiver,
    lookupVariable, writable.scope, reads.binding, putAssignmentReference, set,
    bind, pure, Except.bind, Except.pure]

theorem run_propagation (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) (reads : PropagationReads before owner value) :
    executeAssignment 32 defaultSplitLimit propagation before =
      .ok (value, writePrivateDataState before owner identity value) := by
  obtain ⟨source, bound, read⟩ := reads.source
  have set := setter before owner identity old value writable
  simp [executeAssignment, propagation, evalAssignmentReference, evalExpression, lookupVariable,
    reads.target, writable.scope, bound, read, putAssignmentReference, set,
    bind, pure, Except.bind, Except.pure]

theorem run_parameter (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) (reads : ParameterReads before owner value) :
    executeAssignment 32 defaultSplitLimit parameter before =
      .ok (value, writePrivateDataState before owner identity value) := by
  have set := setter before owner identity old value writable
  simp [executeAssignment, parameter, evalAssignmentReference, evalExpression, lookupVariable,
    reads.target, writable.scope, reads.binding, putAssignmentReference, set,
    bind, pure, Except.bind, Except.pure]

theorem parsed_reset_satisfies (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) (reads : ResetReads before owner value) :
    ∃ after,
      (parseAssignment pinnedResetSource resetBindings NodePrivateCall.classPrivateNames true).map
        (fun assignment => executeAssignment 32 defaultSplitLimit assignment before) = some (.ok (value, after)) ∧
      WriteContract before after owner identity old value value := by
  exact ⟨writePrivateDataState before owner identity value,
    by rw [parses_reset, Option.map_some, run_reset before owner identity old value writable reads],
    write_contract before owner identity old value writable⟩

theorem parsed_propagation_satisfies (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) (reads : PropagationReads before owner value) :
    ∃ after,
      (parseAssignment pinnedPropagationSource propagationBindings NodePrivateCall.classPrivateNames).map
        (fun assignment => executeAssignment 32 defaultSplitLimit assignment before) = some (.ok (value, after)) ∧
      WriteContract before after owner identity old value value := by
  exact ⟨writePrivateDataState before owner identity value,
    by rw [parses_propagation, Option.map_some, run_propagation before owner identity old value writable reads],
    write_contract before owner identity old value writable⟩

theorem parsed_parameter_satisfies (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) (reads : ParameterReads before owner value) :
    ∃ after,
      (parseAssignment pinnedParameterSource parameterBindings NodePrivateCall.classPrivateNames).map
        (fun assignment => executeAssignment 32 defaultSplitLimit assignment before) = some (.ok (value, after)) ∧
      WriteContract before after owner identity old value value := by
  exact ⟨writePrivateDataState before owner identity value,
    by rw [parses_parameter, Option.map_some, run_parameter before owner identity old value writable reads],
    write_contract before owner identity old value writable⟩

theorem parsed_wildcard_satisfies (before : State) (owner identity : Nat) (old value : Value)
    (writable : Writable before owner identity old) (reads : ParameterReads before owner value) :
    ∃ after,
      (parseAssignment pinnedWildcardSource parameterBindings NodePrivateCall.classPrivateNames).map
        (fun assignment => executeAssignment 32 defaultSplitLimit assignment before) = some (.ok (value, after)) ∧
      WriteContract before after owner identity old value value := by
  exact ⟨writePrivateDataState before owner identity value,
    by rw [parses_wildcard, Option.map_some, run_parameter before owner identity old value writable reads],
    write_contract before owner identity old value writable⟩

/-- The source-derived tagged initialization contract proves that params is a
writable DATA element. A function-valued data field would remain DATA as well. -/
theorem initialized_params_writable (before after : State) (prototype : Option Nat)
    (firstIdentity firstHandle owner : Nat) (emptyParams : Value)
    (contract : NodeClass.InstanceContract before after prototype firstIdentity firstHandle owner emptyParams) :
    Writable (NodeClass.classActivation after firstIdentity) owner (firstIdentity + 4) emptyParams := by
  obtain ⟨fields, elements, stored⟩ := contract.tagged
  refine ⟨?_, ?_, fields, ?_, stored.2.2.2.2.1⟩
  · simp [NodeClass.classActivation, NodeClass.names, NodeInitialization.nodeNames, List.lookup]
  · exact ⟨⟨[], prototype, true⟩,
      NodeInitialization.contract_owner_found before after prototype firstIdentity owner emptyParams contract.toInstanceContract⟩
  · simp [NodeClass.classActivation, elements]

/-- Read-only status follows from the source-installed METHOD tag, not the
fact that its current value happens to be a function reference. -/
theorem initialized_method_read_only (before after : State) (prototype : Option Nat)
    (firstIdentity firstHandle owner : Nat) (emptyParams value : Value)
    (contract : NodeClass.InstanceContract before after prototype firstIdentity firstHandle owner emptyParams) :
    privateSet (.object owner) (firstIdentity + 5) value
      (NodeClass.classActivation after firstIdentity) = .error .privateReadOnly := by
  obtain ⟨fields, elements, stored⟩ := contract.tagged
  refine privateSet_method _ owner (firstIdentity + 5) value (.function firstHandle)
    ⟨[], prototype, true⟩ fields ?_ ?_ stored.2.2.2.2.2
  · exact NodeInitialization.contract_owner_found before after prototype firstIdentity owner emptyParams contract.toInstanceContract
  · simp [NodeClass.classActivation, elements]

end HonoLean.Upstream.NodePrivateWrite
