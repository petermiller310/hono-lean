import HonoLean.Upstream.NodeQueueAdvance.Contract

namespace HonoLean.Upstream.NodeQueueAdvance

open SourceSubset ECMA2025

theorem cell_after_shift (before : State) (queue reference : Nat) (queued initial : List Value)
    (queueFound : before.heap[queue]? = some queued) (found : before.heap[reference]? = some initial) :
    (shiftState before queue queued).heap[reference]? = some (currentValues queue reference queued initial) := by
  have inside : queue < before.heap.length := List.getElem?_eq_some_iff.mp queueFound |>.1
  by_cases equal : reference = queue
  · subst reference
    simp [shiftState, currentValues, List.getElem?_set_self inside]
  · simpa [shiftState, currentValues, equal] using
      (List.getElem?_set_ne (Ne.symm equal) (a := queued.tail) (l := before.heap)).trans found

theorem shifted_length (before : State) (queue : Nat) (queued : List Value) :
    (shiftState before queue queued).heap.length = before.heap.length := by simp [shiftState]

theorem execute_shift (extra limit : Nat) (before : State) (queue : Nat) (queued : List Value)
    (binding : before.environment.lookup "curNodesQueue" = some (.array queue))
    (found : before.heap[queue]? = some queued) :
    evalExpression (extra + 9) limit shiftedExpression before =
      .ok (queued.headD .undefined, shiftState before queue queued) := by
  simp [shiftedExpression, evalExpression, lookupVariable, binding, found, evalArguments,
    intrinsic, shiftState, bind, pure, Except.bind, Except.pure]

private theorem execute_with_right (extra limit : Nat) (before : State) (queue temp : Nat)
    (queued temporary : List Value) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : Inputs before queue temp queued temporary front old back)
    (value : Value) (evaluated : State)
    (right : evalExpression (extra + 8) limit nextExpression (declaredState before queue queued) = .ok (value, evaluated)) :
    executeMutableSequence (extra + 10) limit mutableBindings program before =
      .ok (.normal (writeMutableBinding evaluated (front.length + 1) "curNodes" value)) := by
  have lexical : (declaredState before queue queued).environment =
      (("shifted", queued.headD .undefined) :: front) ++ ("curNodes", old) :: back := by
    simp [declaredState, inputs.lexical]
  have first : ((("shifted", queued.headD .undefined) :: front) : List (String × Value)).lookup "curNodes" = none := by
    simpa using inputs.first
  have rebound := executeMutableRebind_first (extra + 8) limit mutableBindings "curNodes" nextExpression
    (declaredState before queue queued) evaluated value old (("shifted", queued.headD .undefined) :: front) back
    (by decide) lexical first right
  simp only [List.length_cons] at rebound
  simp only [program, executeMutableSequence]
  rw [execute_shift extra limit before queue queued inputs.queueBinding inputs.queueFound]
  dsimp only [bind, Except.bind, pure, Except.pure]
  change (do
    let state ← executeMutableRebind (extra + 8) limit mutableBindings "curNodes" nextExpression (declaredState before queue queued)
    executeMutableSequence (extra + 8) limit mutableBindings [] state) = _
  rw [rebound]
  simp [executeMutableSequence, bind, Except.bind]

private theorem finish_environment (before : State) (queue : Nat) (queued : List Value)
    (front : List (String × Value)) (old : Value) (back : List (String × Value)) (value : Value) (heap : List (List Value))
    (lexical : before.environment = front ++ ("curNodes", old) :: back) :
    (finish before queue queued front value heap).environment =
      ("shifted", queued.headD .undefined) :: (front ++ ("curNodes", value) :: back) := by
  simpa [finish, declaredState] using writeMutableBinding_same_environment
    {declaredState before queue queued with heap} (("shifted", queued.headD .undefined) :: front) back
    "curNodes" old value (by simp [declaredState, lexical])

private theorem true_right (extra limit : Nat) (before : State) (queue temp : Nat) (queued temporary : List Value)
    (tempBinding : before.environment.lookup "tempNodes" = some (.array temp))
    (tempFound : (declaredState before queue queued).heap[temp]? = some temporary)
    (test : truthy (queued.headD .undefined) = true) :
    evalExpression (extra + 8) limit nextExpression (declaredState before queue queued) =
      intrinsic limit (.array temp) "concat" [queued.headD .undefined] (declaredState before queue queued) := by
  have binding : (declaredState before queue queued).environment.lookup "tempNodes" = some (.array temp) := by
    simpa [declaredState, List.lookup_cons] using tempBinding
  have shifted : (declaredState before queue queued).environment.lookup "shifted" = some (queued.headD .undefined) := by
    simp [declaredState]
  simp only [nextExpression, evalExpression, lookupVariable, shifted, binding, tempFound,
    test, evalArguments, bind, pure, Except.bind, Except.pure, ↓reduceIte,
    prepareMethod, String.reduceBEq, Bool.or_true, invokePrepared]

private theorem contract_of_contents (before : State) (queue temp : Nat) (queued temporary : List Value)
    (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : Inputs before queue temp queued temporary front old back) (value : Value) (heap : List (List Value))
    (contents : Contents before queue temp queued temporary value (finish before queue queued front value heap)) :
    Contract before queue temp queued temporary (finish before queue queued front value heap) := by
  have environment := finish_environment before queue queued front old back value heap inputs.lexical
  have queueBound := List.getElem?_eq_some_iff.mp inputs.queueFound |>.1
  refine ⟨inputs.queueBinding, inputs.tempBinding, inputs.queueFound, inputs.tempFound,
    ⟨front, old, back, value, inputs.lexical, inputs.first, environment, contents⟩,
    ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp [environment]
  · cases contents with
    | falsy _ _ heap => rw [heap]; exact List.getElem?_set_self queueBound
    | array _ _ _ _ _ _ _ _ heap =>
      rw [heap, List.getElem?_append_left (by simpa using queueBound)]
      exact List.getElem?_set_self queueBound
    | scalar _ _ _ _ _ heap =>
      rw [heap, List.getElem?_append_left (by simpa using queueBound)]
      exact List.getElem?_set_self queueBound
  · intro reference inside different
    cases contents with
    | falsy _ _ heap => rw [heap]; exact List.getElem?_set_ne (Ne.symm different)
    | array _ _ _ _ _ _ _ _ heap =>
      rw [heap, List.getElem?_append_left (by simpa using inside)]
      exact List.getElem?_set_ne (Ne.symm different)
    | scalar _ _ _ _ _ heap =>
      rw [heap, List.getElem?_append_left (by simpa using inside)]
      exact List.getElem?_set_ne (Ne.symm different)

theorem falsy_satisfies (extra limit : Nat) (before : State) (queue temp : Nat)
    (queued temporary : List Value) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : Inputs before queue temp queued temporary front old back)
    (test : truthy (queued.headD .undefined) = false) :
    sourceAdvance (extra + 10) limit before = some (.ok (.normal (falsyState before queue temp queued front))) ∧
    Contract before queue temp queued temporary (falsyState before queue temp queued front) := by
  have right : evalExpression (extra + 8) limit nextExpression (declaredState before queue queued) =
      .ok (.array temp, declaredState before queue queued) := by
    have binding : (declaredState before queue queued).environment.lookup "tempNodes" = some (.array temp) := by
      simpa [declaredState, List.lookup_cons] using inputs.tempBinding
    have shifted : (declaredState before queue queued).environment.lookup "shifted" = some (queued.headD .undefined) := by
      simp [declaredState]
    simp only [nextExpression, evalExpression, lookupVariable, shifted, binding, test,
      bind, pure, Except.bind, Except.pure, Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · simpa [sourceAdvance, parses_source, falsyState, finish, declaredState, shiftState] using
      congrArg some (execute_with_right extra limit before queue temp queued temporary front old back inputs _ _ right)
  · apply contract_of_contents before queue temp queued temporary front old back inputs
    exact .falsy test rfl rfl

theorem array_satisfies (extra limit : Nat) (before : State) (queue temp : Nat)
    (queued temporary : List Value) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : Inputs before queue temp queued temporary front old back)
    (argument : Nat) (initial : List Value) (head : queued.headD .undefined = .array argument)
    (argumentFound : before.heap[argument]? = some initial) :
    let copied := currentValues queue temp queued temporary ++ currentValues queue argument queued initial
    sourceAdvance (extra + 10) limit before = some (.ok (.normal (copiedState before queue queued copied front))) ∧
    Contract before queue temp queued temporary (copiedState before queue queued copied front) := by
  let copied := currentValues queue temp queued temporary ++ currentValues queue argument queued initial
  have tempFound := cell_after_shift before queue temp queued temporary inputs.queueFound inputs.tempFound
  have argFound := cell_after_shift before queue argument queued initial inputs.queueFound argumentFound
  have right : evalExpression (extra + 8) limit nextExpression (declaredState before queue queued) =
      .ok (.array before.heap.length,
        {declaredState before queue queued with heap := (shiftState before queue queued).heap ++ [copied]}) := by
    have tempFound' : (declaredState before queue queued).heap[temp]? = some (currentValues queue temp queued temporary) := tempFound
    have argFound' : (declaredState before queue queued).heap[argument]? = some (currentValues queue argument queued initial) := argFound
    rw [true_right extra limit before queue temp queued _ inputs.tempBinding tempFound' (by rw [head]; rfl), head,
      intrinsic_concat _ _ _ _ _ tempFound' argFound' limit]
    simp [declaredState, shiftState, copied]
  refine ⟨?_, ?_⟩
  · simpa [sourceAdvance, parses_source, copiedState, finish, copied] using
      congrArg some (execute_with_right extra limit before queue temp queued temporary front old back inputs _ _ right)
  · apply contract_of_contents before queue temp queued temporary front old back inputs
    exact .array argument initial copied head argumentFound rfl (by simp [finish, shiftState, writeMutableBinding, copied])
      (append_denseConcatContents _ _) rfl

theorem scalar_satisfies (extra limit : Nat) (before : State) (queue temp : Nat)
    (queued temporary : List Value) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : Inputs before queue temp queued temporary front old back)
    (test : truthy (queued.headD .undefined) = true)
    (notArray : ∀ reference, queued.headD .undefined ≠ .array reference) :
    let copied := currentValues queue temp queued temporary ++ [queued.headD .undefined]
    sourceAdvance (extra + 10) limit before = some (.ok (.normal (copiedState before queue queued copied front))) ∧
    Contract before queue temp queued temporary (copiedState before queue queued copied front) := by
  let copied := currentValues queue temp queued temporary ++ [queued.headD .undefined]
  have tempFound : (declaredState before queue queued).heap[temp]? = some (currentValues queue temp queued temporary) :=
    cell_after_shift before queue temp queued temporary inputs.queueFound inputs.tempFound
  have right : evalExpression (extra + 8) limit nextExpression (declaredState before queue queued) =
      .ok (.array before.heap.length,
        {declaredState before queue queued with heap := (shiftState before queue queued).heap ++ [copied]}) := by
    rw [true_right extra limit before queue temp queued _ inputs.tempBinding tempFound test,
      intrinsic_concat_scalar _ _ _ _ tempFound notArray limit]
    simp [declaredState, shiftState, copied]
  refine ⟨?_, ?_⟩
  · simpa [sourceAdvance, parses_source, copiedState, finish, copied] using
      congrArg some (execute_with_right extra limit before queue temp queued temporary front old back inputs _ _ right)
  · apply contract_of_contents before queue temp queued temporary front old back inputs
    exact .scalar test notArray copied rfl (append_denseConcatContents _ _) rfl

/-- The only extra normal-domain condition is initial allocation of an array
at the queue head. No facts about the completed shift or concat are supplied. -/
theorem source_advance_satisfies (extra limit : Nat) (before : State) (queue temp : Nat)
    (queued temporary : List Value) (front : List (String × Value)) (old : Value) (back : List (String × Value))
    (inputs : Inputs before queue temp queued temporary front old back)
    (headAllocated : ∀ argument, queued.headD .undefined = .array argument →
      ∃ initial, before.heap[argument]? = some initial) :
    ∃ after, sourceAdvance (extra + 10) limit before = some (.ok (.normal after)) ∧
      Contract before queue temp queued temporary after := by
  classical
  by_cases test : truthy (queued.headD .undefined) = false
  · exact ⟨_, falsy_satisfies extra limit before queue temp queued temporary front old back inputs test⟩
  · have truth : truthy (queued.headD .undefined) = true := by
      cases equation : truthy (queued.headD .undefined) with
      | false => exact False.elim (test equation)
      | true => rfl
    by_cases array : ∃ argument, queued.headD .undefined = .array argument
    · obtain ⟨argument, head⟩ := array
      obtain ⟨initial, found⟩ := headAllocated argument head
      exact ⟨_, array_satisfies extra limit before queue temp queued temporary front old back inputs argument initial head found⟩
    · exact ⟨_, scalar_satisfies extra limit before queue temp queued temporary front old back inputs truth
        (by intro argument equal; exact array ⟨argument, equal⟩)⟩

theorem falsy_allocates_nothing (before : State) (queue temp : Nat) (queued : List Value)
    (front : List (String × Value)) :
    (falsyState before queue temp queued front).heap.length = before.heap.length := by
  simp [falsyState, finish, writeMutableBinding, shiftState]

theorem copied_allocates_one (before : State) (queue : Nat) (queued copied : List Value)
    (front : List (String × Value)) :
    (copiedState before queue queued copied front).heap.length = before.heap.length + 1 := by
  simp [copiedState, finish, writeMutableBinding, shiftState]

end HonoLean.Upstream.NodeQueueAdvance
