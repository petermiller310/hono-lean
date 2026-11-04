import HonoLean.Upstream.NodePatternBinding.Contract

set_option autoImplicit false
namespace HonoLean.Upstream.NodePatternBinding
open SourceSubset ECMA2025

 theorem realm_separated (before : ArrayBindingState) (context : ArrayIteratorContext)
    (valuesHandle nextHandle : Nat) (returned : Value) (inputs : Realm before context valuesHandle nextHandle returned) :
    iteratorTablesSeparated context before.regexp.ambient = true := by
  simp [iteratorTablesSeparated, inputs.noArgBefore, inputs.methodsBefore, inputs.functionsBefore,
    inputs.membersBefore, inputs.regexpBefore, inputs.constructorsBefore]

 theorem realm_values_identity (before : ArrayBindingState) (context : ArrayIteratorContext)
    (valuesHandle nextHandle : Nat) (returned : Value) (inputs : Realm before context valuesHandle nextHandle returned) :
    iteratorBuiltinAt context.builtins (.function valuesHandle) = some .arrayValues := by
  simp [iteratorBuiltinAt, inputs.valuesBound, inputs.valuesIdentity]

 theorem realm_next_identity (before : ArrayBindingState) (context : ArrayIteratorContext)
    (valuesHandle nextHandle : Nat) (returned : Value) (inputs : Realm before context valuesHandle nextHandle returned) :
    iteratorBuiltinAt context.builtins (.function nextHandle) = some .arrayNext := by
  simp [iteratorBuiltinAt, inputs.nextBound, inputs.nextIdentity]

 theorem current_method (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value)
    (inputs : Inputs before context pattern valuesHandle nextHandle values returned) :
    getArrayIteratorMethod context pattern before = .ok (.function valuesHandle) := by
  obtain ⟨object, found⟩ := inputs.arrayPrototypeFound
  unfold getArrayIteratorMethod
  rw [inputs.found, inputs.noOwnIterator]
  change lookupIteratorSymbol (31 + 1) before context.arrayPrototype = _
  rw [lookupIteratorSymbol, found, inputs.symbol]

 theorem acquire (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value)
    (inputs : Inputs before context pattern valuesHandle nextHandle values returned) :
    getArrayIterator context (.array pattern) before =
      .ok (record before nextHandle, acquired before context pattern valuesHandle nextHandle) := by
  obtain ⟨object, found⟩ := inputs.iteratorPrototypeFound
  obtain ⟨depth, path, bound⟩ := inputs.nextPath
  exact getArrayIterator_standard context pattern before (.function valuesHandle) (.function nextHandle) object
    (current_method before context pattern valuesHandle nextHandle values returned inputs)
    (realm_separated before context valuesHandle nextHandle returned inputs.toRealm)
    (realm_values_identity before context valuesHandle nextHandle returned inputs.toRealm) found inputs.closed
    (NodeCaptureGuard.descriptor_path_lookup _ _ _ _ _ _ path bound)

 theorem step_objects (context : ArrayIteratorContext) (iterator pattern index : Nat) (values : List Value)
    (before : ArrayBindingState) (readValue : Bool) :
    (stepState context iterator pattern index values before readValue).regexp.ambient.objects =
      before.regexp.ambient.objects ++ [iteratorResultObject context.resultPrototype (values[index]?.getD .undefined) false] := by rfl

 theorem step_yield (context : ArrayIteratorContext) (iterator pattern index nextHandle : Nat) (values : List Value)
    (before : ArrayBindingState) (root : OrdinaryObject)
    (cursor : before.iterators.lookup iterator = some ⟨some pattern, index⟩)
    (found : before.regexp.ambient.heap[pattern]? = some values)
    (rootFound : before.regexp.ambient.objects[context.resultPrototype]? = some root)
    (inBounds : index < values.length)
    (separated : iteratorTablesSeparated context before.regexp.ambient = true)
    (identity : iteratorBuiltinAt context.builtins (.function nextHandle) = some .arrayNext) :
    iteratorStep context ⟨iterator, .function nextHandle, false⟩ before =
      .ok (some before.regexp.ambient.objects.length, ⟨iterator, .function nextHandle, false⟩,
        stepState context iterator pattern index values before false) ∧
    iteratorStepValue context ⟨iterator, .function nextHandle, false⟩ before =
      .ok (values[index]?.getD .undefined, ⟨iterator, .function nextHandle, false⟩,
        stepState context iterator pattern index values before true) := by
  have next := (invokeArrayIteratorNext_saved context ⟨iterator, .function nextHandle, false⟩ before separated identity).trans
    (arrayIteratorNext_yield context iterator pattern index values before root cursor found rootFound inBounds)
  have resultFound : (iteratorYieldState context iterator pattern index values before).regexp.ambient.objects[before.regexp.ambient.objects.length]? =
      some (iteratorResultObject context.resultPrototype (values[index]?.getD .undefined) false) := by
    simp [iteratorYieldState, iteratorResultState, setArrayIteratorCursor]
  have doneRead := getProperty_data _ _ (propertyFuel - 1) iteratorDoneKey _ (.boolean false) true true true resultFound (by rfl)
  have valueRead := getProperty_data _ _ (propertyFuel - 1) iteratorValueKey _ (values[index]?.getD .undefined) true true true resultFound (by rfl)
  constructor
  · simpa [stepState] using iteratorStep_yield context ⟨iterator, .function nextHandle, false⟩ before _ _ rfl next doneRead
  · simpa [stepState, List.append_assoc] using iteratorStepValue_yield context ⟨iterator, .function nextHandle, false⟩ before _ _ _ rfl next doneRead valueRead

 theorem beforeClose_objects (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) :
    (beforeClose before context pattern valuesHandle nextHandle values).regexp.ambient.objects =
      before.regexp.ambient.objects ++ addedObjects before context values := by
  simp [beforeClose, secondState, firstState, initialized, stepState, iteratorYieldState, iteratorResultState, setArrayIteratorCursor,
    acquired, arrayIteratorAcquiredState, allocateArrayIterator, addedObjects, List.append_assoc]

 theorem close_read (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value)
    (inputs : Realm before context valuesHandle nextHandle returned) :
    getProperty propertyFuel (beforeClose before context pattern valuesHandle nextHandle values).regexp.ambient.objects
      before.regexp.ambient.objects.length iteratorReturnKey = .ok returned := by
  obtain ⟨descriptor, depth, path, bound, pureRead⟩ := inputs.returnPath
  rw [beforeClose_objects]
  have appended := NodeCaptureGuard.descriptor_path_append before.regexp.ambient.objects (addedObjects before context values)
    iteratorReturnKey context.iteratorPrototype descriptor depth path
  have found : (before.regexp.ambient.objects ++ addedObjects before context values)[before.regexp.ambient.objects.length]? =
      some (arrayIteratorObject context.iteratorPrototype) := by simp [addedObjects]
  have full := NodeCaptureGuard.DescriptorPath.parent found (by rfl) (by rfl) appended
  exact iterator_get_of_lookup propertyFuel _ _ _ descriptor returned
    (NodeCaptureGuard.descriptor_path_lookup _ _ _ _ _ _ full (by unfold propertyFuel at bound ⊢; omega)) pureRead

 theorem bind_three (extra : Nat) (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value)
    (inputs : Inputs before context pattern valuesHandle nextHandle values returned) :
    bindArrayElements (extra + 4) context program.elements (record before nextHandle)
      (acquired before context pattern valuesHandle nextHandle) =
      .ok (record before nextHandle, beforeClose before context pattern valuesHandle nextHandle values) := by
  obtain ⟨root, rootFound⟩ := inputs.resultPrototypeFound
  have three := inputs.three
  have rootBound := (List.getElem?_eq_some_iff.mp rootFound).1
  have separated := realm_separated before context valuesHandle nextHandle returned inputs.toRealm
  have identity := realm_next_identity before context valuesHandle nextHandle returned inputs.toRealm
  have root0 : (acquired before context pattern valuesHandle nextHandle).regexp.ambient.objects[context.resultPrototype]? = some root := by
    exact (List.getElem?_append_left rootBound).trans rootFound
  have cursor0 : (acquired before context pattern valuesHandle nextHandle).iterators.lookup before.regexp.ambient.objects.length =
      some ⟨some pattern, 0⟩ := by simp [acquired, arrayIteratorAcquiredState, allocateArrayIterator]
  have run0 := (step_yield context before.regexp.ambient.objects.length pattern 0 nextHandle values
    (acquired before context pattern valuesHandle nextHandle) root cursor0 inputs.found root0 (by omega) separated identity).1
  have root1 : (firstState before context pattern valuesHandle nextHandle values).regexp.ambient.objects[context.resultPrototype]? = some root := by
    exact (List.getElem?_append_left (by simp only [setArrayIteratorCursor, acquired, arrayIteratorAcquiredState, allocateArrayIterator, List.length_append, List.length_singleton]; omega)).trans root0
  have cursor1 : (firstState before context pattern valuesHandle nextHandle values).iterators.lookup before.regexp.ambient.objects.length =
      some ⟨some pattern, 1⟩ := by simp [firstState, stepState, iteratorYieldState, iteratorResultState, setArrayIteratorCursor]
  have run1 := (step_yield context before.regexp.ambient.objects.length pattern 1 nextHandle values
    (firstState before context pattern valuesHandle nextHandle values) root cursor1 inputs.found root1 (by omega) separated identity).2
  have root2 : (secondState before context pattern valuesHandle nextHandle values).regexp.ambient.objects[context.resultPrototype]? = some root := by
    exact (List.getElem?_append_left (by simp only [setArrayIteratorCursor, firstState, stepState, iteratorYieldState, iteratorResultState, acquired, arrayIteratorAcquiredState, allocateArrayIterator, List.length_append, List.length_singleton]; omega)).trans root1
  have cursor2 : (secondState before context pattern valuesHandle nextHandle values).iterators.lookup before.regexp.ambient.objects.length =
      some ⟨some pattern, 2⟩ := by simp [secondState, initialized, stepState, iteratorYieldState, iteratorResultState, setArrayIteratorCursor]
  have run2 := (step_yield context before.regexp.ambient.objects.length pattern 2 nextHandle values
    (secondState before context pattern valuesHandle nextHandle values) root cursor2 inputs.found root2 (by omega) separated identity).2
  change bindArrayElements (extra + 4) context [.elision, .binding "name", .binding "matcher"] ⟨_, .function nextHandle, false⟩ _ = _
  rw [bindArrayElements_elision _ _ _ _ _ _ _ _ run0]
  simp only [bindArrayElements, bind, Except.bind]
  change (do
    let (value, rec, after) ← iteratorStepValue context (record before nextHandle) (firstState before context pattern valuesHandle nextHandle values)
    let after := initialized after "name" value
    let (value, rec, after) ← iteratorStepValue context rec after
    pure (rec, initialized after "matcher" value)) = _
  change iteratorStepValue context (record before nextHandle) _ = _ at run1
  change iteratorStepValue context (record before nextHandle) _ = _ at run2
  rw [run1]
  dsimp only [bind, Except.bind]
  change (do
    let (value, rec, after) ← iteratorStepValue context (record before nextHandle) (secondState before context pattern valuesHandle nextHandle values)
    pure (rec, initialized after "matcher" value)) = _
  rw [run2]
  rfl

 theorem execute_source (extra : Nat) (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value)
    (inputs : Inputs before context pattern valuesHandle nextHandle values returned) :
    sourceBinding (extra + 4) context before =
      some (.ok (record before nextHandle, resultState before context pattern valuesHandle nextHandle values returned)) := by
  have initializerRead : evalExpression (extra + 4) defaultSplitLimit program.initializer before.regexp.ambient =
      .ok (.array pattern, before.regexp.ambient) := by
    simp [program, evalExpression, lookupVariable, inputs.binding]
    rfl
  rw [sourceBinding, parses_source]
  dsimp only [Option.map, runArrayBinding]
  rw [initializerRead]
  dsimp only [Except.mapError, bind, Except.bind]
  rw [acquire before context pattern valuesHandle nextHandle values returned inputs]
  dsimp only [bind, Except.bind]
  rw [bind_three extra before context pattern valuesHandle nextHandle values returned inputs]
  dsimp only [bind, Except.bind]
  rw [closeArrayIterator_nullish (record before nextHandle) _ returned rfl
    (close_read before context pattern valuesHandle nextHandle values returned inputs.toRealm) inputs.nullish]
  rfl


private theorem lookup_filter_other_cursor (entries : List (Nat × ArrayIteratorCursor)) (owner other : Nat) (different : other ≠ owner) :
    (entries.filter (fun entry => entry.1 != owner)).lookup other = entries.lookup other := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, cursor⟩ := entry
    by_cases removed : key = owner
    · subst key
      have unequal : (other == owner) = false := beq_eq_false_iff_ne.mpr different
      simp [List.lookup, unequal, ih]
    · have retained : (key == owner) = false := beq_eq_false_iff_ne.mpr removed
      simp only [bne] at ih
      simp [List.filter, bne, retained, List.lookup, ih]

theorem cursor_other (before : ArrayBindingState) (owner other : Nat) (cursor : ArrayIteratorCursor) (different : other ≠ owner) :
    (setArrayIteratorCursor owner cursor before).iterators.lookup other = before.iterators.lookup other := by
  simp [setArrayIteratorCursor, List.lookup, beq_eq_false_iff_ne.mpr different, lookup_filter_other_cursor _ owner other different]

theorem result_old_iterators (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value)
    (reference : Nat) (bound : reference < before.regexp.ambient.objects.length) :
    (resultState before context pattern valuesHandle nextHandle values returned).iterators.lookup reference = before.iterators.lookup reference := by
  have different : reference ≠ before.regexp.ambient.objects.length := by omega
  simp [resultState, beforeClose, initialized, secondState, firstState, stepState, iteratorYieldState,
    iteratorResultState, cursor_other, different, acquired, arrayIteratorAcquiredState, allocateArrayIterator, List.lookup,
    beq_eq_false_iff_ne.mpr different]

 theorem result_contract (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value) :
    Contract before (resultState before context pattern valuesHandle nextHandle values returned) context pattern nextHandle values (record before nextHandle) := by
  have objects := beforeClose_objects before context pattern valuesHandle nextHandle values
  refine ⟨rfl, rfl, rfl, ?_, objects, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simp [resultState, beforeClose, initialized, stepState, iteratorYieldState, iteratorResultState, setArrayIteratorCursor]
  · intro reference bound
    change (beforeClose before context pattern valuesHandle nextHandle values).regexp.ambient.objects[reference]? = _
    rw [objects]
    exact List.getElem?_append_left bound
  · exact result_old_iterators before context pattern valuesHandle nextHandle values returned

 theorem source_binding_satisfies (extra : Nat) (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value)
    (inputs : Inputs before context pattern valuesHandle nextHandle values returned) :
    sourceBinding (extra + 4) context before =
      some (.ok (record before nextHandle, resultState before context pattern valuesHandle nextHandle values returned)) ∧
    Contract before (resultState before context pattern valuesHandle nextHandle values returned) context pattern nextHandle values (record before nextHandle) :=
  ⟨execute_source extra before context pattern valuesHandle nextHandle values returned inputs,
   result_contract before context pattern valuesHandle nextHandle values returned⟩

theorem result_protocol_trace (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value) :
    (resultState before context pattern valuesHandle nextHandle values returned).trace =
      before.trace ++ protocolEvents before pattern valuesHandle nextHandle values returned := by
  simp [resultState, beforeClose, initialized, secondState, firstState, stepState, iteratorYieldState,
    iteratorResultState, setArrayIteratorCursor, acquired, arrayIteratorAcquiredState, allocateArrayIterator,
    protocolEvents, List.append_assoc]

theorem source_binding_protocol_satisfies (extra : Nat) (before : ArrayBindingState) (context : ArrayIteratorContext)
    (pattern valuesHandle nextHandle : Nat) (values : List Value) (returned : Value)
    (inputs : Inputs before context pattern valuesHandle nextHandle values returned) :
    sourceBinding (extra + 4) context before =
      some (.ok (record before nextHandle, resultState before context pattern valuesHandle nextHandle values returned)) ∧
    Contract before (resultState before context pattern valuesHandle nextHandle values returned) context pattern nextHandle values (record before nextHandle) ∧
    (resultState before context pattern valuesHandle nextHandle values returned).trace =
      before.trace ++ protocolEvents before pattern valuesHandle nextHandle values returned :=
  ⟨execute_source extra before context pattern valuesHandle nextHandle values returned inputs,
   result_contract before context pattern valuesHandle nextHandle values returned,
   result_protocol_trace before context pattern valuesHandle nextHandle values returned⟩


end HonoLean.Upstream.NodePatternBinding
