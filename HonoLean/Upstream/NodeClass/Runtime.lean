import HonoLean.Upstream.NodeClass.Program
import HonoLean.Upstream.NodeInitialization.Correctness
import HonoLean.Upstream.SourceSubset.PrivateClass

namespace HonoLean.Upstream.NodeClass

open SourceSubset ECMA2025

def names (firstIdentity : Nat) : List (String × Nat) :=
  NodeInitialization.nodeNames firstIdentity ++ [("pushHandlerSets", firstIdentity + 5)]

def definition (environment : List (String × Value)) (firstIdentity firstHandle : Nat) : SelectedPrivateClass :=
  ⟨fieldsProgram, methodsProgram, firstIdentity, environment, firstHandle⟩

def closure (environment : List (String × Value)) (firstIdentity : Nat) : PrivateMethodClosure :=
  ⟨NodePrivateCall.methodProgram, environment, names firstIdentity⟩

theorem definition_names (environment : List (String × Value)) (firstIdentity firstHandle : Nat) :
    (definition environment firstIdentity firstHandle).names = names firstIdentity := by
  simp [definition, SelectedPrivateClass.names, SelectedPrivateClass.spellings, fieldsProgram,
    methodsProgram, NodeInitialization.fieldsProgram, NodeInitialization.nodeNames, names,
    NodePrivateCall.methodProgram]

theorem definition_methods (environment : List (String × Value)) (firstIdentity firstHandle : Nat) :
    (definition environment firstIdentity firstHandle).methodBindings =
      [(firstIdentity + 5, .function firstHandle)] := by
  simp [definition, SelectedPrivateClass.methodBindings, fieldsProgram, methodsProgram,
    NodeInitialization.fieldsProgram]

theorem definition_closures (environment : List (String × Value)) (firstIdentity firstHandle : Nat) :
    (definition environment firstIdentity firstHandle).closures = [closure environment firstIdentity] := by
  change ([⟨NodePrivateCall.methodProgram, environment, (definition environment firstIdentity firstHandle).names⟩] : List PrivateMethodClosure) = _
  rw [definition_names]
  rfl

theorem define_node (before : State) (world : PrivateWorld) (table : PrivateMethodTable)
    (separate : before.functions.length ≤ table.base) :
    definePrivateClass fieldsProgram methodsProgram before world table =
      some (definition before.environment world.nextIdentity (table.base + table.entries.length),
        ⟨world.nextIdentity + 6⟩,
        {table with entries := table.entries ++ [closure before.environment world.nextIdentity]}) := by
  simp [definePrivateClass, SelectedPrivateClass.spellings, definition, fieldsProgram, methodsProgram,
    NodeInitialization.fieldsProgram, NodePrivateCall.methodProgram, separate,
    SelectedPrivateClass.closures, SelectedPrivateClass.names, names, NodeInitialization.nodeNames,
    closure]

def storedFields (before : State) (firstIdentity firstHandle : Nat) (emptyParams : Value) : List (Nat × Value) :=
  NodeInitialization.storedFields before firstIdentity emptyParams ++ [(firstIdentity + 5, .function firstHandle)]

def storedElements (before : State) (firstIdentity firstHandle : Nat) (emptyParams : Value) : List (Nat × PrivateElement) :=
  dataElements (NodeInitialization.storedFields before firstIdentity emptyParams) ++
    [(firstIdentity + 5, .method (.function firstHandle))]

def methodsInstalledState (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity firstHandle : Nat) : State :=
  {before with
    environment
    thisValue := .object before.objects.length
    objects := before.objects ++ [⟨[], prototype, true⟩]
    privates := ⟨names firstIdentity,
      (before.objects.length, [(firstIdentity + 5, .method (.function firstHandle))]) :: before.privates.elements⟩}

def rawFieldsState (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity firstHandle : Nat) (emptyParams : Value) : State :=
  {before with
    environment
    thisValue := .object before.objects.length
    objects := before.objects ++ [⟨[], prototype, true⟩, emptyNullObject]
    heap := before.heap ++ [[], []]
    privates := ⟨names firstIdentity,
      (before.objects.length, storedElements before firstIdentity firstHandle emptyParams) :: before.privates.elements⟩}

def instanceState (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity firstHandle : Nat) (emptyParams : Value) : State :=
  restoreDataCaller before (rawFieldsState before prototype environment firstIdentity firstHandle emptyParams)

theorem install_node_method (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity firstHandle : Nat)
    (fresh : before.privates.slots.lookup before.objects.length = none) :
    installPrivateMethodBindings (definition environment firstIdentity firstHandle).methodBindings before.objects.length
      (initialPrivateClassState (definition environment firstIdentity firstHandle) prototype before) =
      .ok (methodsInstalledState before prototype environment firstIdentity firstHandle) := by
  have rawFresh := (PrivateStore.slots_lookup_none_iff _ _).mp fresh
  have filtered := NodeInitialization.filter_slots_absent before.privates.elements before.objects.length rawFresh
  rw [definition_methods, install_single_method]
  simp only [initialPrivateClassState, definition_names]
  simp [privateMethodAdd, privateElementAdd, initialInstanceState, SelectedPrivateClass.dataDefinition,
    definition, addedPrivateElementState, methodsInstalledState, filtered]

theorem initialize_node_fields (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity firstHandle : Nat) (emptyParams : Value)
    (fresh : before.privates.slots.lookup before.objects.length = none)
    (bindings : NodeInitialization.InitializerBindings before environment emptyParams) :
    initializeFields 64 defaultSplitLimit fieldsProgram before.objects.length
      (methodsInstalledState before prototype environment firstIdentity firstHandle) =
      .ok (rawFieldsState before prototype environment firstIdentity firstHandle emptyParams) := by
  obtain ⟨⟨reference, helperEnvironment, binding, found, standard⟩, shared⟩ := bindings
  have rawFresh := (PrivateStore.slots_lookup_none_iff _ _).mp fresh
  have filtered := NodeInitialization.filter_slots_absent before.privates.elements before.objects.length rawFresh
  have d10 : (firstIdentity + 1 == firstIdentity) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d20 : (firstIdentity + 2 == firstIdentity) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d21 : (firstIdentity + 2 == firstIdentity + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d30 : (firstIdentity + 3 == firstIdentity) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d31 : (firstIdentity + 3 == firstIdentity + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d32 : (firstIdentity + 3 == firstIdentity + 2) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d40 : (firstIdentity + 4 == firstIdentity) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d41 : (firstIdentity + 4 == firstIdentity + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d42 : (firstIdentity + 4 == firstIdentity + 2) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d43 : (firstIdentity + 4 == firstIdentity + 3) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d05 : (firstIdentity == firstIdentity + 5) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d15 : (firstIdentity + 1 == firstIdentity + 5) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d25 : (firstIdentity + 2 == firstIdentity + 5) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d35 : (firstIdentity + 3 == firstIdentity + 5) = false := beq_eq_false_iff_ne.mpr (by omega)
  have d45 : (firstIdentity + 4 == firstIdentity + 5) = false := beq_eq_false_iff_ne.mpr (by omega)
  rcases standard with ambient | ambient <;>
    simp [initializeFields, initializeField, fieldsProgram, NodeInitialization.fieldsProgram,
      methodsInstalledState, evalExpression, evalLiteralElements, evalArguments, lookupVariable,
      binding, found, CreateNullObject.createProgram, ambient, intrinsic, createNull,
      privateAdd, privateElementAdd, addedPrivateElementState, dataElements, filtered, shared, rawFieldsState, storedElements,
      NodeInitialization.storedFields, names, NodeInitialization.nodeNames,
      List.lookup, List.append_assoc, d10, d20, d21, d30, d31, d32, d40, d41, d42, d43,
      d05, d15, d25, d35, d45, bind, pure, Except.bind, Except.pure]

theorem instantiate_node (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity firstHandle : Nat) (emptyParams : Value)
    (fresh : before.privates.slots.lookup before.objects.length = none)
    (prototypeReady : NodeInitialization.PrototypeReady before prototype)
    (bindings : NodeInitialization.InitializerBindings before environment emptyParams) :
    instantiatePrivateClass 64 defaultSplitLimit (definition environment firstIdentity firstHandle) prototype before =
      .ok (before.objects.length, instanceState before prototype environment firstIdentity firstHandle emptyParams) := by
  have started : beginPrivateClassInstance (definition environment firstIdentity firstHandle) prototype before =
      .ok (before.objects.length, initialPrivateClassState (definition environment firstIdentity firstHandle) prototype before) := by
    cases prototype with
    | none => exact beginPrivateClass_none _ _ fresh
    | some reference =>
      obtain ⟨object, found⟩ := prototypeReady
      exact beginPrivateClass_some _ _ _ object fresh found
  simp only [instantiatePrivateClass]
  rw [started]
  simp only [bind, Except.bind]
  rw [install_node_method before prototype environment firstIdentity firstHandle fresh]
  change (do
    let state ← initializeFields 64 defaultSplitLimit fieldsProgram before.objects.length
      (methodsInstalledState before prototype environment firstIdentity firstHandle)
    pure (before.objects.length, restoreDataCaller before state)) = _
  rw [initialize_node_fields before prototype environment firstIdentity firstHandle emptyParams fresh bindings]
  rfl

end HonoLean.Upstream.NodeClass
