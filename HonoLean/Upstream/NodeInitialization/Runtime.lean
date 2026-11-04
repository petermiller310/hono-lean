import HonoLean.Upstream.NodeInitialization.Contract
import HonoLean.Upstream.SourceSubset.PrivateInitialization

namespace HonoLean.Upstream.NodeInitialization

open SourceSubset ECMA2025

def definition (environment : List (String × Value)) (firstIdentity : Nat) : DataClass :=
  ⟨fieldsProgram, firstIdentity, environment⟩

theorem definition_names (environment : List (String × Value)) (firstIdentity : Nat) :
    (definition environment firstIdentity).names = nodeNames firstIdentity := by
  simp [definition, DataClass.names, fieldsProgram, nodeNames]

theorem define_node (before : State) (world : PrivateWorld) :
    defineDataClass fieldsProgram before world =
      some (definition before.environment world.nextIdentity, ⟨world.nextIdentity + 5⟩) := by
  simp [defineDataClass, fieldsProgram, definition]

theorem parsed_define_node (before : State) (world : PrivateWorld) :
    (parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"]).bind
      (fun fields => defineDataClass fields before world) =
        some (definition before.environment world.nextIdentity, ⟨world.nextIdentity + 5⟩) := by
  rw [parses_fields, Option.bind_some, define_node]

def storedFields (before : State) (firstIdentity : Nat) (emptyParams : Value) : List (Nat × Value) :=
  [(firstIdentity + 4, emptyParams), (firstIdentity + 3, .undefined),
   (firstIdentity + 2, .array (before.heap.length + 1)),
   (firstIdentity + 1, .object (before.objects.length + 1)),
   (firstIdentity, .array before.heap.length)]

def rawFieldsState (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity : Nat) (emptyParams : Value) : State :=
  {before with
    environment
    thisValue := .object before.objects.length
    objects := before.objects ++ [⟨[], prototype, true⟩, emptyNullObject]
    heap := before.heap ++ [[], []]
    privates := ⟨nodeNames firstIdentity,
      (before.objects.length, dataElements (storedFields before firstIdentity emptyParams)) :: before.privates.elements⟩}

def instanceState (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity : Nat) (emptyParams : Value) : State :=
  restoreDataCaller before (rawFieldsState before prototype environment firstIdentity emptyParams)

def PrototypeReady (before : State) : Option Nat → Prop
  | none => True
  | some reference => ∃ object, before.objects[reference]? = some object

def InitializerBindings (before : State) (environment : List (String × Value)) (emptyParams : Value) : Prop :=
  HelperBinding {before with environment} ∧ environment.lookup "emptyParams" = some emptyParams

theorem filter_slots_absent {α : Type} (slots : List (Nat × α)) (owner : Nat)
    (absent : slots.lookup owner = none) :
    slots.filter (fun entry => entry.1 != owner) = slots := by
  induction slots with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, fields⟩ := entry
    by_cases equal : owner = key
    · subst key
      simp at absent
    · have different : (owner == key) = false := beq_eq_false_iff_ne.mpr equal
      have restAbsent : rest.lookup owner = none := by
        simpa only [List.lookup, different] using absent
      simpa [equal, Ne.symm equal] using congrArg (List.cons (key, fields)) (ih restAbsent)

theorem initialize_node_fields (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity : Nat) (emptyParams : Value)
    (fresh : before.privates.slots.lookup before.objects.length = none)
    (bindings : InitializerBindings before environment emptyParams) :
    initializeFields 64 defaultSplitLimit fieldsProgram before.objects.length
      (initialInstanceState (definition environment firstIdentity) prototype before) =
      .ok (rawFieldsState before prototype environment firstIdentity emptyParams) := by
  obtain ⟨⟨reference, helperEnvironment, binding, found, standard⟩, shared⟩ := bindings
  have rawFresh := (PrivateStore.slots_lookup_none_iff _ _).mp fresh
  have filtered := filter_slots_absent before.privates.elements before.objects.length rawFresh
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
  rcases standard with ambient | ambient <;>
    simp [initializeFields, initializeField, fieldsProgram, initialInstanceState, definition,
      DataClass.names, evalExpression, evalLiteralElements, evalArguments, lookupVariable,
      binding, found, CreateNullObject.createProgram, ambient, intrinsic, createNull,
      privateAdd, privateElementAdd, addedPrivateElementState, dataElements, filtered, shared, rawFieldsState, storedFields, nodeNames,
      List.lookup, List.append_assoc, d10, d20, d21, d30, d31, d32, d40, d41, d42, d43,
      bind, pure, Except.bind, Except.pure]

theorem instantiate_node (before : State) (prototype : Option Nat)
    (environment : List (String × Value)) (firstIdentity : Nat) (emptyParams : Value)
    (fresh : before.privates.slots.lookup before.objects.length = none)
    (prototypeReady : PrototypeReady before prototype)
    (bindings : InitializerBindings before environment emptyParams) :
    instantiateDataClass 64 defaultSplitLimit (definition environment firstIdentity) prototype before =
      .ok (before.objects.length, instanceState before prototype environment firstIdentity emptyParams) := by
  have started : beginInstance (definition environment firstIdentity) prototype before =
      .ok (before.objects.length, initialInstanceState (definition environment firstIdentity) prototype before) := by
    cases prototype with
    | none => exact beginInstance_none _ _ fresh
    | some reference =>
      obtain ⟨object, found⟩ := prototypeReady
      exact beginInstance_some _ _ _ object fresh found
  simp only [instantiateDataClass]
  rw [started]
  simp only [bind, Except.bind]
  change (do
    let state ← initializeFields 64 defaultSplitLimit fieldsProgram before.objects.length
      (initialInstanceState (definition environment firstIdentity) prototype before)
    pure (before.objects.length, restoreDataCaller before state)) = _
  rw [initialize_node_fields before prototype environment firstIdentity emptyParams fresh bindings]
  rfl

end HonoLean.Upstream.NodeInitialization
