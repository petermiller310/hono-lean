import HonoLean.Upstream.SourceSubset.PrivateInitialization
import HonoLean.Upstream.SourceSubset.PrivateCall

namespace HonoLean.Upstream.SourceSubset

/-- Identities represented either by current private storage/scope or by a
retained method closure. A definition with no instances can still reserve
names through its closure table entry. Unrepresented external definitions and
zero-method definitions still require the persistent world protocol. -/
def storedPrivateClassIdentities (before : State) (table : PrivateMethodTable) : List Nat :=
  storedPrivateIdentities before ++
    table.entries.flatMap (fun closure => closure.privateNames.map Prod.snd)

def initialPrivateClassWorld (before : State) (table : PrivateMethodTable) : PrivateWorld :=
  ⟨(storedPrivateClassIdentities before table).foldl Nat.max 0 + 1⟩

private theorem classFoldMax_initial (initial : Nat) (values : List Nat) :
    initial ≤ values.foldl Nat.max initial := by
  induction values generalizing initial with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact Nat.le_trans (Nat.le_max_left initial head) (ih _)

private theorem classFoldMax_member (initial : Nat) (values : List Nat) (value : Nat)
    (member : value ∈ values) : value ≤ values.foldl Nat.max initial := by
  induction values generalizing initial with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (Nat.le_max_right initial value) (classFoldMax_initial _ _)
    · exact ih _ member

theorem initialPrivateClassWorld_fresh (before : State) (table : PrivateMethodTable) (identity : Nat)
    (used : identity ∈ storedPrivateClassIdentities before table) :
    identity < (initialPrivateClassWorld before table).nextIdentity := by
  have bound := classFoldMax_member 0 (storedPrivateClassIdentities before table) identity used
  simp only [initialPrivateClassWorld]
  omega

theorem initialPrivateClassWorld_state_fresh (before : State) (table : PrivateMethodTable) (identity : Nat)
    (used : identity ∈ storedPrivateIdentities before) :
    identity < (initialPrivateClassWorld before table).nextIdentity :=
  initialPrivateClassWorld_fresh before table identity (List.mem_append_left _ used)

theorem initialPrivateClassWorld_closure_fresh (before : State) (table : PrivateMethodTable)
    (closure : PrivateMethodClosure) (name : String) (identity : Nat)
    (stored : closure ∈ table.entries) (used : (name, identity) ∈ closure.privateNames) :
    identity < (initialPrivateClassWorld before table).nextIdentity := by
  apply initialPrivateClassWorld_fresh
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨closure, stored, List.mem_map.mpr ⟨(name, identity), used, rfl⟩⟩

/-- A selected class-private element plan: these data declarations occur before
these method declarations in private-name source order. Public members, class
evaluation, constructors, home objects and native function objects are not
represented by this plan. Captures are frozen values in the admitted subset. -/
structure SelectedPrivateClass where
  fields : List PrivateField
  methods : List PrivateMethod
  firstIdentity : Nat
  environment : List (String × Value)
  firstHandle : Nat
  deriving Repr

def SelectedPrivateClass.spellings (definition : SelectedPrivateClass) : List String :=
  definition.fields.map PrivateField.name ++ definition.methods.map PrivateMethod.name

def SelectedPrivateClass.names (definition : SelectedPrivateClass) : List (String × Nat) :=
  definition.spellings.zipIdx.map (fun (name, index) => (name, definition.firstIdentity + index))

def SelectedPrivateClass.dataDefinition (definition : SelectedPrivateClass) : DataClass :=
  ⟨definition.fields, definition.firstIdentity, definition.environment⟩

def SelectedPrivateClass.closures (definition : SelectedPrivateClass) : List PrivateMethodClosure :=
  definition.methods.map (fun method => ⟨method, definition.environment, definition.names⟩)

/-- Method read handles share one identity per definition across all instances.
The raw private element carries a METHOD tag. Ordinary assignment uses that
tag to reject method writes; the Value observation does not erase it in storage. -/
def SelectedPrivateClass.methodBindings (definition : SelectedPrivateClass) : List (Nat × Value) :=
  definition.methods.zipIdx.map (fun (_, index) =>
    (definition.firstIdentity + definition.fields.length + index,
      .function (definition.firstHandle + index)))

/-- Thread BOTH the returned identity world and method table across definitions,
including definitions with no instances. Reconstructing a world/table from a
later active instance loses reservations. Existing expression-function IDs are
separated from the method table at definition and call-entry boundaries. -/
def definePrivateClass (fields : List PrivateField) (methods : List PrivateMethod)
    (before : State) (world : PrivateWorld) (table : PrivateMethodTable) :
    Option (SelectedPrivateClass × PrivateWorld × PrivateMethodTable) :=
  let definition : SelectedPrivateClass :=
    ⟨fields, methods, world.nextIdentity, before.environment, table.base + table.entries.length⟩
  if decide definition.spellings.Nodup &&
      definition.spellings.all (fun name => name != "constructor") &&
      decide (before.functions.length ≤ table.base) then
    some (definition, ⟨world.nextIdentity + definition.spellings.length⟩,
      {table with entries := table.entries ++ definition.closures})
  else none

def initialPrivateClassState (definition : SelectedPrivateClass) (prototype : Option Nat)
    (before : State) : State :=
  let state := initialInstanceState definition.dataDefinition prototype before
  {state with privates := {state.privates with names := definition.names}}

/-- Allocation keeps the old ghost-slot/prototype checks, then enters the full
selected private-name scope. No method or field is installed at this step. -/
def beginPrivateClassInstance (definition : SelectedPrivateClass) (prototype : Option Nat)
    (before : State) : Except EvalError (Nat × State) := do
  let (owner, state) ← beginInstance definition.dataDefinition prototype before
  pure (owner, {state with privates := {state.privates with names := definition.names}})

def installPrivateMethodBindings : List (Nat × Value) → Nat → State → Except EvalError State
  | [], _, before => .ok before
  | (identity, value) :: rest, owner, before => do
    let next ← privateMethodAdd before owner identity value
    installPrivateMethodBindings rest owner next

/-- Install selected private method read handles BEFORE executing ordered data
initializers. The existing privateAdd rejects duplicates and bypasses ordinary
setters/extensibility. Partial exception-state traces, constructor/newTarget
lookup, arbitrary private field/method kinds and full native class semantics
remain separate obligations. -/
def instantiatePrivateClass (fuel limit : Nat) (definition : SelectedPrivateClass)
    (prototype : Option Nat) (before : State) : Except EvalError (Nat × State) := do
  let (owner, state) ← beginPrivateClassInstance definition prototype before
  let state ← installPrivateMethodBindings definition.methodBindings owner state
  let state ← initializeFields fuel limit definition.fields owner state
  pure (owner, restoreDataCaller before state)

theorem class_spellings_length (definition : SelectedPrivateClass) :
    definition.spellings.length = definition.fields.length + definition.methods.length := by
  simp [SelectedPrivateClass.spellings]

theorem class_closures_length (definition : SelectedPrivateClass) :
    definition.closures.length = definition.methods.length := by
  simp [SelectedPrivateClass.closures]

theorem class_names_length (definition : SelectedPrivateClass) :
    definition.names.length = definition.spellings.length := by
  simp [SelectedPrivateClass.names]

theorem definePrivateClass_reserves (fields : List PrivateField) (methods : List PrivateMethod)
    (before : State) (world : PrivateWorld) (table : PrivateMethodTable)
    (definition : SelectedPrivateClass) (next : PrivateWorld) (nextTable : PrivateMethodTable)
    (defined : definePrivateClass fields methods before world table = some (definition, next, nextTable)) :
    definition.fields = fields ∧ definition.methods = methods ∧
      definition.firstIdentity = world.nextIdentity ∧ definition.environment = before.environment ∧
      definition.firstHandle = table.base + table.entries.length ∧
      next.nextIdentity = world.nextIdentity + definition.spellings.length ∧
      nextTable.base = table.base ∧ nextTable.entries = table.entries ++ definition.closures ∧
      before.functions.length ≤ table.base := by
  simp only [definePrivateClass] at defined
  split at defined
  · rename_i condition
    cases defined
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true (Bool.and_eq_true_iff.mp condition).2⟩
  · contradiction

theorem class_name_range (definition : SelectedPrivateClass) (name : String) (identity : Nat)
    (member : (name, identity) ∈ definition.names) :
    definition.firstIdentity ≤ identity ∧
      identity < definition.firstIdentity + definition.spellings.length := by
  simp only [SelectedPrivateClass.names, List.mem_map] at member
  obtain ⟨⟨spelling, index⟩, member, equal⟩ := member
  have inside := (List.mem_zipIdx' member).1
  cases equal
  omega

theorem successive_private_classes_disjoint (fieldsA fieldsB : List PrivateField)
    (methodsA methodsB : List PrivateMethod) (beforeA beforeB : State)
    (world next final : PrivateWorld) (table nextTable finalTable : PrivateMethodTable)
    (first second : SelectedPrivateClass)
    (definedA : definePrivateClass fieldsA methodsA beforeA world table = some (first, next, nextTable))
    (definedB : definePrivateClass fieldsB methodsB beforeB next nextTable = some (second, final, finalTable))
    (nameA nameB : String) (identityA identityB : Nat)
    (memberA : (nameA, identityA) ∈ first.names) (memberB : (nameB, identityB) ∈ second.names) :
    identityA ≠ identityB := by
  have firstFacts := definePrivateClass_reserves _ _ _ _ _ _ _ _ definedA
  have secondFacts := definePrivateClass_reserves _ _ _ _ _ _ _ _ definedB
  have firstRange := class_name_range first nameA identityA memberA
  have secondRange := class_name_range second nameB identityB memberB
  rw [firstFacts.2.2.1] at firstRange
  rw [secondFacts.2.2.1] at secondRange
  have advance := firstFacts.2.2.2.2.2.1
  omega

theorem defined_table_old (fields : List PrivateField) (methods : List PrivateMethod)
    (before : State) (world : PrivateWorld) (table : PrivateMethodTable)
    (definition : SelectedPrivateClass) (next : PrivateWorld) (nextTable : PrivateMethodTable)
    (defined : definePrivateClass fields methods before world table = some (definition, next, nextTable))
    (index : Nat) (inside : index < table.entries.length) :
    nextTable.entries[index]? = table.entries[index]? := by
  have facts := definePrivateClass_reserves _ _ _ _ _ _ _ _ defined
  rw [facts.2.2.2.2.2.2.2.1]
  exact List.getElem?_append_left inside

theorem defined_table_method (fields : List PrivateField) (methods : List PrivateMethod)
    (before : State) (world : PrivateWorld) (table : PrivateMethodTable)
    (definition : SelectedPrivateClass) (next : PrivateWorld) (nextTable : PrivateMethodTable)
    (defined : definePrivateClass fields methods before world table = some (definition, next, nextTable))
    (index : Nat) (method : PrivateMethod) (found : methods[index]? = some method) :
    nextTable.entries[table.entries.length + index]? =
      some ⟨method, before.environment, definition.names⟩ := by
  have facts := definePrivateClass_reserves _ _ _ _ _ _ _ _ defined
  rw [facts.2.2.2.2.2.2.2.1]
  rw [List.getElem?_append_right (l₁ := table.entries) (l₂ := definition.closures)
    (i := table.entries.length + index) (by omega)]
  simp [SelectedPrivateClass.closures, facts.2.1, facts.2.2.2.1, found]

theorem defined_handle_separate (fields : List PrivateField) (methods : List PrivateMethod)
    (before : State) (world : PrivateWorld) (table : PrivateMethodTable)
    (definition : SelectedPrivateClass) (next : PrivateWorld) (nextTable : PrivateMethodTable)
    (defined : definePrivateClass fields methods before world table = some (definition, next, nextTable))
    (index old : Nat) (oldFunction : old < before.functions.length) :
    old ≠ definition.firstHandle + index := by
  have facts := definePrivateClass_reserves _ _ _ _ _ _ _ _ defined
  have partition := facts.2.2.2.2.2.2.2.2
  have handle := facts.2.2.2.2.1
  omega

theorem successive_method_handles_disjoint (fieldsA fieldsB : List PrivateField)
    (methodsA methodsB : List PrivateMethod) (beforeA beforeB : State)
    (world next final : PrivateWorld) (table nextTable finalTable : PrivateMethodTable)
    (first second : SelectedPrivateClass)
    (definedA : definePrivateClass fieldsA methodsA beforeA world table = some (first, next, nextTable))
    (definedB : definePrivateClass fieldsB methodsB beforeB next nextTable = some (second, final, finalTable))
    (indexA indexB : Nat) (inside : indexA < first.methods.length) :
    first.firstHandle + indexA ≠ second.firstHandle + indexB := by
  have firstFacts := definePrivateClass_reserves _ _ _ _ _ _ _ _ definedA
  have secondFacts := definePrivateClass_reserves _ _ _ _ _ _ _ _ definedB
  have base := firstFacts.2.2.2.2.2.2.1
  have entries := firstFacts.2.2.2.2.2.2.2.1
  have count : nextTable.entries.length = table.entries.length + first.methods.length := by
    rw [entries, List.length_append, class_closures_length]
  rw [firstFacts.2.2.2.2.1, secondFacts.2.2.2.2.1, base, count]
  omega

theorem beginPrivateClass_none (definition : SelectedPrivateClass) (before : State)
    (fresh : before.privates.slots.lookup before.objects.length = none) :
    beginPrivateClassInstance definition none before =
      .ok (before.objects.length, initialPrivateClassState definition none before) := by
  simp [beginPrivateClassInstance, beginInstance_none _ _ fresh, initialPrivateClassState,
    bind, pure, Except.bind, Except.pure]

theorem beginPrivateClass_some (definition : SelectedPrivateClass) (before : State)
    (prototype : Nat) (object : ECMA2025.OrdinaryObject)
    (fresh : before.privates.slots.lookup before.objects.length = none)
    (found : before.objects[prototype]? = some object) :
    beginPrivateClassInstance definition (some prototype) before =
      .ok (before.objects.length, initialPrivateClassState definition (some prototype) before) := by
  simp [beginPrivateClassInstance, beginInstance_some _ _ _ object fresh found, initialPrivateClassState,
    bind, pure, Except.bind, Except.pure]

theorem install_single_method (owner identity : Nat) (value : Value) (before : State) :
    installPrivateMethodBindings [(identity, value)] owner before = privateMethodAdd before owner identity value := by
  unfold installPrivateMethodBindings
  cases privateMethodAdd before owner identity value <;> rfl

theorem install_single_method_normal (owner identity : Nat) (value : Value) (before : State)
    (object : ECMA2025.OrdinaryObject) (prior : List (Nat × PrivateElement))
    (found : before.objects[owner]? = some object)
    (fields : before.privates.elements.lookup owner = some prior) (absent : prior.lookup identity = none) :
    installPrivateMethodBindings [(identity, value)] owner before =
      .ok (addedPrivateElementState before owner identity (.method value) prior) := by
  rw [install_single_method]
  simp [privateMethodAdd, privateElementAdd, found, fields, absent]

private theorem lookup_filter_other_owner {α : Type} (slots : List (Nat × α))
    (owner other : Nat) (different : other ≠ owner) :
    (slots.filter (fun entry => entry.1 != owner)).lookup other = slots.lookup other := by
  induction slots with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, fields⟩ := entry
    by_cases removed : key = owner
    · subst key
      have unequal : (other == owner) = false := beq_eq_false_iff_ne.mpr different
      simp [List.lookup, unequal, ih]
    · have retained : (key == owner) = false := beq_eq_false_iff_ne.mpr removed
      simp only [bne] at ih
      simp [List.filter, bne, retained, List.lookup, ih]

/-- Installing tagged method elements frames every other raw private owner as
well as ordinary/public state. The Value projection follows from those tags. -/
structure MethodInstallFrame (before after : State) (owner : Nat) : Prop where
  environment : after.environment = before.environment
  thisValue : after.thisValue = before.thisValue
  names : after.privates.names = before.privates.names
  objects : after.objects = before.objects
  arrays : after.heap = before.heap
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  otherElements : ∀ other, other ≠ owner → after.privates.elements.lookup other = before.privates.elements.lookup other
  otherOwners : ∀ other, other ≠ owner → after.privates.slots.lookup other = before.privates.slots.lookup other

theorem privateElementAdd_frame (before after : State) (owner identity : Nat) (element : PrivateElement)
    (added : privateElementAdd before owner identity element = .ok after) :
    MethodInstallFrame before after owner := by
  unfold privateElementAdd at added
  split at added
  · contradiction
  · dsimp only at added
    split at added
    · contradiction
    · cases added
      have raw : ∀ other, other ≠ owner →
          (addedPrivateElementState before owner identity element
            ((before.privates.elements.lookup owner).getD [])).privates.elements.lookup other =
              before.privates.elements.lookup other := by
        intro other different
        have unequal : (other == owner) = false := beq_eq_false_iff_ne.mpr different
        simp [addedPrivateElementState, List.lookup, unequal,
          lookup_filter_other_owner _ owner other different]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, raw, ?_⟩
      intro other different
      rw [PrivateStore.slots_lookup, PrivateStore.slots_lookup, raw other different]

theorem privateAdd_frame (before after : State) (owner identity : Nat) (value : Value)
    (added : privateAdd before owner identity value = .ok after) : MethodInstallFrame before after owner :=
  privateElementAdd_frame before after owner identity (.data value) added

theorem privateMethodAdd_frame (before after : State) (owner identity : Nat) (value : Value)
    (added : privateMethodAdd before owner identity value = .ok after) : MethodInstallFrame before after owner :=
  privateElementAdd_frame before after owner identity (.method value) added

theorem install_private_methods_frame (bindings : List (Nat × Value)) (owner : Nat)
    (before after : State)
    (installed : installPrivateMethodBindings bindings owner before = .ok after) :
    MethodInstallFrame before after owner := by
  induction bindings generalizing before with
  | nil =>
    simp only [installPrivateMethodBindings, Except.ok.injEq] at installed
    cases installed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons binding rest ih =>
    obtain ⟨identity, value⟩ := binding
    cases first : privateMethodAdd before owner identity value with
    | error error => simp [installPrivateMethodBindings, first, bind, Except.bind] at installed
    | ok middle =>
      simp only [installPrivateMethodBindings, first, bind, Except.bind] at installed
      have one := privateMethodAdd_frame before middle owner identity value first
      have later := ih middle installed
      exact ⟨later.environment.trans one.environment, later.thisValue.trans one.thisValue,
        later.names.trans one.names, later.objects.trans one.objects, later.arrays.trans one.arrays,
        later.functions.trans one.functions, later.sets.trans one.sets,
        fun other different => (later.otherElements other different).trans (one.otherElements other different),
        fun other different => (later.otherOwners other different).trans (one.otherOwners other different)⟩

end HonoLean.Upstream.SourceSubset
