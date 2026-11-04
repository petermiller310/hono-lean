import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset

/-- Persistent reservation cursor for private DATA identities. Thread the
returned world across definitions, including definitions with no instances.
Reconstructing a world from a later active scope would lose reservations.
Private method/accessor definitions and full native class evaluation are open. -/
structure PrivateWorld where
  nextIdentity : Nat
  deriving Repr, DecidableEq

def storedPrivateIdentities (state : State) : List Nat :=
  state.privates.names.map Prod.snd ++ state.privates.slots.flatMap (fun entry => entry.2.map Prod.fst)

def initialPrivateWorld (state : State) : PrivateWorld :=
  ⟨(storedPrivateIdentities state).foldl Nat.max 0 + 1⟩

/-- One supported field-list definition and its frozen value environment.
Its names are derived from the declarations and reservation base, rather than
supplied desired private slots. This does not install class methods/closures. -/
structure DataClass where
  fields : List PrivateField
  baseIdentity : Nat
  environment : List (String × Value)
  deriving Repr

def DataClass.names (definition : DataClass) : List (String × Nat) :=
  definition.fields.zipIdx.map (fun (field, index) => (field.name, definition.baseIdentity + index))

def defineDataClass (fields : List PrivateField) (before : State) (world : PrivateWorld) :
    Option (DataClass × PrivateWorld) :=
  if decide (fields.map PrivateField.name).Nodup && fields.all (fun field => field.name != "constructor") then
    some (⟨fields, world.nextIdentity, before.environment⟩, ⟨world.nextIdentity + fields.length⟩)
  else none

/-- Own-private-field addition bypasses ordinary properties, setters and
extensibility. Duplicate identities reject. The coarse error tag is not a
native exception object or a partial-state exception trace. -/
def addedPrivateElementState (state : State) (owner identity : Nat) (element : PrivateElement)
    (prior : List (Nat × PrivateElement)) : State :=
  {state with privates := {state.privates with elements :=
    (owner, (identity, element) :: prior) :: state.privates.elements.filter (fun entry => entry.1 != owner)}}

def addedPrivateState (state : State) (owner identity : Nat) (value : Value)
    (prior : List (Nat × PrivateElement)) : State :=
  addedPrivateElementState state owner identity (.data value) prior

def privateElementAdd (state : State) (owner identity : Nat) (element : PrivateElement) : Except EvalError State := do
  match state.objects[owner]? with
  | none => .error .invalidReference
  | some _ =>
    let prior := (state.privates.elements.lookup owner).getD []
    if (prior.lookup identity).isSome then .error .privateBrand
    else .ok (addedPrivateElementState state owner identity element prior)

def privateAdd (state : State) (owner identity : Nat) (value : Value) : Except EvalError State :=
  privateElementAdd state owner identity (.data value)

def privateMethodAdd (state : State) (owner identity : Nat) (value : Value) : Except EvalError State :=
  privateElementAdd state owner identity (.method value)

/-- Structural allocated-owner endpoint. A prototype is caller-supplied and
must already be an ordinary allocated object when present. Existing ghost slot
metadata at the fresh object address is rejected, never silently overwritten. -/
def initialInstanceState (definition : DataClass) (prototype : Option Nat) (before : State) : State :=
  {before with
    environment := definition.environment
    thisValue := .object before.objects.length
    objects := before.objects ++ [{prototype}]
    privates := ⟨definition.names, (before.objects.length, []) :: before.privates.elements⟩}

def beginInstance (definition : DataClass) (prototype : Option Nat) (before : State) :
    Except EvalError (Nat × State) := do
  if (before.privates.slots.lookup before.objects.length).isSome then .error .privateBrand else
  match prototype with
  | some reference =>
    match before.objects[reference]? with
    | none => .error .invalidReference
    | some _ => .ok (before.objects.length, initialInstanceState definition prototype before)
  | none => .ok (before.objects.length, initialInstanceState definition prototype before)

/-- Evaluate this field's initializer before adding its private identity.
Later fields and the current field have no slot until their own add occurs.
Type/optional metadata contributes no runtime validation or omission. -/
def initializeField (fuel limit : Nat) (field : PrivateField) (owner : Nat) (before : State) :
    Except EvalError State := do
  let (value, state) ← match field.initializer with
    | none => .ok (.undefined, before)
    | some expression => evalExpression fuel limit expression before
  let identity ← match state.privates.names.lookup field.name with
    | none => .error .privateScope
    | some identity => .ok identity
  privateAdd state owner identity value

def initializeFields : Nat → Nat → List PrivateField → Nat → State → Except EvalError State
  | 0, _, _, _, _ => .error .exhausted
  | _ + 1, _, [], _, before => .ok before
  | fuel + 1, limit, field :: rest, owner, before => do
    let next ← initializeField fuel limit field owner before
    initializeFields fuel limit rest owner next

def restoreDataCaller (before after : State) : State :=
  {after with
    environment := before.environment
    thisValue := before.thisValue
    privates := {after.privates with names := before.privates.names}}

/-- Supported data-field instance allocation/initialization. This is not native
newTarget/prototype lookup, default-constructor semantics, private-method
installation, derived constructors or general mutable module/closure cells. -/
def instantiateDataClass (fuel limit : Nat) (definition : DataClass) (prototype : Option Nat)
    (before : State) : Except EvalError (Nat × State) := do
  let (owner, state) ← beginInstance definition prototype before
  let state ← initializeFields fuel limit definition.fields owner state
  return (owner, restoreDataCaller before state)

theorem privateAdd_normal (state : State) (owner identity : Nat) (value : Value)
    (object : ECMA2025.OrdinaryObject) (prior : List (Nat × PrivateElement))
    (found : state.objects[owner]? = some object)
    (fields : state.privates.elements.lookup owner = some prior) (absent : prior.lookup identity = none) :
    privateAdd state owner identity value = .ok (addedPrivateState state owner identity value prior) := by
  simp [privateAdd, privateElementAdd, addedPrivateState, found, fields, absent]

theorem initialize_no_value (fuel limit : Nat) (name : String) (optional : Bool)
    (annotation : Option TypeSyntax) (owner : Nat) (before : State) :
    initializeField fuel limit ⟨name, optional, annotation, none⟩ owner before =
      (do
        let identity ← match before.privates.names.lookup name with
          | none => .error .privateScope
          | some identity => .ok identity
        privateAdd before owner identity .undefined) := by
  rfl

theorem beginInstance_none (definition : DataClass) (before : State)
    (fresh : before.privates.slots.lookup before.objects.length = none) :
    beginInstance definition none before =
      .ok (before.objects.length, initialInstanceState definition none before) := by
  simp [beginInstance, fresh]

theorem beginInstance_some (definition : DataClass) (before : State) (prototype : Nat)
    (object : ECMA2025.OrdinaryObject)
    (fresh : before.privates.slots.lookup before.objects.length = none)
    (found : before.objects[prototype]? = some object) :
    beginInstance definition (some prototype) before =
      .ok (before.objects.length, initialInstanceState definition (some prototype) before) := by
  simp [beginInstance, fresh, found]

private theorem foldMax_initial (initial : Nat) (values : List Nat) :
    initial ≤ values.foldl Nat.max initial := by
  induction values generalizing initial with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact Nat.le_trans (Nat.le_max_left initial head) (ih _)

private theorem foldMax_member (initial : Nat) (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldl Nat.max initial := by
  induction values generalizing initial with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (Nat.le_max_right initial value) (foldMax_initial _ _)
    · exact ih _ member

theorem initialPrivateWorld_fresh (state : State) (identity : Nat)
    (used : identity ∈ storedPrivateIdentities state) : identity < (initialPrivateWorld state).nextIdentity := by
  have bound := foldMax_member 0 (storedPrivateIdentities state) identity used
  simp only [initialPrivateWorld]
  omega

theorem definition_name_range (definition : DataClass) (name : String) (identity : Nat)
    (member : (name, identity) ∈ definition.names) :
    definition.baseIdentity ≤ identity ∧ identity < definition.baseIdentity + definition.fields.length := by
  simp only [DataClass.names, List.mem_map] at member
  obtain ⟨⟨field, index⟩, member, equal⟩ := member
  have inside := (List.mem_zipIdx' member).1
  cases equal
  omega

theorem defineDataClass_reserves (fields : List PrivateField) (before : State) (world : PrivateWorld)
    (definition : DataClass) (next : PrivateWorld)
    (defined : defineDataClass fields before world = some (definition, next)) :
    definition.fields = fields ∧ definition.baseIdentity = world.nextIdentity ∧
      definition.environment = before.environment ∧ next.nextIdentity = world.nextIdentity + fields.length := by
  simp only [defineDataClass] at defined
  split at defined
  · cases defined
    exact ⟨rfl, rfl, rfl, rfl⟩
  · contradiction

/-- Even before any instance exists, the returned reservation world separates
all identities in successive definitions. Reusing a definition for another
instance intentionally reuses its own identities. -/
theorem successive_definitions_disjoint (fieldsA fieldsB : List PrivateField) (beforeA beforeB : State)
    (world next final : PrivateWorld) (first second : DataClass)
    (definedA : defineDataClass fieldsA beforeA world = some (first, next))
    (definedB : defineDataClass fieldsB beforeB next = some (second, final))
    (nameA nameB : String) (identityA identityB : Nat)
    (memberA : (nameA, identityA) ∈ first.names) (memberB : (nameB, identityB) ∈ second.names) :
    identityA ≠ identityB := by
  have fields := defineDataClass_reserves fieldsA beforeA world first next definedA
  have later := defineDataClass_reserves fieldsB beforeB next second final definedB
  have firstRange := definition_name_range first nameA identityA memberA
  have secondRange := definition_name_range second nameB identityB memberB
  rw [fields.1, fields.2.1] at firstRange
  rw [later.2.1] at secondRange
  have advance := fields.2.2.2
  omega

end HonoLean.Upstream.SourceSubset
