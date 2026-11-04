import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset

theorem replacePrivateData_keys (identity : Nat) (value : Value) (fields : List (Nat × PrivateElement)) :
    (replacePrivateData identity value fields).map Prod.fst = fields.map Prod.fst := by
  induction fields with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, element⟩ := entry
    simp only [replacePrivateData]
    split
    · rfl
    · simpa using congrArg (List.cons key) ih

theorem replacePrivateData_found (fields : List (Nat × PrivateElement)) (identity : Nat)
    (value : Value) (old : PrivateElement) (found : fields.lookup identity = some old) :
    (replacePrivateData identity value fields).lookup identity = some (.data value) := by
  induction fields with
  | nil => simp at found
  | cons entry rest ih =>
    obtain ⟨key, element⟩ := entry
    by_cases equal : identity = key
    · subst key
      simp [replacePrivateData]
    · have unequal : (identity == key) = false := beq_eq_false_iff_ne.mpr equal
      simp only [List.lookup, unequal] at found
      simpa [replacePrivateData, unequal, List.lookup] using ih found

theorem replacePrivateData_other (fields : List (Nat × PrivateElement)) (identity other : Nat)
    (value : Value) (different : other ≠ identity) :
    (replacePrivateData identity value fields).lookup other = fields.lookup other := by
  induction fields with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, element⟩ := entry
    by_cases equal : identity = key
    · subst key
      have unequal : (other == identity) = false := beq_eq_false_iff_ne.mpr different
      simp [replacePrivateData, List.lookup, unequal]
    · have unequal : (identity == key) = false := beq_eq_false_iff_ne.mpr equal
      simp [replacePrivateData, unequal, List.lookup, ih]

theorem replacePrivateOwner_keys (owner identity : Nat) (value : Value)
    (slots : List (Nat × List (Nat × PrivateElement))) :
    (replacePrivateOwner owner identity value slots).map Prod.fst = slots.map Prod.fst := by
  induction slots with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, fields⟩ := entry
    simp only [replacePrivateOwner]
    split
    · rfl
    · simpa using congrArg (List.cons key) ih

theorem replacePrivateOwner_found (slots : List (Nat × List (Nat × PrivateElement)))
    (owner identity : Nat) (value : Value) (fields : List (Nat × PrivateElement))
    (found : slots.lookup owner = some fields) :
    (replacePrivateOwner owner identity value slots).lookup owner = some (replacePrivateData identity value fields) := by
  induction slots with
  | nil => simp at found
  | cons entry rest ih =>
    obtain ⟨key, elements⟩ := entry
    by_cases equal : owner = key
    · subst key
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at found
      subst elements
      simp [replacePrivateOwner]
    · have unequal : (owner == key) = false := beq_eq_false_iff_ne.mpr equal
      simp only [List.lookup, unequal] at found
      simpa [replacePrivateOwner, unequal, List.lookup] using ih found

theorem replacePrivateOwner_other (slots : List (Nat × List (Nat × PrivateElement)))
    (owner identity other : Nat) (value : Value) (different : other ≠ owner) :
    (replacePrivateOwner owner identity value slots).lookup other = slots.lookup other := by
  induction slots with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, fields⟩ := entry
    by_cases equal : owner = key
    · subst key
      have unequal : (other == owner) = false := beq_eq_false_iff_ne.mpr different
      simp [replacePrivateOwner, List.lookup, unequal]
    · have unequal : (owner == key) = false := beq_eq_false_iff_ne.mpr equal
      simp [replacePrivateOwner, unequal, List.lookup, ih]

/-- Independent successful DATA write observation at the PutValue state, after
any RHS effects. It states the permitted input kind, new value and
preserved raw tags/keys/owners and public state, without mentioning an evaluator
or a particular list-update implementation. No deep graph disjointness is needed:
the private cell changes, while referenced ordinary objects are unchanged. -/
structure PrivateWriteContract (before after : State) (owner identity : Nat) (value : Value) : Prop where
  environment : after.environment = before.environment
  thisValue : after.thisValue = before.thisValue
  names : after.privates.names = before.privates.names
  objects : after.objects = before.objects
  heap : after.heap = before.heap
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  beforeData : ∃ fields old,
    before.privates.elements.lookup owner = some fields ∧ fields.lookup identity = some (.data old)
  ownerKeys : after.privates.elements.map Prod.fst = before.privates.elements.map Prod.fst
  otherOwners : ∀ other, other ≠ owner → after.privates.elements.lookup other = before.privates.elements.lookup other
  fields : ∃ prior final,
    before.privates.elements.lookup owner = some prior ∧
    after.privates.elements.lookup owner = some final ∧
    final.lookup identity = some (.data value) ∧
    final.map Prod.fst = prior.map Prod.fst ∧
    ∀ other, other ≠ identity → final.lookup other = prior.lookup other

theorem writePrivateDataState_satisfies (before : State) (owner identity : Nat) (value old : Value)
    (fields : List (Nat × PrivateElement))
    (brand : before.privates.elements.lookup owner = some fields)
    (field : fields.lookup identity = some (.data old)) :
    PrivateWriteContract before (writePrivateDataState before owner identity value) owner identity value := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨fields, old, brand, field⟩,
    replacePrivateOwner_keys _ _ _ _, ?_, ?_⟩
  · intro other different
    exact replacePrivateOwner_other _ _ _ _ _ different
  · exact ⟨fields, replacePrivateData identity value fields, brand,
      replacePrivateOwner_found _ _ _ _ _ brand,
      replacePrivateData_found _ _ _ _ field, replacePrivateData_keys _ _ _,
      fun other different => replacePrivateData_other _ _ _ _ different⟩

theorem privateSet_satisfies (before : State) (owner identity : Nat) (value old : Value)
    (object : ECMA2025.OrdinaryObject) (fields : List (Nat × PrivateElement))
    (allocated : before.objects[owner]? = some object)
    (brand : before.privates.elements.lookup owner = some fields)
    (field : fields.lookup identity = some (.data old)) :
    ∃ after, privateSet (.object owner) identity value before = .ok after ∧
      PrivateWriteContract before after owner identity value :=
  ⟨_, privateSet_data before owner identity value old object fields allocated brand field,
    writePrivateDataState_satisfies before owner identity value old fields brand field⟩

theorem writePrivateDataState_other_owner (before : State) (owner identity other : Nat)
    (value : Value) (different : other ≠ owner) :
    (writePrivateDataState before owner identity value).privates.slots.lookup other =
      before.privates.slots.lookup other := by
  rw [PrivateStore.slots_lookup, PrivateStore.slots_lookup]
  exact congrArg _ (replacePrivateOwner_other before.privates.elements owner identity other value different)

theorem privateGet_write_other_owner (before : State) (owner identity other : Nat)
    (value : Value) (spelling : String) (different : other ≠ owner) :
    privateGet (.object other) spelling (writePrivateDataState before owner identity value) =
      privateGet (.object other) spelling before := by
  have raw := replacePrivateOwner_other before.privates.elements owner identity other value different
  simp [privateGet, writePrivateDataState, PrivateStore.slots_lookup, raw]

theorem privateGet_write_other_identity (before : State) (owner identity other : Nat)
    (value : Value) (spelling : String) (fields : List (Nat × PrivateElement))
    (lexical : before.privates.names.lookup spelling = some other)
    (brand : before.privates.elements.lookup owner = some fields) (different : other ≠ identity) :
    privateGet (.object owner) spelling (writePrivateDataState before owner identity value) =
      privateGet (.object owner) spelling before := by
  have changed := replacePrivateOwner_found before.privates.elements owner identity value fields brand
  have kept := replacePrivateData_other fields identity other value different
  simp [privateGet, writePrivateDataState, lexical, PrivateStore.slots_lookup,
    changed, brand, lookup_map_values, kept, bind, Except.bind]

theorem privateGet_write_same (before : State) (owner identity : Nat) (spelling : String)
    (value old : Value) (object : ECMA2025.OrdinaryObject) (fields : List (Nat × PrivateElement))
    (lexical : before.privates.names.lookup spelling = some identity)
    (allocated : before.objects[owner]? = some object)
    (brand : before.privates.elements.lookup owner = some fields)
    (field : fields.lookup identity = some (.data old)) :
    privateGet (.object owner) spelling (writePrivateDataState before owner identity value) = .ok value := by
  have changed := replacePrivateOwner_found before.privates.elements owner identity value fields brand
  have stored := replacePrivateData_found fields identity value (.data old) field
  simp [privateGet, writePrivateDataState, lexical, allocated, PrivateStore.slots_lookup,
    changed, lookup_map_values, stored, bind, Except.bind]

/-- info: 'HonoLean.Upstream.SourceSubset.privateSet_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms privateSet_satisfies

end HonoLean.Upstream.SourceSubset
