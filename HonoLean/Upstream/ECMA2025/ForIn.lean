import HonoLean.Upstream.ECMA2025.Objects

namespace HonoLean.Upstream.ECMA2025

open SourceSubset

/-- Descriptor inspection never reads its data value or invokes a getter. -/
def descriptorEnumerable : PropertyDescriptor → Bool
  | .data _ _ enumerable _ | .accessor _ _ enumerable _ => enumerable

def EnumerableName (object : OrdinaryObject) (key : JSString) : Prop :=
  ∃ descriptor, object.own.lookup key = some descriptor ∧ descriptorEnumerable descriptor = true

private def descriptorAtEnumerable (object : OrdinaryObject) (key : JSString) : Bool :=
  match object.own.lookup key with
  | none => false
  | some descriptor => descriptorEnumerable descriptor

/-- Exact null-prototype specialization: inspect own string names and their
FIRST descriptors. Unique native own names are an explicit domain premise.
List order is only a representative, not native OwnPropertyKeys ordering.
General prototypes, inherited names, proxies, symbols and mutation are open. -/
def enumerableOwn (object : OrdinaryObject) : List JSString :=
  (object.own.map Prod.fst).filter (descriptorAtEnumerable object)

theorem enumerableOwn_member (object : OrdinaryObject) (key : JSString) :
    key ∈ enumerableOwn object ↔ EnumerableName object key := by
  constructor
  · intro member
    obtain ⟨_, enumerable⟩ := List.mem_filter.mp member
    cases found : object.own.lookup key with
    | none => simp [descriptorAtEnumerable, found] at enumerable
    | some descriptor => exact ⟨descriptor, found, by simpa [descriptorAtEnumerable, found] using enumerable⟩
  · rintro ⟨descriptor, found, enumerable⟩
    obtain ⟨front, back, equation, _⟩ := List.lookup_eq_some_iff.mp found
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa [descriptorAtEnumerable, found] using enumerable⟩
    rw [equation]
    simp

/-- Overapproximate legal key orders by complete duplicate-free enumerations.
Native OwnPropertyKeys has further ordering rules. The source body theorem must
establish insensitivity to every order in this larger relation. -/
structure LegalForInOrder (object : OrdinaryObject) (keys : List JSString) : Prop where
  nullPrototype : object.prototype = none
  wellFormed : WellFormedObject object
  unique : keys.Nodup
  complete : ∀ key, key ∈ keys ↔ EnumerableName object key

theorem enumerableOwn_legal (object : OrdinaryObject) (nullPrototype : object.prototype = none)
    (wellFormed : WellFormedObject object) : LegalForInOrder object (enumerableOwn object) :=
  ⟨nullPrototype, wellFormed, List.Pairwise.filter _ wellFormed, enumerableOwn_member object⟩

theorem enumerableOwn_empty_iff (object : OrdinaryObject) :
    enumerableOwn object = [] ↔ ¬∃ key, EnumerableName object key := by
  constructor
  · intro empty existsKey
    obtain ⟨key, found⟩ := existsKey
    have member := (enumerableOwn_member object key).mpr found
    rw [empty] at member
    cases member
  · intro absent
    cases equation : enumerableOwn object with
    | nil => rfl
    | cons key rest =>
      have member : key ∈ enumerableOwn object := by rw [equation]; simp
      exact False.elim (absent ⟨key, (enumerableOwn_member object key).mp member⟩)

theorem enumerableOwn_empty_of_descriptors (object : OrdinaryObject)
    (noneEnumerable : ∀ key descriptor, object.own.lookup key = some descriptor → descriptorEnumerable descriptor = false) :
    enumerableOwn object = [] := by
  apply (enumerableOwn_empty_iff object).mpr
  rintro ⟨key, descriptor, found, enumerable⟩
  rw [noneEnumerable key descriptor found] at enumerable
  cases enumerable

end HonoLean.Upstream.ECMA2025
