import HonoLean.Upstream.SourceSubset.Syntax

namespace HonoLean.Upstream.ECMA2025.StringSet

open SourceSubset (JSString)

/-!
Compact normalized primitive-string Set state. Strings are immutable UTF-16
unit lists, so keyed-collection canonicalization does not change them and
SameValue compares their unit sequences. Native constructors, iterator method
lookup, interleaved mutation, object-valued keys and engine adequacy remain
outside this model. StringSetSteps supplies the indexed-scan/iterator account.
-/

def add (entries : List JSString) (key : JSString) : List JSString :=
  if key ∈ entries then entries else entries ++ [key]

def values (entries : List JSString) : List JSString := entries

/-- Independent witness for the first event containing one primitive string. -/
def FirstOccurrence (events : List JSString) (key : JSString) (index : Nat) : Prop :=
  events[index]? = some key ∧ ∀ earlier, earlier < index → events[earlier]? ≠ some key

inductive FirstMatches (events : List JSString) : List Nat → List JSString → Prop where
  | nil : FirstMatches events [] []
  | cons {index key indices keys} (first : FirstOccurrence events key index)
      (rest : FirstMatches events indices keys) : FirstMatches events (index :: indices) (key :: keys)

/-- Membership coverage plus strictly ordered first-occurrence witnesses.
The contract invokes neither add, a fold, a deduplication algorithm nor the
source interpreter. Equal UTF-16 strings share one output occurrence. -/
def OrderedFirstOccurrences (events keys : List JSString) : Prop :=
  keys.Nodup ∧ (∀ key, key ∈ keys ↔ key ∈ events) ∧
    ∃ indices, indices.Pairwise (· < ·) ∧ FirstMatches events indices keys

theorem firstOccurrence_bound {events : List JSString} {key : JSString} {index : Nat}
    (first : FirstOccurrence events key index) : index < events.length :=
  (List.getElem?_eq_some_iff.mp first.1).1

theorem firstOccurrence_append {events : List JSString} {key : JSString} {index : Nat}
    (first : FirstOccurrence events key index) (suffix : List JSString) :
    FirstOccurrence (events ++ suffix) key index := by
  have bound := firstOccurrence_bound first
  constructor
  · rw [List.getElem?_append_left bound]
    exact first.1
  · intro earlier less
    rw [List.getElem?_append_left (by omega : earlier < events.length)]
    exact first.2 earlier less

theorem firstOccurrence_new (events : List JSString) (key : JSString) (absent : key ∉ events) :
    FirstOccurrence (events ++ [key]) key events.length := by
  constructor
  · simp
  · intro earlier less equal
    rw [List.getElem?_append_left less] at equal
    exact absent (List.mem_of_getElem? equal)

theorem firstMatches_append {events : List JSString} {indices : List Nat} {keys : List JSString}
    (matched : FirstMatches events indices keys) (suffix : List JSString) :
    FirstMatches (events ++ suffix) indices keys := by
  induction matched with
  | nil => exact .nil
  | cons first _ ih => exact .cons (firstOccurrence_append first suffix) ih

theorem firstMatches_bound {events : List JSString} {indices : List Nat} {keys : List JSString}
    (matched : FirstMatches events indices keys) : ∀ index ∈ indices, index < events.length := by
  induction matched with
  | nil => simp
  | cons first _ ih =>
    intro index member
    rcases List.mem_cons.mp member with equal | member
    · subst index
      exact firstOccurrence_bound first
    · exact ih index member

theorem firstMatches_snoc {events : List JSString} {indices : List Nat} {keys : List JSString}
    (matched : FirstMatches events indices keys) (index : Nat) (key : JSString)
    (first : FirstOccurrence events key index) :
    FirstMatches events (indices ++ [index]) (keys ++ [key]) := by
  induction matched with
  | nil => exact .cons first .nil
  | cons earlier _ ih => exact .cons earlier ih

theorem add_mem (entries : List JSString) (key candidate : JSString) :
    candidate ∈ add entries key ↔ candidate ∈ entries ∨ candidate = key := by
  by_cases present : key ∈ entries
  · simp only [add, present, ↓reduceIte]
    constructor
    · exact Or.inl
    · rintro (member | equal)
      · exact member
      · exact equal ▸ present
  · simp [add, present]

theorem add_nodup (entries : List JSString) (key : JSString) (unique : entries.Nodup) :
    (add entries key).Nodup := by
  by_cases present : key ∈ entries
  · simpa [add, present] using unique
  · simp only [add, present, ↓reduceIte, List.nodup_append]
    refine ⟨unique, by simp, ?_⟩
    intro earlier member later singleton equal
    have same : later = key := by simpa using singleton
    exact present ((equal.trans same) ▸ member)

theorem ordered_add (events entries : List JSString) (key : JSString)
    (ordered : OrderedFirstOccurrences events entries) :
    OrderedFirstOccurrences (events ++ [key]) (add entries key) := by
  obtain ⟨unique, coverage, indices, increasing, matched⟩ := ordered
  refine ⟨add_nodup entries key unique, ?_, ?_⟩
  · intro candidate
    rw [add_mem]
    simp only [List.mem_append, List.mem_singleton]
    exact or_congr (coverage candidate) Iff.rfl
  · by_cases present : key ∈ entries
    · simp only [add, present, ↓reduceIte]
      exact ⟨indices, increasing, firstMatches_append matched [key]⟩
    · have absent : key ∉ events := fun member => present ((coverage key).mpr member)
      simp only [add, present, ↓reduceIte]
      refine ⟨indices ++ [events.length], ?_, firstMatches_snoc (firstMatches_append matched [key])
        events.length key (firstOccurrence_new events key absent)⟩
      rw [List.pairwise_append]
      refine ⟨increasing, by simp, ?_⟩
      intro earlier member later singleton
      have same : later = events.length := by simpa using singleton
      subst later
      exact firstMatches_bound matched earlier member

def fromTrace (events : List JSString) : List JSString := events.foldl add []

theorem fromTrace_snoc (events : List JSString) (key : JSString) :
    fromTrace (events ++ [key]) = add (fromTrace events) key := by
  simp [fromTrace, List.foldl_append]

theorem fromTrace_ordered (events : List JSString) :
    OrderedFirstOccurrences events (fromTrace events) := by
  have reversed : ∀ reverseEvents : List JSString,
      OrderedFirstOccurrences reverseEvents.reverse (fromTrace reverseEvents.reverse) := by
    intro reverseEvents
    induction reverseEvents with
    | nil => exact ⟨by simp [fromTrace], by simp [fromTrace], [], by simp, .nil⟩
    | cons key rest ih =>
      simpa only [List.reverse_cons, fromTrace_snoc] using ordered_add rest.reverse (fromTrace rest.reverse) key ih
  simpa using reversed events.reverse

theorem fromTrace_nodup (events : List JSString) : (fromTrace events).Nodup :=
  (fromTrace_ordered events).1

end HonoLean.Upstream.ECMA2025.StringSet
