import HonoLean.Upstream.ECMA2025.StringSplit

namespace HonoLean.Upstream.ECMA2025

open SourceSubset (JSString)

/-!
Normalized finite-integer, primitive UTF-16 models corresponding to ECMA-262
2025 §22.1.3.9 and §22.1.3.22:
https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.indexof
https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.slice

The receiver/search unit are already primitive and the positions already finite
mathematical integers. NaN, infinities, signed zero, ToString/ToIntegerOrInfinity,
mutable method lookup, realm behavior, resources and engine adequacy are outside
these models. Integer bounds below support a separate exact-number bridge; they
do not themselves formalize IEEE-754 or establish that bridge.
-/

def normalizeSearchPosition (length : Nat) (position : Int) : Nat :=
  min position.toNat length

theorem normalizeSearchPosition_nonpositive (length : Nat) (position : Int)
    (nonpositive : position ≤ 0) : normalizeSearchPosition length position = 0 := by
  unfold normalizeSearchPosition
  omega

def stringIndexOf (input : JSString) (separator : UInt16) (position : Int) : Int :=
  match stringIndexOfUnit input separator (normalizeSearchPosition input.length position) with
  | none => -1
  | some index => (index : Int)

/-- Independent occurrence/minimality relation; it never invokes a search. -/
def FirstUnitAt (input : JSString) (separator : UInt16) (cursor index : Nat) : Prop :=
  cursor ≤ index ∧ input[index]? = some separator ∧
    ∀ earlier, cursor ≤ earlier → earlier < index → input[earlier]? ≠ some separator

theorem firstUnitAt_bound {input : JSString} {separator : UInt16} {cursor index : Nat}
    (occurrence : FirstUnitAt input separator cursor index) : index < input.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp occurrence.2.1
  exact bound

theorem firstUnitAt_unique {input : JSString} {separator : UInt16} {cursor a b : Nat}
    (left : FirstUnitAt input separator cursor a)
    (right : FirstUnitAt input separator cursor b) : a = b := by
  by_cases less : a < b
  · exact False.elim (right.2.2 a left.1 less left.2.1)
  · by_cases greater : b < a
    · exact False.elim (left.2.2 b right.1 greater right.2.1)
    · omega

private theorem firstIndex_bound {input : JSString} {separator : UInt16} {index : Nat}
    (found : firstIndex separator input = some index) : index < input.length := by
  induction input generalizing index with
  | nil => simp [firstIndex] at found
  | cons unit rest ih =>
    by_cases same : unit = separator
    · simp [firstIndex, same] at found
      subst index
      simp
    · cases result : firstIndex separator rest with
      | none => simp [firstIndex, same, result] at found
      | some offset =>
        simp only [firstIndex, same, ↓reduceIte, result, Option.map_some,
          Option.some.injEq] at found
        subst index
        have bound := ih result
        simp only [List.length_cons]
        omega

private theorem firstIndex_sound {input : JSString} {separator : UInt16} {index : Nat}
    (found : firstIndex separator input = some index) : FirstUnitAt input separator 0 index := by
  obtain ⟨clean, decomposition⟩ := firstIndex_some found
  have bound := firstIndex_bound found
  have prefixLength : (input.take index).length = index := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  refine ⟨Nat.zero_le _, ?_, ?_⟩
  · rw [decomposition, List.getElem?_append_right (by omega)]
    simp [prefixLength]
  · intro earlier _ less equal
    apply clean
    apply List.mem_of_getElem? (i := earlier)
    rw [List.getElem?_take_of_lt less]
    exact equal

theorem stringIndexOfUnit_sound {input : JSString} {separator : UInt16}
    {cursor index : Nat} (found : stringIndexOfUnit input separator cursor = some index) :
    FirstUnitAt input separator cursor index := by
  unfold stringIndexOfUnit at found
  cases search : firstIndex separator (input.drop cursor) with
  | none => simp [search] at found
  | some offset =>
    simp only [search, Option.map_some, Option.some.injEq] at found
    subst index
    have occurrence := firstIndex_sound search
    refine ⟨by omega, ?_, ?_⟩
    · simpa only [List.getElem?_drop] using occurrence.2.1
    · intro earlier lower less equal
      have absent := occurrence.2.2 (earlier - cursor) (by omega) (by omega)
      apply absent
      simpa only [List.getElem?_drop, Nat.add_sub_of_le lower] using equal

theorem stringIndexOfUnit_missing_iff (input : JSString) (separator : UInt16) (cursor : Nat) :
    stringIndexOfUnit input separator cursor = none ↔
      ∀ index, cursor ≤ index → input[index]? ≠ some separator := by
  constructor
  · intro missing index lower equal
    have noUnit : separator ∉ input.drop cursor := by
      apply firstIndex_none
      simpa only [stringIndexOfUnit, Option.map_eq_none_iff] using missing
    apply noUnit
    apply List.mem_of_getElem? (i := index - cursor)
    simpa only [List.getElem?_drop, Nat.add_sub_of_le lower] using equal
  · intro absent
    cases search : stringIndexOfUnit input separator cursor with
    | none => rfl
    | some index =>
      have occurrence := stringIndexOfUnit_sound search
      exact False.elim (absent index occurrence.1 occurrence.2.1)

theorem stringIndexOfUnit_some_iff (input : JSString) (separator : UInt16)
    (cursor index : Nat) :
    stringIndexOfUnit input separator cursor = some index ↔
      FirstUnitAt input separator cursor index := by
  constructor
  · exact stringIndexOfUnit_sound
  · intro occurrence
    cases search : stringIndexOfUnit input separator cursor with
    | none =>
      have absent := (stringIndexOfUnit_missing_iff input separator cursor).mp search
      exact False.elim (absent index occurrence.1 occurrence.2.1)
    | some found =>
      have equal := firstUnitAt_unique (stringIndexOfUnit_sound search) occurrence
      simp [equal]

theorem stringIndexOf_some_iff (input : JSString) (separator : UInt16)
    (position : Int) (index : Nat) :
    stringIndexOf input separator position = (index : Int) ↔
      FirstUnitAt input separator (normalizeSearchPosition input.length position) index := by
  rw [← stringIndexOfUnit_some_iff]
  unfold stringIndexOf
  cases search : stringIndexOfUnit input separator (normalizeSearchPosition input.length position) with
  | none => simp
  | some found =>
    simp only [Option.some.injEq]
    exact Int.ofNat_inj

theorem stringIndexOf_missing_iff (input : JSString) (separator : UInt16) (position : Int) :
    stringIndexOf input separator position = -1 ↔
      ∀ index, normalizeSearchPosition input.length position ≤ index →
        input[index]? ≠ some separator := by
  rw [← stringIndexOfUnit_missing_iff]
  unfold stringIndexOf
  cases search : stringIndexOfUnit input separator (normalizeSearchPosition input.length position) with
  | none => simp
  | some found => simp

theorem stringIndexOf_result (input : JSString) (separator : UInt16) (position : Int) :
    stringIndexOf input separator position = -1 ∨
      ∃ index : Nat, stringIndexOf input separator position = (index : Int) := by
  unfold stringIndexOf
  cases stringIndexOfUnit input separator (normalizeSearchPosition input.length position) with
  | none => exact Or.inl rfl
  | some index => exact Or.inr ⟨index, rfl⟩

theorem firstUnitAt_clamp_iff (input : JSString) (separator : UInt16) (cursor index : Nat) :
    FirstUnitAt input separator (min cursor input.length) index ↔
      FirstUnitAt input separator cursor index := by
  constructor
  · intro occurrence
    have bound := firstUnitAt_bound occurrence
    have lower := occurrence.1
    refine ⟨by omega, occurrence.2.1, ?_⟩
    intro earlier lower less
    exact occurrence.2.2 earlier (by omega) less
  · intro occurrence
    have lower := occurrence.1
    refine ⟨by omega, occurrence.2.1, ?_⟩
    intro earlier lower less
    have bound := firstUnitAt_bound occurrence
    exact occurrence.2.2 earlier (by omega) less

theorem stringIndexOf_from_nat_iff (input : JSString) (separator : UInt16)
    (cursor index : Nat) :
    stringIndexOf input separator (cursor : Int) = (index : Int) ↔
      FirstUnitAt input separator cursor index := by
  rw [stringIndexOf_some_iff]
  simpa only [normalizeSearchPosition, Int.toNat_natCast] using
    firstUnitAt_clamp_iff input separator cursor index

theorem stringIndexOf_from_nat_missing_iff (input : JSString) (separator : UInt16)
    (cursor : Nat) :
    stringIndexOf input separator (cursor : Int) = -1 ↔
      ∀ index, cursor ≤ index → input[index]? ≠ some separator := by
  rw [stringIndexOf_missing_iff]
  simp only [normalizeSearchPosition, Int.toNat_natCast]
  constructor
  · intro absent index lower
    exact absent index (by omega)
  · intro absent index lower equal
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp equal
    exact absent index (by omega) equal

def maximumSafeInteger : Nat := 9007199254740991

/-- Mathematical range needed by a separate exact-native-number interpretation.
The lower sentinel is -1; every successful single-unit match is strictly below
the legal string's length. IEEE-754/coercion adequacy is not proved here. -/
theorem stringIndexOf_safe_range (input : JSString) (separator : UInt16) (position : Int)
    (legal : input.length ≤ maximumSafeInteger) :
    -1 ≤ stringIndexOf input separator position ∧
      stringIndexOf input separator position ≤ (maximumSafeInteger : Int) := by
  unfold stringIndexOf
  cases search : stringIndexOfUnit input separator (normalizeSearchPosition input.length position) with
  | none => simp [maximumSafeInteger]
  | some index =>
    have bound := firstUnitAt_bound (stringIndexOfUnit_sound search)
    dsimp
    omega

def normalizeSliceIndex (length : Nat) (position : Int) : Nat :=
  if position < 0 then ((length : Int) + position).toNat
  else min position.toNat length

def stringSlice (input : JSString) (start : Int) (stop : Option Int := none) : JSString :=
  let beginIndex := normalizeSliceIndex input.length start
  let endIndex := (stop.map (normalizeSliceIndex input.length)).getD input.length
  (input.drop beginIndex).take (endIndex - beginIndex)

theorem normalizeSliceIndex_le (length : Nat) (position : Int) :
    normalizeSliceIndex length position ≤ length := by
  unfold normalizeSliceIndex
  split <;> omega

theorem normalizeSliceIndex_nat (length position : Nat) :
    normalizeSliceIndex length (position : Int) = min position length := by
  have nonnegative : ¬ (position : Int) < 0 := by omega
  simp only [normalizeSliceIndex, nonnegative, ↓reduceIte, Int.toNat_natCast]

theorem normalizeSliceIndex_negative (length : Nat) (position : Int)
    (negative : position < 0) :
    normalizeSliceIndex length position = ((length : Int) + position).toNat := by
  simp only [normalizeSliceIndex, negative, ↓reduceIte]

theorem normalizeSliceIndex_before_beginning (length : Nat) (position : Int)
    (before : position ≤ -(length : Int)) : normalizeSliceIndex length position = 0 := by
  unfold normalizeSliceIndex
  split <;> omega

theorem stringSlice_from_nat (input : JSString) (start : Nat) :
    stringSlice input (start : Int) none = input.drop start := by
  simp only [stringSlice, normalizeSliceIndex_nat, Option.map_none, Option.getD_none]
  rw [← List.length_drop, List.take_length, ← List.drop_eq_drop_min]

theorem stringSlice_from_nat_to_nat (input : JSString) (start stop : Nat) :
    stringSlice input (start : Int) (some (stop : Int)) =
      (input.drop start).take (stop - start) := by
  simp only [stringSlice, normalizeSliceIndex_nat, Option.map_some, Option.getD_some]
  by_cases starts : start ≤ input.length
  · rw [Nat.min_eq_left starts]
    by_cases stops : stop ≤ input.length
    · rw [Nat.min_eq_left stops]
    · rw [Nat.min_eq_right (by omega)]
      rw [List.take_of_length_le (by simp only [List.length_drop]; omega),
        List.take_of_length_le (by simp only [List.length_drop]; omega)]
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge starts))]
    simp [List.drop_eq_nil_of_le (by omega : input.length ≤ start)]

theorem stringSlice_length (input : JSString) (start : Int) (stop : Option Int) :
    (stringSlice input start stop).length =
      (stop.map (normalizeSliceIndex input.length)).getD input.length -
        normalizeSliceIndex input.length start := by
  have starts := normalizeSliceIndex_le input.length start
  have stops : (stop.map (normalizeSliceIndex input.length)).getD input.length ≤ input.length := by
    cases stop with
    | none => exact Nat.le_refl _
    | some value => exact normalizeSliceIndex_le _ _
  simp only [stringSlice, List.length_take, List.length_drop]
  omega

theorem stringSlice_getElem? (input : JSString) (start : Int) (stop : Option Int) (index : Nat) :
    (stringSlice input start stop)[index]? =
      if index < (stop.map (normalizeSliceIndex input.length)).getD input.length -
          normalizeSliceIndex input.length start
      then input[normalizeSliceIndex input.length start + index]? else none := by
  simp only [stringSlice, List.getElem?_take, List.getElem?_drop]

/-- info: 'HonoLean.Upstream.ECMA2025.stringIndexOf_from_nat_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stringIndexOf_from_nat_iff

/-- info: 'HonoLean.Upstream.ECMA2025.stringSlice_from_nat_to_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stringSlice_from_nat_to_nat

end HonoLean.Upstream.ECMA2025
