import HonoLean.Upstream.SourceSubset.Syntax
import Init.Data.List.SplitOn.Lemmas
import Init.Data.List.Nat.TakeDrop

namespace HonoLean.Upstream.ECMA2025

open SourceSubset (JSString)

/-!
A normalized, single-code-unit fragment of ECMA-262 (2025) 22.1.3.23,
https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.split
and 6.1.4.1 StringIndexOf. The receiver is already a primitive UTF-16 string;
the separator is already a primitive string of exactly one code unit; the limit
is already normalized. Standard intrinsic dispatch and successful allocation
are premises of the intended interpretation, not operations proved here.

This module proves equivalence of two mathematical descriptions. It does not
prove the adequacy of this formalization against a full ECMAScript semantics,
ToString/ToUint32/Symbol.split dispatch, object properties, or a native engine.
Theorems quantify over all lists and Nat limits, a larger mathematical domain
than legal native strings (length at most 2^53 - 1) and unsigned-32-bit limits.
-/

/-- Search left to right, returning the first matching code-unit offset. -/
def firstIndex (separator : UInt16) : JSString → Option Nat
  | [] => none
  | unit :: rest =>
    if unit = separator then some 0 else (firstIndex separator rest).map Nat.succ

/-- The nonempty, one-unit specialization of StringIndexOf, with an absolute
cursor. `none` represents the specification's not-found result. -/
def stringIndexOfUnit (input : JSString) (separator : UInt16) (cursor : Nat) : Option Nat :=
  (firstIndex separator (input.drop cursor)).map (cursor + ·)

/-- Specification substring with ordered nonnegative code-unit indices. -/
def substring (input : JSString) (start stop : Nat) : JSString :=
  (input.drop start).take (stop - start)

/-- Steps 11–17, with the still-available output capacity encoding `lim` minus
the number of appended substrings. A match appends a substring before stopping
at the limit; a missing match appends the final suffix, including an empty one.
Structural recursion on capacity avoids an arbitrary execution-fuel cutoff. -/
def splitSteps (input : JSString) (separator : UInt16) :
    Nat → Nat → List JSString → List JSString
  | 0, _, substrings => substrings
  | capacity + 1, cursor, substrings =>
    match stringIndexOfUnit input separator cursor with
    | none => substrings ++ [input.drop cursor]
    | some index =>
      splitSteps input separator capacity (index + 1)
        (substrings ++ [substring input cursor index])

/-- Steps 6 and 10 are explicit; the separator-empty and separator-undefined
branches cannot occur in the declared single-unit normalized fragment. -/
def stringSplit (input : JSString) (separator : UInt16) (limit : Nat) : List JSString :=
  if limit = 0 then []
  else if input.isEmpty then [[]]
  else splitSteps input separator limit 0 []

theorem firstIndex_none {separator : UInt16} {input : JSString}
    (missing : firstIndex separator input = none) : separator ∉ input := by
  induction input with
  | nil => simp
  | cons unit rest ih =>
    by_cases equal : unit = separator
    · simp [firstIndex, equal] at missing
    · simp only [firstIndex, equal, ↓reduceIte, Option.map_eq_none_iff] at missing
      simp [Ne.symm equal, ih missing]

/-- A successful search exhibits a delimiter-free prefix and the actual
matching code unit, proving both occurrence and first-match minimality. -/
theorem firstIndex_some {separator : UInt16} {input : JSString} {index : Nat}
    (found : firstIndex separator input = some index) :
    separator ∉ input.take index ∧
      input = input.take index ++ separator :: input.drop (index + 1) := by
  induction input generalizing index with
  | nil => simp [firstIndex] at found
  | cons unit rest ih =>
    by_cases equal : unit = separator
    · simp only [firstIndex, equal, ↓reduceIte, Option.some.injEq] at found
      subst index
      simp [equal]
    · simp only [firstIndex, equal, ↓reduceIte] at found
      cases result : firstIndex separator rest with
      | none => simp [result] at found
      | some offset =>
        simp only [result, Option.map_some, Option.some.injEq] at found
        subst index
        obtain ⟨clean, decomposition⟩ := ih result
        constructor
        · simpa [Ne.symm equal] using clean
        · simpa [Nat.succ_eq_add_one] using congrArg (unit :: ·) decomposition

/-- Absolute cursor form of the first-match decomposition. The prefix has no
earlier occurrence, and the next cursor skips exactly the matching code unit. -/
theorem stringIndexOfUnit_some {input : JSString} {separator : UInt16}
    {cursor index : Nat} (found : stringIndexOfUnit input separator cursor = some index) :
    cursor ≤ index ∧ separator ∉ substring input cursor index ∧
      input.drop cursor = substring input cursor index ++ separator :: input.drop (index + 1) := by
  unfold stringIndexOfUnit at found
  cases search : firstIndex separator (input.drop cursor) with
  | none => simp [search] at found
  | some offset =>
    simp only [search, Option.map_some, Option.some.injEq] at found
    subst index
    obtain ⟨clean, decomposition⟩ := firstIndex_some search
    refine ⟨Nat.le_add_right _ _, ?_, ?_⟩
    · simpa [substring] using clean
    · simpa [substring, List.drop_drop, Nat.add_assoc] using decomposition

/-- The last available slot returns immediately after appending its field.
In particular, it neither discards an empty field nor appends a final suffix. -/
theorem splitSteps_lastSlot {input : JSString} {separator : UInt16}
    {cursor index : Nat} (found : stringIndexOfUnit input separator cursor = some index)
    (substrings : List JSString) :
    splitSteps input separator 1 cursor substrings =
      substrings ++ [substring input cursor index] := by
  simp [splitSteps, found]

theorem splitSteps_refines (input : JSString) (separator : UInt16)
    (capacity cursor : Nat) (substrings : List JSString) :
    splitSteps input separator capacity cursor substrings =
      substrings ++ ((input.drop cursor).splitOn separator).take capacity := by
  induction capacity generalizing cursor substrings with
  | zero => simp [splitSteps]
  | succ capacity ih =>
    unfold splitSteps
    unfold stringIndexOfUnit
    cases search : firstIndex separator (input.drop cursor) with
    | none =>
      simp only [Option.map_none]
      rw [List.splitOn_eq_singleton (firstIndex_none search)]
      simp
    | some offset =>
      simp only [Option.map_some]
      rw [ih]
      obtain ⟨clean, decomposition⟩ := firstIndex_some search
      have splitAt : (input.drop cursor).splitOn separator =
          (input.drop cursor).take offset ::
            ((input.drop cursor).drop (offset + 1)).splitOn separator := by
        calc
          (input.drop cursor).splitOn separator =
              ((input.drop cursor).take offset ++
                separator :: (input.drop cursor).drop (offset + 1)).splitOn separator :=
            congrArg (List.splitOn separator) decomposition
          _ = _ := List.splitOn_append_cons_self_of_not_mem clean _
      rw [splitAt]
      simp [substring, List.drop_drop, Nat.add_assoc, List.append_assoc]

/-- The independently structured cursor/search/substring model agrees with the
existing list primitive. No normative-source or native-engine adequacy is
assumed as a logical hypothesis or established by this model-equivalence proof. -/
theorem stringSplit_refines (input : JSString) (separator : UInt16) (limit : Nat) :
    stringSplit input separator limit = (input.splitOn separator).take limit := by
  by_cases zero : limit = 0
  · simp [stringSplit, zero]
  · cases input with
    | nil => cases limit with
      | zero => exact False.elim (zero rfl)
      | succ limit => simp [stringSplit]
    | cons unit rest =>
      simp [stringSplit, zero, splitSteps_refines]

/-- A normalized limit therefore bounds the dense array's prospective length;
at the default limit the result has at most 2^32 - 1 elements. -/
theorem stringSplit_length_le (input : JSString) (separator : UInt16) (limit : Nat) :
    (stringSplit input separator limit).length ≤ limit := by
  rw [stringSplit_refines, List.length_take]
  exact Nat.min_le_left _ _

/-- info: 'HonoLean.Upstream.ECMA2025.stringSplit_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stringSplit_refines

end HonoLean.Upstream.ECMA2025
