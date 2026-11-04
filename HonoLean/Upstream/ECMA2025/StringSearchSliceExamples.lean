import HonoLean.Upstream.ECMA2025.StringSearchSlice

namespace HonoLean.Upstream.ECMA2025

example : stringIndexOf [] 63 (-100) = -1 := by cbv
example : stringIndexOf [97, 63, 98, 63] 63 (-100) = 1 := by cbv
example : stringIndexOf [97, 63, 98, 63] 63 2 = 3 := by cbv
example : stringIndexOf [97, 63, 98, 63] 63 100 = -1 := by cbv
example : stringIndexOf [63] 63 8 = -1 := by cbv

/-- Search positions count UTF-16 units, including the middle of a surrogate
pair. A single-unit separator can itself be a low surrogate. -/
example : stringIndexOf [55357, 56832, 63] 63 0 = 2 := by cbv
example : stringIndexOf [55357, 56832, 63] 56832 0 = 1 := by cbv
example : stringIndexOf [55296, 63, 56320] 56320 0 = 2 := by cbv

example : FirstUnitAt [63, 97, 63] 63 1 2 :=
  (stringIndexOf_from_nat_iff _ _ _ _).mp (by cbv)

example : ∀ index, 8 ≤ index → ([63] : SourceSubset.JSString)[index]? ≠ some 63 :=
  (stringIndexOf_from_nat_missing_iff _ _ _).mp (by cbv)

example : normalizeSliceIndex 4 (-2) = 2 := by cbv
example : normalizeSliceIndex 4 (-100) = 0 := by cbv
example : normalizeSliceIndex 4 100 = 4 := by cbv
example : stringSlice [97, 98, 99, 100] (-2) = [99, 100] := by cbv
example : stringSlice [97, 98, 99, 100] 1 (some (-1)) = [98, 99] := by cbv
example : stringSlice [97, 98, 99, 100] (-100) (some 100) = [97, 98, 99, 100] := by cbv
example : stringSlice [97, 98, 99, 100] 3 (some 1) = [] := by cbv
example : stringSlice [97, 98, 99, 100] 100 = [] := by cbv

/-- Slicing can expose either half of an astral pair or a lone surrogate. It
does not repair, decode, normalize or count Unicode scalar values. -/
example : stringSlice [55357, 56832, 63] 1 (some 2) = [56832] := by cbv
example : stringSlice [55296, 63, 56320] (-1) = [56320] := by cbv
example : stringSlice [55296, 63, 56320] 0 (some (-1)) = [55296, 63] := by cbv

/-- Fault witness: ignoring the cursor finds an earlier marker outside the
requested range. The correct search begins at offset eight. -/
example : stringIndexOf [97, 63, 0, 0, 0, 0, 0, 0, 98, 63] 63 0 = 1 ∧
    stringIndexOf [97, 63, 0, 0, 0, 0, 0, 0, 98, 63] 63 8 = 9 := by
  constructor <;> decide +kernel

/-- Fault witness: treating -2 as zero instead of a relative slice index changes
the returned contents. This is distinct from indexOf's negative-position rule. -/
example : stringSlice [97, 98, 99, 100] 0 = [97, 98, 99, 100] ∧
    stringSlice [97, 98, 99, 100] (-2) = [99, 100] := by cbv

end HonoLean.Upstream.ECMA2025
