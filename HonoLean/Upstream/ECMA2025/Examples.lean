import HonoLean.Upstream.ECMA2025.StringSplit

namespace HonoLean.Upstream.ECMA2025

example : stringSplit [47, 97] 47 0 = [] := by cbv
example : stringSplit [] 47 4 = [[]] := by cbv
example : stringSplit [47] 47 4 = [[], []] := by cbv
example : stringSplit [47, 47, 97, 47] 47 9 = [[], [], [97], []] := by cbv
example : stringSplit [47, 97, 47, 98] 47 1 = [[]] := by cbv
example : stringSplit [47, 97, 47, 98] 47 2 = [[], [97]] := by cbv
example : stringSplit [47, 97, 47, 98] 47 3 = [[], [97], [98]] := by cbv

-- Search starts at the supplied cursor, and an end-of-string cursor misses.
example : stringIndexOfUnit [47, 97, 47, 98] 47 1 = some 2 := by cbv
example : stringIndexOfUnit [47] 47 1 = none := by cbv

-- One code-unit separator is generic; neither input nor separator is required
-- to be a Unicode scalar value. Surrogates stay separate 16-bit units.
example : stringSplit [0xD800, 0xDC00, 47, 0xDC00, 47, 0xD800] 47 7 =
    [[0xD800, 0xDC00], [0xDC00], [0xD800]] := by cbv
example : stringSplit [97, 0xD800, 98, 0xD800] 0xD800 4 = [[97], [98], []] := by cbv

/-- Deliberate fault: discard empty fields after the normal cursor loop. -/
def dropsEmptyFault (input : SourceSubset.JSString) (separator : UInt16) (limit : Nat) :=
  (stringSplit input separator limit).filter (fun field => !field.isEmpty)

/-- Deliberate fault: allow one extra append before stopping at a positive
limit. Keeping the zero-limit exit exposes the loop's off-by-one error. -/
def lateLimitFault (input : SourceSubset.JSString) (separator : UInt16) (limit : Nat) :=
  if limit = 0 then [] else splitSteps input separator (limit + 1) 0 []

theorem dropsEmptyFault_not_refines :
    ¬ ∀ input separator limit,
      dropsEmptyFault input separator limit = (input.splitOn separator).take limit := by
  intro claimed
  have counterexample := claimed [47] 47 4
  cbv at counterexample
  contradiction

theorem lateLimitFault_not_refines :
    ¬ ∀ input separator limit,
      lateLimitFault input separator limit = (input.splitOn separator).take limit := by
  intro claimed
  have counterexample := claimed [97, 47, 98] 47 1
  cbv at counterexample
  contradiction

example : (lateLimitFault [97, 47, 98] 47 1).length > 1 := by cbv

end HonoLean.Upstream.ECMA2025
