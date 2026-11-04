import HonoLean.Upstream.ECMA2025.StringSet

namespace HonoLean.Upstream.ECMA2025.StringSetSteps

open SourceSubset (JSString)

/-!
Indexed no-deletion specialization of ECMA-262 2025 SetData operations.
Only primitive strings occur here: CanonicalizeKeyedCollectionKey leaves them
unchanged, and SameValue tests exact UTF-16 contents. No empty/deleted slots can
be produced by construction and add alone. Object keys, deletion, method lookup
and general iterable/exception semantics are not silently covered.
-/

/-- Scan the indexed data from the current position. `none` means an inadequate
model budget; it is never mistaken for a failed membership test. -/
def scanMemberFrom : Nat → List JSString → Nat → JSString → Option Bool
  | 0, _, _, _ => none
  | fuel + 1, entries, index, key =>
    match entries[index]? with
    | none => some false
    | some entry =>
      if entry = key then some true else scanMemberFrom fuel entries (index + 1) key

theorem scan_suffix (earlier suffix : List JSString) (key : JSString) :
    scanMemberFrom (suffix.length + 1) (earlier ++ suffix) earlier.length key =
      some (decide (key ∈ suffix)) := by
  induction suffix generalizing earlier with
  | nil => simp [scanMemberFrom]
  | cons head tail ih =>
    have atHead : (earlier ++ head :: tail)[earlier.length]? = some head := by simp
    have step := ih (earlier ++ [head])
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at step
    by_cases same : head = key
    · subst head
      simp [scanMemberFrom]
    · simpa [scanMemberFrom, atHead, same, Ne.symm same] using step

theorem scan_complete (entries : List JSString) (key : JSString) :
    scanMemberFrom (entries.length + 1) entries 0 key = some (decide (key ∈ entries)) := by
  simpa using scan_suffix [] entries key

/-- The standard add scan either returns the original data unchanged or appends
one new slot at the end. The source interpreter separately retains Set identity. -/
def addSteps (entries : List JSString) (key : JSString) : Option (List JSString) := do
  let found ← scanMemberFrom (entries.length + 1) entries 0 key
  return if found then entries else entries ++ [key]

theorem add_refines (entries : List JSString) (key : JSString) :
    addSteps entries key = some (StringSet.add entries key) := by
  simp [addSteps, scan_complete, StringSet.add]

structure Cursor where
  index : Nat := 0
  done : Bool := false
  deriving Repr, DecidableEq

inductive Next where
  | yield (value : JSString) (cursor : Cursor)
  | complete (cursor : Cursor)
  deriving Repr, DecidableEq

/-- One standard values-iterator step without deleted slots. Supplying the
current data again on a later call can expose intervening additions, until
completion permanently exhausts this cursor. Spread refinement below fixes
the data for its entire run; it does not assume general iterators are snapshots. -/
def next (entries : List JSString) (cursor : Cursor) : Next :=
  if cursor.done then .complete cursor
  else
    match entries[cursor.index]? with
    | none => .complete {cursor with done := true}
    | some value => .yield value ⟨cursor.index + 1, false⟩

def drain : Nat → List JSString → Cursor → Option (List JSString × Cursor)
  | 0, _, _ => none
  | fuel + 1, entries, cursor =>
    match next entries cursor with
    | .complete stopped => some ([], stopped)
    | .yield value following => do
      let (rest, stopped) ← drain fuel entries following
      return (value :: rest, stopped)

theorem drain_suffix (earlier suffix : List JSString) :
    drain (suffix.length + 1) (earlier ++ suffix) ⟨earlier.length, false⟩ =
      some (suffix, ⟨(earlier ++ suffix).length, true⟩) := by
  induction suffix generalizing earlier with
  | nil => simp [drain, next]
  | cons head tail ih =>
    have atHead : (earlier ++ head :: tail)[earlier.length]? = some head := by simp
    have step := ih (earlier ++ [head])
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at step
    rw [drain]
    simp only [next, Bool.false_eq_true, ↓reduceIte, atHead]
    change (do
      let result ← drain (tail.length + 1) (earlier ++ head :: tail) ⟨earlier.length + 1, false⟩
      pure (head :: result.1, result.2)) = _
    rw [step]
    simp [bind, pure, List.length_append]

/-- Materialization from a fresh iterator consumes all data in insertion order
and ends the iterator. This justifies compact `values` under stable iteration. -/
theorem values_refines (entries : List JSString) :
    drain (entries.length + 1) entries ⟨0, false⟩ =
      some (StringSet.values entries, ⟨entries.length, true⟩) := by
  simpa [StringSet.values] using drain_suffix [] entries

example : addSteps [[97], [98]] [97] = some [[97], [98]] := by decide
example : addSteps [[97], [98]] [99] = some [[97], [98], [99]] := by decide
example : scanMemberFrom 1 [[97], [98]] 0 [98] = none := by decide

-- A live standard iterator can see an addition before completion.
example : next [[97]] ⟨0, false⟩ = .yield [97] ⟨1, false⟩ := by decide
example : next [[97], [98]] ⟨1, false⟩ = .yield [98] ⟨2, false⟩ := by decide
example : next [[97], [98]] ⟨2, false⟩ = .complete ⟨2, true⟩ := by decide
example : next [[97], [98], [99]] ⟨2, true⟩ = .complete ⟨2, true⟩ := by decide

/-- info: 'HonoLean.Upstream.ECMA2025.StringSetSteps.add_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms add_refines

/-- info: 'HonoLean.Upstream.ECMA2025.StringSetSteps.values_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms values_refines

end HonoLean.Upstream.ECMA2025.StringSetSteps
