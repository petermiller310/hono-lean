import HonoLean.Adapter

namespace HonoLean.Adapter.PathText

/-- The specification's alphabet, stated as propositions rather than using
the executable `validSegment` check. -/
def Character (c : Char) : Prop :=
  c = '_' ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨
    ('0' ≤ c ∧ c ≤ '9') ∨ c = '-'

/-- A segment contains one or more characters from the restricted alphabet. -/
def Segment (text : String) : Prop :=
  text ≠ "" ∧ ∀ c ∈ text.toList, Character c

/-- Canonical spelling. The empty core path is the single root slash. -/
def render (pieces : HonoLean.Path) : String :=
  "/" ++ "/".intercalate pieces

/-- Independent request-path grammar: canonical slash spelling with valid
segments. This definition never calls a parser or a splitter. -/
def Denotes (text : String) (pieces : HonoLean.Path) : Prop :=
  (∀ piece ∈ pieces, Segment piece) ∧ text = render pieces

end HonoLean.Adapter.PathText
