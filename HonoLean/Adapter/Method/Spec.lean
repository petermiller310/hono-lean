import HonoLean.Adapter

namespace HonoLean.Adapter.MethodText

/-- The specification's method alphabet, independently of the executable check. -/
def Character (c : Char) : Prop :=
  'A' ≤ c ∧ c ≤ 'Z'

/-- One or more uppercase ASCII letters, excluding the reserved route selector.
This grammar calls neither `parseMethod` nor `Literal.ValidMethod`. -/
def Spelling (text : String) : Prop :=
  text.toList ≠ [] ∧ (∀ c ∈ text.toList, Character c) ∧ text ≠ "ALL"

/-- A parsed method has the grammar's exact spelling, with no normalization. -/
def Denotes (text : String) (method : Literal.Method) : Prop :=
  Spelling text ∧ method.name = text

end HonoLean.Adapter.MethodText
