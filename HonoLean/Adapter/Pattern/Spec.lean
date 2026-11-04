import HonoLean.Adapter.Path.Spec

namespace HonoLean.Adapter.PatternText
open Literal

def NameStart (c : Char) : Prop :=
  c = '_' ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')

def Name (text : String) : Prop :=
  match text.toList with
  | [] => False
  | first :: rest => NameStart first ∧
      ∀ c ∈ rest, NameStart c ∨ ('0' ≤ c ∧ c ≤ '9')

/-- Literal and parameter spellings use different alphabets; neither is normalized. -/
def ComponentText (text : String) : Component → Prop
  | .literal segment => text = segment ∧ PathText.Segment segment
  | .parameter name => text = ":" ++ name ∧ Name name

/-- A declarative grammar for a sequence of whole component spellings.
The wildcard has one production, at the end, and adds no component. -/
inductive Pieces : List String → List Component → Bool → Prop where
  | exact : Pieces [] [] false
  | wildcard : Pieces ["*"] [] true
  | component (head : ComponentText text item) (tail : Pieces texts items suffix) :
      Pieces (text :: texts) (item :: items) suffix

/-- Slash spelling is exact; bare `*` is the one non-slash alias. -/
def Spelling (text : String) (components : List Component) (suffix : Bool) : Prop :=
  ∃ texts, Pieces texts components suffix ∧
    (text = "/" ++ "/".intercalate texts ∨
      (text = "*" ∧ texts = ["*"]))

/-- Parameter names are unique within one route, not across the table. -/
def Denotes (text : String) (components : List Component) (suffix : Bool) : Prop :=
  Spelling text components suffix ∧ (parameterNames components).Nodup

end HonoLean.Adapter.PatternText
