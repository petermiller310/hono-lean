import HonoLean.Adapter.Build.Spec

namespace HonoLean.Adapter.LookupText

/-- Text-level matching means exactly the ordered core rules applied to the
independent meanings of the route table and request. No parser or lookup runs
inside this specification. -/
def Matches (inputs : List TextRoute) (request : TextRequest)
    (output : List Literal.Match) : Prop :=
  ∃ routes decoded, BuildText.TableDenotes inputs routes ∧
    RecordText.RequestDenotes request decoded ∧
    Literal.Matches 0 routes decoded.1 decoded.2 output

end HonoLean.Adapter.LookupText
