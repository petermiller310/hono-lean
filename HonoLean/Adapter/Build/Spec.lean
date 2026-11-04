import HonoLean.Adapter.Record.Spec

namespace HonoLean.Adapter.BuildText

/-- Pointwise ordered record meaning: each registration occurrence is retained. -/
inductive TableDenotes : List TextRoute → List Literal.Route → Prop where
  | nil : TableDenotes [] []
  | cons (head : RecordText.RouteDenotes input route) (tail : TableDenotes inputs routes) :
      TableDenotes (input :: inputs) (route :: routes)

/-- The input grammar is independent of parsing or router construction. -/
def TableSpelling (inputs : List TextRoute) : Prop :=
  ∀ input ∈ inputs, RecordText.RouteSpelling input

end HonoLean.Adapter.BuildText
