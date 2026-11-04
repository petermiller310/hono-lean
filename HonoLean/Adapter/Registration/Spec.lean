import HonoLean.Adapter.Build.Spec
import HonoLean.Router.Correctness

namespace HonoLean.Adapter.RegistrationText

/-- A text-table view of the persistent runtime router. -/
def StateDenotes (inputs : List TextRoute) (router : Literal.Router) : Prop :=
  ∃ routes, BuildText.TableDenotes inputs routes ∧ Literal.Router.Represents router routes

/-- Independent registration rules: append one valid occurrence, or retain the
whole previous table and reject an unsupported record. -/
inductive StepDenotes : List TextRoute → TextRoute → List TextRoute → Except Error Nat → Prop where
  | accepted (grammar : RecordText.RouteSpelling input) :
      StepDenotes before input (before ++ [input]) (.ok before.length)
  | rejected (outside : ¬ RecordText.RouteSpelling input) (category : error.kind = .invalidRoute) :
      StepDenotes before input before (.error error)

/-- Finite registration histories retain valid occurrences in input order and
skip rejected records. No parser or runtime traversal appears in these rules. -/
inductive TraceDenotes : List TextRoute → List TextRoute → List TextRoute → Prop where
  | nil : TraceDenotes before [] before
  | accepted (grammar : RecordText.RouteSpelling input)
      (tail : TraceDenotes (before ++ [input]) rest after) :
      TraceDenotes before (input :: rest) after
  | rejected (outside : ¬ RecordText.RouteSpelling input)
      (tail : TraceDenotes before rest after) :
      TraceDenotes before (input :: rest) after

end HonoLean.Adapter.RegistrationText
