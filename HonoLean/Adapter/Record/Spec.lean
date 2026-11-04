import HonoLean.Adapter.Method.Spec
import HonoLean.Adapter.Pattern.Spec

namespace HonoLean.Adapter.RecordText
open Literal

/-- ALL is a route selector; exact selectors retain one supported method name. -/
def SelectorDenotes (text : String) : Selector → Prop
  | .all => text = "ALL"
  | .exact method => MethodText.Denotes text method

/-- Record meaning is the conjunction of the independent field contracts. -/
def RouteDenotes (input : TextRoute) (route : Literal.Route) : Prop :=
  SelectorDenotes input.method route.selector ∧
    PatternText.Denotes input.pattern route.path route.suffix ∧
    route.handler = input.handler

def RequestDenotes (input : TextRequest) (request : Method × HonoLean.Path) : Prop :=
  MethodText.Denotes input.method request.1 ∧ PathText.Denotes input.path request.2

/-- Valid text records are specified without preconstructing a typed result. -/
def RouteSpelling (input : TextRoute) : Prop :=
  (input.method = "ALL" ∨ MethodText.Spelling input.method) ∧
    ∃ components suffix, PatternText.Denotes input.pattern components suffix

def RequestSpelling (input : TextRequest) : Prop :=
  MethodText.Spelling input.method ∧ ∃ path, PathText.Denotes input.path path

end HonoLean.Adapter.RecordText
