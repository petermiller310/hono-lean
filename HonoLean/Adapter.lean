import HonoLean.Router

namespace HonoLean.Adapter
open Literal

inductive ErrorKind where
  | invalidRoute | invalidRequest | invalidInput
  deriving Repr, DecidableEq

def ErrorKind.category : ErrorKind → String
  | .invalidRoute => "invalid_route"
  | .invalidRequest => "invalid_request"
  | .invalidInput => "invalid_input"

structure Error where
  kind : ErrorKind
  message : String
  deriving Repr

structure TextRoute where
  method : String
  pattern : String
  handler : String
  deriving Repr

structure TextRequest where
  method : String
  path : String
  deriving Repr

def parseMethod (kind : ErrorKind) (text : String) : Except Error Method :=
  if valid : ValidMethod text then pure ⟨text, valid⟩
  else .error ⟨kind, "Expected uppercase ASCII method other than ALL"⟩

def validSegment (text : String) : Bool :=
  !text.isEmpty && text.toList.all (fun c =>
    nameStart c || ('0' ≤ c && c ≤ '9') || c == '-')

/-- Split only; never trim, decode, case-fold, or repair path text. -/
def rootedPieces (kind : ErrorKind) (text : String) : Except Error (List String) :=
  if text == "/" then pure []
  else match (text.split '/').toList.map (·.copy) with
    | "" :: pieces =>
      if !pieces.isEmpty && pieces.all (fun piece => !piece.isEmpty) then pure pieces
      else .error ⟨kind, "Empty or trailing path segment"⟩
    | _ => .error ⟨kind, "Expected an absolute slash path"⟩

/-- Request-only splitting uses the standard character splitter, whose inverse
laws let the proof connect the result to the independent text grammar. -/
def parsePath (text : String) : Except Error Path :=
  if text == "/" then .ok []
  else match (text.split '/').toList.map (·.copy) with
    | "" :: pieces =>
      if !pieces.isEmpty && pieces.all validSegment then .ok pieces
      else .error ⟨.invalidRequest, "Empty or unsupported request path segment"⟩
    | _ => .error ⟨.invalidRequest, "Expected an absolute slash path"⟩

def parseComponent (text : String) : Except Error Component :=
  match text.toList with
  | ':' :: rest =>
    let name := String.ofList rest
    if validName name then pure (.parameter name)
    else .error ⟨.invalidRoute, "Invalid parameter name"⟩
  | _ =>
    if validSegment text then pure (.literal text)
    else .error ⟨.invalidRoute, "Unsupported route component"⟩

structure ParsedPattern where
  path : List Component
  suffix : Bool
  valid : ValidPattern path
  deriving Repr

/-- A wildcard is accepted only as the sole remaining whole component. -/
def parsePatternPieces : List String → Except Error (List Component × Bool)
  | [] => .ok ([], false)
  | text :: rest =>
    if text == "*" && rest.isEmpty then .ok ([], true)
    else do
      let component ← parseComponent text
      let (components, suffix) ← parsePatternPieces rest
      return (component :: components, suffix)

def patternTexts (text : String) : Except Error (List String) :=
  if text == "*" then .ok ["*"] else rootedPieces .invalidRoute text

def parsePattern (text : String) : Except Error ParsedPattern := do
  let pieces ← patternTexts text
  let (components, suffix) ← parsePatternPieces pieces
  if valid : ValidPattern components then
    pure ⟨components, suffix, valid⟩
  else .error ⟨.invalidRoute, "Parameter names must be valid and unique"⟩

def parseRoute (input : TextRoute) : Except Error Literal.Route := do
  let selector ← if input.method == "ALL" then pure Selector.all
    else do pure (Selector.exact (← parseMethod .invalidRoute input.method))
  let pattern ← parsePattern input.pattern
  return {selector, path := pattern.path, suffix := pattern.suffix, handler := input.handler, valid := pattern.valid}

def parseRequest (input : TextRequest) : Except Error (Method × Path) := do
  return (← parseMethod .invalidRequest input.method, ← parsePath input.path)

def build (inputs : List TextRoute) : Except Error Router := do
  return Router.build (← inputs.mapM parseRoute)

def register (router : Router) (input : TextRoute) : Except Error Router := do
  return Router.register router (← parseRoute input)

/-- A total registration step: rejection retains the exact prior router. -/
def registerStep (router : Router) (input : TextRoute) : Router × Except Error Nat :=
  match register router input with
  | .ok updated => (updated, .ok router.nextOrdinal)
  | .error error => (router, .error error)

def lookup (router : Router) (input : TextRequest) : Except Error (List Match) := do
  let (method, path) ← parseRequest input
  return Router.lookup router method path

end HonoLean.Adapter
