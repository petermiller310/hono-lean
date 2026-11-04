import HonoLean.Adapter
import Lean.Data.Json

namespace HonoLean.Adapter
open Literal Lean

def field (kind : ErrorKind) (value : Json) (name : String) : Except Error Json :=
  (value.getObjVal? name).mapError (fun message => ⟨kind, message⟩)

def stringField (kind : ErrorKind) (value : Json) (name : String) : Except Error String := do
  let text ← field kind value name
  text.getStr?.mapError (fun message => ⟨kind, name ++ ": " ++ message⟩)

def arrayField (kind : ErrorKind) (value : Json) (name : String) : Except Error (Array Json) := do
  let array ← field kind value name
  array.getArr?.mapError (fun message => ⟨kind, name ++ ": " ++ message⟩)

def decodeRoute (value : Json) : Except Error TextRoute := do
  let method ← stringField .invalidRoute value "method"
  let pattern ← stringField .invalidRoute value "pattern"
  let handler ← stringField .invalidRoute value "handler"
  return ⟨method, pattern, handler⟩

def decodeRequest (value : Json) : Except Error TextRequest := do
  let method ← stringField .invalidRequest value "method"
  let path ← stringField .invalidRequest value "path"
  return ⟨method, path⟩

def errorJson (error : Error) : Json := Json.mkObj [
  ("error", Json.mkObj [("category", toJson error.kind.category), ("message", toJson error.message)])]

def matchesJson (items : List Match) : Json :=
  toJson (items.map (fun item => Json.mkObj [
    ("registration", toJson item.registration), ("handler", toJson item.handler),
    ("params", Json.mkObj (item.params.map (fun (name, value) => (name, toJson value))))]))

def buildJson (inputs : Json) : Except Error Router := do
  let array ← inputs.getArr?.mapError (fun message => ⟨.invalidRoute, message⟩)
  build (← array.toList.mapM decodeRoute)

def registerJson (router : Router) (input : Json) : Except Error Router := do
  register router (← decodeRoute input)

def lookupJson (router : Router) (input : Json) : Except Error Json := do
  return matchesJson (← lookup router (← decodeRequest input))

/-- A failed step returns its error and the exact input router. -/
def runStep (router : Router) (step : Json) : Router × Json :=
  let result : Except Error (Router × Json) := do
    match ← stringField .invalidInput step "op" with
    | "register" =>
      let route ← decodeRoute (← field .invalidRoute step "route")
      let (updated, outcome) := registerStep router route
      let registration ← outcome
      return (updated, Json.mkObj [("registration", toJson registration)])
    | "lookup" =>
      let items ← lookupJson router (← field .invalidRequest step "request")
      return (router, Json.mkObj [("matches", items)])
    | _ => .error ⟨.invalidInput, "Expected lookup or register operation"⟩
  match result with
  | .ok value => value
  | .error error => (router, errorJson error)

def runScenario (input : Json) : Except Error Json := do
  let _ ← input.getObj?.mapError (fun message => ⟨.invalidInput, message⟩)
  let steps ← arrayField .invalidInput input "steps"
  let router ← buildJson (← field .invalidRoute input "routes")
  let (final, results) := steps.foldl (fun (router, results) step =>
    let (updated, result) := runStep router step
    (updated, results.push result)) (router, #[])
  return Json.mkObj [("results", .arr results), ("nextRegistration", toJson final.nextOrdinal)]

def runDocument (text : String) : Json :=
  match Json.parse text with
  | .error message => errorJson ⟨.invalidInput, message⟩
  | .ok input =>
    match runScenario input with
    | .ok output => output
    | .error error => errorJson error

end HonoLean.Adapter
