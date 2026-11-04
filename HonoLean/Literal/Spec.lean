import HonoLean.Literal

namespace HonoLean.Literal

abbrev ValidMethod (name : String) : Prop :=
  name ≠ "" ∧ name.toList.all (fun c => 'A' ≤ c && c ≤ 'Z') = true ∧ name ≠ "ALL"

structure Method where
  name : String
  valid : ValidMethod name
  deriving Repr

inductive Selector where
  | all
  | exact (method : Method)
  deriving Repr

def Accepts (selector : Selector) (requestMethod : Method) : Prop :=
  match selector with
  | .all => True
  | .exact method => method.name = requestMethod.name

instance (selector : Selector) (requestMethod : Method) : Decidable (Accepts selector requestMethod) :=
  match selector with
  | .all => isTrue True.intro
  | .exact method => inferInstanceAs (Decidable (method.name = requestMethod.name))

inductive Component where
  | literal (text : String)
  | parameter (name : String)
  deriving Repr, DecidableEq

abbrev Params := List (String × String)

def nameStart (c : Char) : Bool :=
  c == '_' || ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

def validName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => nameStart first && rest.all (fun c => nameStart c || ('0' ≤ c && c ≤ '9'))

def parameterNames (pattern : List Component) : List String :=
  pattern.filterMap (fun component => match component with
    | .literal _ => none
    | .parameter name => some name)

abbrev ValidPattern (pattern : List Component) : Prop :=
  (parameterNames pattern).all validName = true ∧ (parameterNames pattern).Nodup

structure Route where
  selector : Selector
  path : List Component
  /-- Accept any remaining suffix after the prefix; this adds no capture. -/
  suffix : Bool := false
  handler : String
  valid : ValidPattern path
  deriving Repr

theorem parameterNames_literals (path : Path) : parameterNames (path.map Component.literal) = [] := by
  induction path with
  | nil => rfl
  | cons segment rest ih => simp [parameterNames, List.filterMap_map]

def literalRoute (selector : Selector) (path : Path) (handler : String) : Route :=
  {selector, path := path.map Component.literal, handler,
   valid := by simp [ValidPattern, parameterNames_literals]}

structure Match where
  registration : Nat
  handler : String
  params : Params := []
  deriving Repr, DecidableEq

def result (registration : Nat) (route : Route) (params : Params) : Match :=
  {registration, handler := route.handler, params}

/-- One component consumes one segment; a parameter requires nonempty text. -/
def consume (component : Component) (segment : String) : Option Params :=
  match component with
  | .literal text => if text = segment then some [] else none
  | .parameter name => if segment ≠ "" then some [(name, segment)] else none

def capture (pattern : List Component) (suffix : Bool) (path : Path) : Option Params :=
  match pattern, path with
  | [], [] => some []
  | [], _ :: _ => if suffix then some [] else none
  | component :: rest, segment :: remaining =>
    (consume component segment).bind (fun bindings =>
      (capture rest suffix remaining).map (bindings ++ ·))
  | _, _ => none

/-- Declarative capture rules, independent of either route-table traversal. -/
inductive Captures : List Component → Bool → Path → Params → Prop where
  | nil : Captures [] false [] []
  | suffix : Captures [] true remaining []
  | literal {text segment rest remaining params}
      (same : text = segment) (tail : Captures rest suffix remaining params) :
      Captures (.literal text :: rest) suffix (segment :: remaining) params
  | parameter {name segment rest remaining params}
      (nonempty : segment ≠ "") (tail : Captures rest suffix remaining params) :
      Captures (.parameter name :: rest) suffix (segment :: remaining) ((name, segment) :: params)

def routeCapture (route : Route) (method : Method) (path : Path) : Option Params :=
  if Accepts route.selector method then capture route.path route.suffix path else none

inductive Matches : Nat → List Route → Method → Path → List Match → Prop where
  | nil (start : Nat) (method : Method) (path : Path) : Matches start [] method path []
  | hit {start route rest method path params output}
      (accepted : Accepts route.selector method) (captured : Captures route.path route.suffix path params)
      (tail : Matches (start + 1) rest method path output) :
      Matches start (route :: rest) method path (result start route params :: output)
  | miss {start route rest method path output}
      (different : ¬ ∃ params, Accepts route.selector method ∧ Captures route.path route.suffix path params)
      (tail : Matches (start + 1) rest method path output) :
      Matches start (route :: rest) method path output

end HonoLean.Literal
