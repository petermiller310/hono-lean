import HonoLean.Literal.Spec

namespace HonoLean.Literal

structure Entry where
  selector : Selector
  registration : Nat
  handler : String
  deriving Repr

def entryMatch (entry : Entry) (params : Params) : Match :=
  {registration := entry.registration, handler := entry.handler, params}

def entryOf (registration : Nat) (route : Route) : Entry :=
  {selector := route.selector, registration, handler := route.handler}

def prefixMatch (bindings : Params) (value : Match) : Match :=
  {value with params := bindings ++ value.params}

def select (entries : List Entry) (method : Method) : List Match :=
  entries.filterMap (fun entry => if Accepts entry.selector method then some (entryMatch entry []) else none)

def entryResults (entry : Entry) (pattern : List Component) (suffix : Bool) (method : Method) (path : Path) : List Match :=
  if Accepts entry.selector method then
    (capture pattern suffix path).toList.map (entryMatch entry)
  else []

/-- A finite prefix tree with literal and name-keyed parameter branches. -/
inductive Trie where
  | node (terminal wildcard : List Entry) (children : List (Component × Trie))
  deriving Repr

namespace Trie

def empty : Trie := .node [] [] []

def alterChild (children : List (Component × Trie)) (key : Component)
    (change : Trie → Trie) : List (Component × Trie) :=
  match children with
  | [] => [(key, change empty)]
  | (label, tree) :: rest =>
    if label = key then (label, change tree) :: rest
    else (label, tree) :: alterChild rest key change

def insert (tree : Trie) (pattern : List Component) (suffix : Bool) (entry : Entry) : Trie :=
  match tree, pattern with
  | .node terminal wildcard children, [] =>
    if suffix then .node terminal (wildcard ++ [entry]) children
    else .node (terminal ++ [entry]) wildcard children
  | .node terminal wildcard children, component :: rest =>
    .node terminal wildcard (alterChild children component (fun subtree => insert subtree rest suffix entry))
termination_by structural pattern

def candidates (tree : Trie) (method : Method) (path : Path) : List Match :=
  match tree, path with
  | .node terminal wildcard _, [] => select wildcard method ++ select terminal method
  | .node _ wildcard children, segment :: remaining =>
    select wildcard method ++ children.flatMap (fun (component, subtree) =>
      match consume component segment with
      | none => []
      | some bindings => (candidates subtree method remaining).map (prefixMatch bindings))
termination_by structural path

def branch (component : Component) (tree : Trie) (method : Method)
    (segment : String) (remaining : Path) : List Match :=
  match consume component segment with
  | none => []
  | some bindings => (candidates tree method remaining).map (prefixMatch bindings)

def byRegistration (left right : Match) : Bool := decide (left.registration ≤ right.registration)

def lookup (tree : Trie) (method : Method) (path : Path) : List Match :=
  (candidates tree method path).mergeSort byRegistration

def buildFrom (routes : List Route) (next : Nat) (tree : Trie) : Trie :=
  match routes with
  | [] => tree
  | route :: rest => buildFrom rest (next + 1) (insert tree route.path route.suffix (entryOf next route))

def build (routes : List Route) : Trie := buildFrom routes 0 empty

end Trie
end HonoLean.Literal
