import Std

namespace HonoLean

/-- An already-parsed literal path. The root path is the empty list. -/
abbrev Path := List String

structure Route where
  path : Path
  handler : String
  deriving Repr

/-- Collect exact path matches in registration order. -/
def lookup (routes : List Route) (requestPath : Path) : List String :=
  match routes with
  | [] => []
  | route :: rest =>
    if route.path == requestPath then
      route.handler :: lookup rest requestPath
    else
      lookup rest requestPath

theorem lookup_singleton_self (route : Route) :
    lookup [route] route.path = [route.handler] := by
  simp [lookup]

#print axioms lookup_singleton_self

end HonoLean
