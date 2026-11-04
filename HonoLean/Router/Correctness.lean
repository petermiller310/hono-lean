import HonoLean.Router
import HonoLean.Literal.Correctness

namespace HonoLean.Literal

namespace Trie

theorem buildFrom_append (before after : List Route) (start : Nat) (tree : Trie) :
    buildFrom (before ++ after) start tree =
      buildFrom after (start + before.length) (buildFrom before start tree) := by
  induction before generalizing start tree with
  | nil => simp [buildFrom]
  | cons route rest ih =>
    simpa [buildFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (start + 1) (insert tree route.path route.suffix (entryOf start route))

theorem build_append_singleton (routes : List Route) (route : Route) :
    build (routes ++ [route]) =
      insert (build routes) route.path route.suffix (entryOf routes.length route) := by
  simpa [build, buildFrom] using buildFrom_append routes [route] 0 empty

end Trie

namespace Router

/-- A proof-only description of the table represented by the runtime state. -/
def Represents (router : Router) (routes : List Route) : Prop :=
  router.tree = Trie.build routes ∧ router.nextOrdinal = routes.length

theorem build_represents (routes : List Route) : Represents (build routes) routes :=
  ⟨rfl, rfl⟩

theorem empty_represents : Represents empty [] := build_represents []

theorem register_represents {router : Router} {routes : List Route}
    (valid : Represents router routes) (route : Route) :
    Represents (register router route) (routes ++ [route]) := by
  rcases valid with ⟨tree, next⟩
  constructor
  · simpa [register, tree, next] using (Trie.build_append_singleton routes route).symm
  · simp [register, next]

theorem registerMany_represents {router : Router} {routes : List Route}
    (valid : Represents router routes) (added : List Route) :
    Represents (registerMany router added) (routes ++ added) := by
  induction added generalizing router routes with
  | nil => simpa [registerMany] using valid
  | cons route rest ih =>
    simpa [registerMany, List.append_assoc] using ih (register_represents valid route)

theorem lookup_eq_reference {router : Router} {routes : List Route}
    (valid : Represents router routes) (method : Method) (path : Path) :
    lookup router method path = referenceLookup routes method path := by
  rw [lookup, valid.1, Trie.lookup_build]

theorem lookup_iff_rules {router : Router} {routes : List Route}
    (valid : Represents router routes) (method : Method) (path : Path) (output : List Match) :
    lookup router method path = output ↔ Matches 0 routes method path output := by
  rw [lookup, valid.1, Trie.lookup_build_iff_rules]

theorem lookup_register {router : Router} {routes : List Route}
    (valid : Represents router routes) (route : Route) (method : Method) (path : Path) :
    lookup (register router route) method path = referenceLookup (routes ++ [route]) method path :=
  lookup_eq_reference (register_represents valid route) method path

theorem lookup_registerMany {router : Router} {routes : List Route}
    (valid : Represents router routes) (added : List Route) (method : Method) (path : Path) :
    lookup (registerMany router added) method path = referenceLookup (routes ++ added) method path :=
  lookup_eq_reference (registerMany_represents valid added) method path

theorem lookup_registerMany_build (initial added : List Route) (method : Method) (path : Path) :
    lookup (registerMany (build initial) added) method path =
      referenceLookup (initial ++ added) method path :=
  lookup_registerMany (build_represents initial) added method path

theorem lookup_registerMany_build_iff_rules (initial added : List Route) (method : Method)
    (path : Path) (output : List Match) :
    lookup (registerMany (build initial) added) method path = output ↔
      Matches 0 (initial ++ added) method path output :=
  lookup_iff_rules (registerMany_represents (build_represents initial) added) method path output

/-- info: 'HonoLean.Literal.Router.register_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms register_represents

/-- info: 'HonoLean.Literal.Router.lookup_registerMany_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_registerMany_build

/-- info: 'HonoLean.Literal.Router.lookup_registerMany_build_iff_rules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_registerMany_build_iff_rules

end Router
end HonoLean.Literal
