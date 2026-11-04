import HonoLean.Literal.Trie

namespace HonoLean.Literal

/-- Persistent router state. Correct states are characterized by `Router.Represents`. -/
structure Router where
  private mk ::
  tree : Trie
  nextOrdinal : Nat
  deriving Repr

namespace Router

def build (routes : List Route) : Router :=
  ⟨Trie.build routes, routes.length⟩

def empty : Router := build []

/-- Append one registration, returning a new router and leaving the input usable. -/
def register (router : Router) (route : Route) : Router :=
  ⟨Trie.insert router.tree route.path route.suffix (entryOf router.nextOrdinal route),
    router.nextOrdinal + 1⟩

def registerMany (router : Router) (routes : List Route) : Router :=
  routes.foldl register router

def lookup (router : Router) (method : Method) (path : Path) : List Match :=
  Trie.lookup router.tree method path

end Router
end HonoLean.Literal
