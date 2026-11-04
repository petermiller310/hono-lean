import HonoLean.Upstream.SourceSubset.Semantics

set_option autoImplicit false
namespace HonoLean.Upstream.ECMA2025
open SourceSubset

/-- Metadata retained for zero-capture builtin exec arrays. Numeric contents
and length belong to the CURRENT dense heap, rather than stale sidecar copies.
This is a five-property observation projection, not general Array descriptors,
prototype lookup, key enumeration, freezing or full native allocation adequacy. -/
structure RegExpMatchView where
  index : Nat
  input : JSString
  deriving Repr, DecidableEq

inductive RegExpMatchProperty where
  | zero | length | index | input | groups
  deriving Repr, DecidableEq

def observeRegExpMatch (heap : List (List Value)) (reference : Nat) (view : RegExpMatchView)
    (property : RegExpMatchProperty) : Option PropertyDescriptor := do
  let contents ← heap[reference]?
  match property with
  | .zero => contents[0]?.map (fun value => .data value true true true)
  | .length => some (.data (.number contents.length) true false false)
  | .index => some (.data (.number view.index) true true true)
  | .input => some (.data (.string view.input) true true true)
  | .groups => some (.data .undefined true true true)

theorem observeRegExpMatch_fresh (heap : List (List Value)) (input matched : JSString) (index : Nat) :
    observeRegExpMatch (heap ++ [[.string matched]]) heap.length ⟨index, input⟩ .zero = some (.data (.string matched) true true true) ∧
    observeRegExpMatch (heap ++ [[.string matched]]) heap.length ⟨index, input⟩ .length = some (.data (.number 1) true false false) ∧
    observeRegExpMatch (heap ++ [[.string matched]]) heap.length ⟨index, input⟩ .index = some (.data (.number index) true true true) ∧
    observeRegExpMatch (heap ++ [[.string matched]]) heap.length ⟨index, input⟩ .input = some (.data (.string input) true true true) ∧
    observeRegExpMatch (heap ++ [[.string matched]]) heap.length ⟨index, input⟩ .groups = some (.data .undefined true true true) := by
  simp [observeRegExpMatch]

/-- Existing arrays may change contents under ordinary source closures. The
view retains named data while length and index0 use those actual current cells. -/
theorem observeRegExpMatch_current (heap : List (List Value)) (reference : Nat) (view : RegExpMatchView) (contents : List Value)
    (found : heap[reference]? = some contents) :
    observeRegExpMatch heap reference view .length = some (.data (.number contents.length) true false false) ∧
    observeRegExpMatch heap reference view .zero = contents[0]?.map (fun value => .data value true true true) := by
  simp [observeRegExpMatch, found]

end HonoLean.Upstream.ECMA2025
