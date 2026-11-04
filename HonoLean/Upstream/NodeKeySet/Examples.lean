import HonoLean.Upstream.NodeKeySet.Correctness

namespace HonoLean.Upstream.NodeKeySet.Examples

open SourceSubset ECMA2025

set_option maxRecDepth 65536

/-- Primitive strings include the empty string, individual surrogate units and
astral pairs. Canonically equivalent Unicode spellings remain different keys. -/
def events : List JSString :=
  [[], [97], [], [0xD83D, 0xDE00], [0xD800], [0xD83D, 0xDE00], [233], [101, 769], [0xD800], [0]]

def expected : List JSString :=
  [[], [97], [0xD83D, 0xDE00], [0xD800], [233], [101, 769], [0]]

def initial : State :=
  {environment := [("Set", .setConstructor), ("possibleKeys", .set 0), ("pattern", .null)]
   heap := [[.string [111]]]
   sets := [[[111]]]}

-- Creation allocates Set1, frames the previous Set0 and replaces the local
-- possibleKeys binding; the explicit standard-constructor premise is inhabited.
example : StandardSetBinding initial := .inr (by cbv)
example : (parseBlock pinnedCreateSource bindings).map (fun source => execute 32 defaultSplitLimit source
    {initial with environment := withoutBindings initial.environment ["possibleKeys"]}) =
      some (.ok (.normal (createState initial))) := by
  rw [parses_create, Option.map_some, create_execution initial (.inr (by cbv))]
example : (createState initial).sets[0]? = some [[111]] ∧
    (createState initial).sets[1]? = some [] := by cbv

-- Closed evaluation of the actual add expression for ten supplied events.
-- The extractor/checker/parse equation, not a handwritten add implementation,
-- links the executed AST to pinned Node line51.
example : (runSuppliedTrace events (createState initial)).map (fun state => state.sets[1]?) =
    .ok (some expected) := by cbv

-- Independently witnessed first positions are [0,1,3,4,6,7,9]. Empty strings
-- are real keys, never a tombstone/sentinel; exact UTF-16 equality is retained.
private theorem first_of_take (input : List JSString) (key : JSString) (index : Nat)
    (read : input[index]? = some key) (absent : key ∉ input.take index) :
    StringSet.FirstOccurrence input key index := by
  refine ⟨read, ?_⟩
  intro earlier bound equal
  apply absent
  apply List.mem_of_getElem?
  rw [List.getElem?_take_of_lt bound]
  exact equal

example : StringSet.FirstMatches events [0, 1, 3, 4, 6, 7, 9] expected := by
  repeat' apply StringSet.FirstMatches.cons
  all_goals first | exact .nil | exact first_of_take _ _ _ (by decide) (by decide)

example : StringSet.OrderedFirstOccurrences events expected := by
  have computed : StringSet.fromTrace events = expected := by decide
  simpa only [computed] using StringSet.fromTrace_ordered events

-- The universal source theorem has an inhabited nonempty entry. It proves
-- existence/normal completion and the independent endpoint, not just a closed
-- reduction with an assumed desired result.
example : ∃ created after keys snapshot,
    (parseBlock pinnedCreateSource bindings).map (fun source => execute 32 defaultSplitLimit source
      {initial with environment := withoutBindings initial.environment ["possibleKeys"]}) =
        some (.ok (.normal created)) ∧
    runSuppliedTrace events created = .ok after ∧
    StringSet.OrderedFirstOccurrences events keys ∧
    (parseExpression pinnedSpreadSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source after) =
      some (.ok (.array after.heap.length, snapshot)) ∧
    SnapshotContract after keys (.array after.heap.length) snapshot ∧
    snapshot.heap[after.heap.length]? = some (keys.map Value.string) :=
  source_sequence_satisfies initial events (.inr (by cbv))

-- Zero admitted events still yield a fresh empty Set and a fresh empty array.
example : ∃ after, runSuppliedTrace [] (createState initial) = .ok after ∧
    after.environment.lookup "possibleKeys" = some (.set initial.sets.length) ∧
    TraceContract [] initial.sets.length after ∧ (∃ extra, after.heap = initial.heap ++ extra) :=
  created_trace_satisfies initial []

def aliases : State :=
  {environment := [("possibleKeys", .set 0), ("alias", .set 0)]
   heap := [[.string [111]]]
   sets := [[[97]]]}

def firstSnapshot : State := {aliases with heap := aliases.heap ++ [[.string [97]]]}
def afterAdd : State :=
  {stagePattern firstSnapshot [98] with sets := [[[97], [98]]]}

example : (parseExpression pinnedSpreadSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source aliases) =
    some (.ok (.array 1, firstSnapshot)) := by cbv

-- Add returns the same Set reference, including through an alias; previous
-- array1 remains [a], and later materialization produces new array3 [a,b].
example : (parseExpression pinnedAddSource bindings).map
    (fun source => evalExpression 32 defaultSplitLimit source (stagePattern firstSnapshot [98])) =
      some (.ok (.set 0, afterAdd)) := by cbv
example : afterAdd.environment.lookup "alias" = some (.set 0) ∧
    afterAdd.sets[0]? = some [[97], [98]] ∧ afterAdd.heap[1]? = some [.string [97]] := by cbv
example : (parseExpression pinnedSpreadSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source afterAdd) =
    some (.ok (.array 3, {afterAdd with heap := afterAdd.heap ++ [[.string [97], .string [98]]]})) := by cbv

-- A quantified later trace frames the first snapshot, not just one addition.
example (later : List JSString) :
    ∃ after, runSuppliedTrace later firstSnapshot = .ok after ∧ after.heap[1]? = some [.string [97]] :=
  trace_preserves_array later firstSnapshot 0 [[97]] 1 [.string [97]]
    (by cbv) (by cbv) (by cbv)

-- Source mutations distinguish necessary deduplication and event selection.
example : (parseExpression "possibleKeys.add(pattern[0])" bindings).map
    (fun source => evalExpression 32 defaultSplitLimit source (stagePattern aliases [98])) =
      some (.error .unsupported) := by cbv
example : StringSet.OrderedFirstOccurrences [[97], [97]] [[97], [97]] → False := by
  intro invalid
  have duplicate : ¬ ([[97], [97]] : List JSString).Nodup := by decide
  exact duplicate invalid.1

end HonoLean.Upstream.NodeKeySet.Examples
