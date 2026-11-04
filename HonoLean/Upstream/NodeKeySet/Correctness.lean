import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.NodeKeySet.Generated
import HonoLean.Upstream.NodeKeySet.Contract
import HonoLean.Upstream.ECMA2025.StringSetSteps

namespace HonoLean.Upstream.NodeKeySet

open SourceSubset ECMA2025

def bindings : List String := ["Set", "possibleKeys", "pattern"]
def createProgram : List Stmt :=
  [.declare "possibleKeys" (.construct (.variable "Set") (some .string) [])]
def addExpression : Expr :=
  .call (.variable "possibleKeys") "add" [.index (.variable "pattern") (.number 1)]
def spreadExpression : Expr := .arrayLiteral [(true, .variable "possibleKeys")]

set_option maxRecDepth 32768 in
theorem parses_create : parseBlock pinnedCreateSource bindings = some createProgram := by cbv
set_option maxRecDepth 32768 in
theorem parses_add : parseExpression pinnedAddSource bindings = some addExpression := by cbv
set_option maxRecDepth 32768 in
theorem parses_spread : parseExpression pinnedSpreadSource bindings = some spreadExpression := by cbv

theorem addDelta_iff (entries : List JSString) (key : JSString) (changed : List JSString) :
    AddDelta entries key changed ↔ changed = StringSet.add entries key := by
  by_cases present : key ∈ entries <;> simp [AddDelta, StringSet.add, present]

theorem create_execution (before : State) (standard : StandardSetBinding before) (limit : Nat) :
    execute 32 limit createProgram {before with environment := withoutBindings before.environment ["possibleKeys"]} =
      .ok (.normal (createState before)) := by
  have preserved := lookup_withoutBindings before.environment ["possibleKeys"] "Set" (by decide)
  rcases standard with binding | binding <;>
    simp [createProgram, execute, evalExpression, evalArguments, lookupVariable, preserved,
      binding, createState, bind, pure, Except.bind, Except.pure]

theorem parsed_create_correct (before after : State) (standard : StandardSetBinding before) :
    (parseBlock pinnedCreateSource bindings).map (fun source => execute 32 defaultSplitLimit source
      {before with environment := withoutBindings before.environment ["possibleKeys"]}) =
      some (.ok (.normal after)) ↔ CreateContract before after := by
  rw [parses_create, Option.map_some, create_execution before standard]
  simp [CreateContract, eq_comm]

theorem add_execution (before : State) (reference patternReference limit : Nat)
    (entries : List JSString) (key : JSString)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (patternBinding : before.environment.lookup "pattern" = some (.array patternReference))
    (found : before.sets[reference]? = some entries)
    (patternRead : before.heap[patternReference]?.bind (fun elements => elements[1]?) = some (.string key)) :
    evalExpression 32 limit addExpression before =
      .ok (.set reference, {before with sets := before.sets.set reference (StringSet.add entries key)}) := by
  cases array : before.heap[patternReference]? with
  | none => simp [array] at patternRead
  | some elements =>
    simp only [array, Option.bind_some] at patternRead
    simp [addExpression, evalExpression, evalArguments, lookupVariable, binding, patternBinding,
      readProperty, array, patternRead, intrinsic, found, bind, pure, Except.bind, Except.pure]

theorem parsed_add_correct (before after : State) (returned : Value) (reference patternReference : Nat)
    (entries : List JSString) (key : JSString)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (patternBinding : before.environment.lookup "pattern" = some (.array patternReference))
    (found : before.sets[reference]? = some entries)
    (patternRead : before.heap[patternReference]?.bind (fun elements => elements[1]?) = some (.string key)) :
    (parseExpression pinnedAddSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source before) =
      some (.ok (returned, after)) ↔ AddContract before reference entries key returned after := by
  rw [parses_add, Option.map_some, add_execution before reference patternReference defaultSplitLimit entries key
    binding patternBinding found patternRead]
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, AddContract, addDelta_iff]
  constructor
  · rintro ⟨value, state⟩
    exact ⟨value.symm, _, rfl, state.symm⟩
  · rintro ⟨value, changed, equal, state⟩
    exact ⟨value.symm, by simpa only [equal] using state.symm⟩

/-- The source's compact add primitive is connected to the separately proved
indexed membership scan, rather than trusting an intrinsic desired result. -/
theorem add_source_refines_steps (before : State) (reference patternReference limit : Nat)
    (entries : List JSString) (key : JSString)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (patternBinding : before.environment.lookup "pattern" = some (.array patternReference))
    (found : before.sets[reference]? = some entries)
    (patternRead : before.heap[patternReference]?.bind (fun elements => elements[1]?) = some (.string key)) :
    ∃ changed, StringSetSteps.addSteps entries key = some changed ∧
      evalExpression 32 limit addExpression before =
        .ok (.set reference, {before with sets := before.sets.set reference changed}) :=
  ⟨_, StringSetSteps.add_refines entries key,
    add_execution before reference patternReference limit entries key binding patternBinding found patternRead⟩

theorem spread_execution (before : State) (reference limit : Nat) (entries : List JSString)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (found : before.sets[reference]? = some entries) :
    evalExpression 32 limit spreadExpression before =
      .ok (.array before.heap.length, {before with heap := before.heap ++ [entries.map Value.string]}) := by
  simp [spreadExpression, evalExpression, evalLiteralElements, lookupVariable, binding, found,
    iterableValues, StringSet.values, appendLiteralElements, bind, pure, Except.bind, Except.pure]

theorem parsed_spread_correct (before after : State) (returned : Value) (reference : Nat) (entries : List JSString)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (found : before.sets[reference]? = some entries) :
    (parseExpression pinnedSpreadSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source before) =
      some (.ok (returned, after)) ↔ SnapshotContract before entries returned after := by
  rw [parses_spread, Option.map_some, spread_execution before reference defaultSplitLimit entries binding found]
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, SnapshotContract]
  exact ⟨fun ⟨value, state⟩ => ⟨value.symm, state.symm⟩, fun ⟨value, state⟩ => ⟨value.symm, state.symm⟩⟩

theorem spread_iterator_refinement (before : State) (reference : Nat) (entries : List JSString)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (found : before.sets[reference]? = some entries) :
    ∃ values, StringSetSteps.drain (entries.length + 1) entries ⟨0, false⟩ =
        some (values, ⟨entries.length, true⟩) ∧
      evalExpression 32 defaultSplitLimit spreadExpression before =
        .ok (.array before.heap.length, {before with heap := before.heap ++ [values.map Value.string]}) :=
  ⟨entries, StringSetSteps.values_refines entries,
    spread_execution before reference defaultSplitLimit entries binding found⟩

/-- Explicit caller staging for one admitted successful string-add event.
This supplies pattern[1]; it does not execute Node.insert's traversal or derive
its pattern value. The exact pinned add expression is executed below. -/
def stagePattern (before : State) (key : JSString) : State :=
  {before with
    environment := ("pattern", .array before.heap.length) :: withoutBindings before.environment ["pattern"]
    heap := before.heap ++ [[.undefined, .string key]]}

/-- A supplied finite event trace, executing the checked source add each time.
It is deliberately a caller trace rather than an extraction of insert control
flow. Native string production and branch reachability are separate work. -/
def runSuppliedTrace : List JSString → State → Except EvalError State
  | [], before => .ok before
  | key :: rest, before => do
    let (_, after) ← evalExpression 32 defaultSplitLimit addExpression (stagePattern before key)
    runSuppliedTrace rest after

theorem stage_binding (before : State) (key : JSString) (reference : Nat)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference)) :
    (stagePattern before key).environment.lookup "possibleKeys" = some (.set reference) := by
  simp only [stagePattern, List.lookup_cons]
  rw [lookup_withoutBindings _ _ _ (by decide)]
  exact binding

theorem staged_add (before : State) (reference : Nat) (entries : List JSString) (key : JSString)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (found : before.sets[reference]? = some entries) :
    evalExpression 32 defaultSplitLimit addExpression (stagePattern before key) =
      .ok (.set reference, {stagePattern before key with sets := before.sets.set reference (StringSet.add entries key)}) := by
  exact add_execution (stagePattern before key) reference before.heap.length defaultSplitLimit entries key
    (stage_binding before key reference binding) (by simp [stagePattern]) found (by simp [stagePattern])

/-- Mathematical proof helper: the public trace theorem below exposes indexed
first-occurrence witnesses. This internal fold is not the public contract. -/
theorem trace_execution (events : List JSString) (before : State) (reference : Nat) (entries : List JSString)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (found : before.sets[reference]? = some entries) :
    ∃ after, runSuppliedTrace events before = .ok after ∧
      after.environment.lookup "possibleKeys" = some (.set reference) ∧
      after.sets[reference]? = some (events.foldl StringSet.add entries) ∧
      (∃ extra, after.heap = before.heap ++ extra) ∧
      after.objects = before.objects ∧ after.functions = before.functions ∧
      ∀ other, other ≠ reference → after.sets[other]? = before.sets[other]? := by
  induction events generalizing before entries with
  | nil =>
    exact ⟨before, rfl, binding, found, ⟨[], by simp⟩, rfl, rfl, fun _ _ => rfl⟩
  | cons key rest ih =>
    let written := {stagePattern before key with sets := before.sets.set reference (StringSet.add entries key)}
    have inside : reference < before.sets.length := (List.getElem?_eq_some_iff.mp found).1
    have nextBinding : written.environment.lookup "possibleKeys" = some (.set reference) :=
      stage_binding before key reference binding
    have nextFound : written.sets[reference]? = some (StringSet.add entries key) :=
      List.getElem?_set_self inside
    obtain ⟨after, execution, finalBinding, finalFound, ⟨extra, arrays⟩, objects, functions, otherSets⟩ :=
      ih written (StringSet.add entries key) nextBinding nextFound
    refine ⟨after, ?_, finalBinding, finalFound, ?_, objects, functions, ?_⟩
    · simp only [runSuppliedTrace, staged_add before reference entries key binding found, bind, Except.bind]
      exact execution
    · refine ⟨[ [.undefined, .string key] ] ++ extra, ?_⟩
      simpa only [written, stagePattern, List.append_assoc] using arrays
    · intro other different
      rw [otherSets other different]
      exact List.getElem?_set_ne different.symm

/-- From the created state, any supplied successful primitive-string add events
yield coverage, uniqueness and first-occurrence order. Creation itself is
connected to the exact parsed snippet by parsed_create_correct. -/
theorem created_trace_satisfies (before : State) (events : List JSString) :
    ∃ after, runSuppliedTrace events (createState before) = .ok after ∧
      after.environment.lookup "possibleKeys" = some (.set before.sets.length) ∧
      TraceContract events before.sets.length after ∧
      (∃ extra, after.heap = before.heap ++ extra) := by
  obtain ⟨after, execution, binding, found, arrays, _⟩ := trace_execution events (createState before)
    before.sets.length [] (by simp [createState]) (by simp [createState])
  exact ⟨after, execution, binding, ⟨StringSet.fromTrace events, found, StringSet.fromTrace_ordered events⟩, arrays⟩

/-- Every pre-existing dense array remains the same snapshot across later
supplied adds. Set aliases mutate one Set cell; arrays never retain that cell. -/
theorem trace_preserves_array (events : List JSString) (before : State) (reference : Nat)
    (entries : List JSString) (array : Nat) (snapshot : List Value)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (found : before.sets[reference]? = some entries) (observed : before.heap[array]? = some snapshot) :
    ∃ after, runSuppliedTrace events before = .ok after ∧ after.heap[array]? = some snapshot := by
  obtain ⟨after, execution, _, _, ⟨extra, arrays⟩, _⟩ := trace_execution events before reference entries binding found
  refine ⟨after, execution, ?_⟩
  rw [arrays, List.getElem?_append_left (List.getElem?_eq_some_iff.mp observed).1]
  exact observed

/-- Materialization turns the produced ordered Set entries into a fresh array
with unique string elements. Constructor/add/iterator lookup adequacy is an
explicit native interpretation obligation, not a theorem about all JS realms. -/
theorem trace_snapshot_satisfies (events : List JSString) (before : State) (reference : Nat)
    (binding : before.environment.lookup "possibleKeys" = some (.set reference))
    (trace : TraceContract events reference before) :
    ∃ keys after, StringSet.OrderedFirstOccurrences events keys ∧
      (parseExpression pinnedSpreadSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source before) =
        some (.ok (.array before.heap.length, after)) ∧
      SnapshotContract before keys (.array before.heap.length) after ∧
      after.heap[before.heap.length]? = some (keys.map Value.string) := by
  obtain ⟨keys, found, ordered⟩ := trace
  let after := {before with heap := before.heap ++ [keys.map Value.string]}
  refine ⟨keys, after, ordered, ?_, ⟨rfl, rfl⟩, ?_⟩
  · rw [parses_spread, Option.map_some, spread_execution before reference defaultSplitLimit keys binding found]
  · simp [after]

/-- Source-connected endpoints for all three snippets. The only connecting
control flow here is a caller-supplied finite sequence of string events; this
does not claim the noncontiguous snippets execute on every Node.insert path. -/
theorem source_sequence_satisfies (before : State) (events : List JSString)
    (standard : StandardSetBinding before) :
    ∃ created after keys snapshot,
      (parseBlock pinnedCreateSource bindings).map (fun source => execute 32 defaultSplitLimit source
        {before with environment := withoutBindings before.environment ["possibleKeys"]}) =
          some (.ok (.normal created)) ∧
      runSuppliedTrace events created = .ok after ∧
      StringSet.OrderedFirstOccurrences events keys ∧
      (parseExpression pinnedSpreadSource bindings).map (fun source => evalExpression 32 defaultSplitLimit source after) =
        some (.ok (.array after.heap.length, snapshot)) ∧
      SnapshotContract after keys (.array after.heap.length) snapshot ∧
      snapshot.heap[after.heap.length]? = some (keys.map Value.string) := by
  obtain ⟨after, execution, binding, trace, _⟩ := created_trace_satisfies before events
  obtain ⟨keys, snapshot, ordered, materialized, contract, found⟩ :=
    trace_snapshot_satisfies events after before.sets.length binding trace
  refine ⟨createState before, after, keys, snapshot, ?_, execution, ordered, materialized, contract, found⟩
  rw [parses_create, Option.map_some, create_execution before standard]

/-- info: 'HonoLean.Upstream.NodeKeySet.source_sequence_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_sequence_satisfies

end HonoLean.Upstream.NodeKeySet
