import HonoLean.Upstream.GetPatternLookahead.Contract
import HonoLean.Upstream.ECMA2025.LiteralLookahead.Correctness

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.GetPatternLookahead
open SourceSubset hiding pinnedSource State
open ECMA2025
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

theorem constructor_tables (before : LookaheadRegExp.State) (context : RegExpConstructContext) (handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (lower upper : UInt16) (next : JSString)
    (inputs : ConstructorInputs before context handle constructor prototypeObject lower upper next) :
    constructorTablesSeparated context before.base.base.regexp.ambient = true := by
  simp [constructorTablesSeparated, inputs.noArgBefore, inputs.methodsBefore, inputs.functionsBefore,
    inputs.membersBefore, inputs.builtinsBefore]

theorem construction_contract (before : LookaheadRegExp.State) (prototype : Nat) (lower upper : UInt16) (next : JSString)
    (coherent : LookaheadRegExp.Coherent before) :
    ConstructionContract before (LookaheadRegExp.constructedState before prototype (LookaheadRegExp.compiledRecord lower upper next))
      (.object before.base.base.regexp.ambient.objects.length) prototype lower upper next := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, LookaheadRegExp.coherent_constructed before prototype _ coherent⟩
  · simp [LookaheadRegExp.constructedState, LookaheadRegExp.withAmbient, LookaheadRegExp.withBase, cacheWithAmbient]
  · intro reference bound
    exact List.getElem?_append_left bound

theorem constructor_satisfies (before : LookaheadRegExp.State) (context : RegExpConstructContext) (handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (lower upper : UInt16) (next : JSString)
    (inputs : ConstructorInputs before context handle constructor prototypeObject lower upper next) :
    LookaheadRegExp.invokeConstructor context (.function handle) (.string (LiteralLookahead.rawSource lower upper next)) before =
      .ok (.object before.base.base.regexp.ambient.objects.length,
        LookaheadRegExp.constructedState before constructor.prototype (LookaheadRegExp.compiledRecord lower upper next)) ∧
    ConstructionContract before (LookaheadRegExp.constructedState before constructor.prototype (LookaheadRegExp.compiledRecord lower upper next))
      (.object before.base.base.regexp.ambient.objects.length) constructor.prototype lower upper next := by
  refine ⟨LookaheadRegExp.constructor_safe context before (.function handle) constructor prototypeObject lower upper next inputs.coherent
    (constructor_tables before context handle constructor prototypeObject lower upper next inputs) ?_ inputs.prototypeFound
    inputs.lowerSafe inputs.upperSafe inputs.ordered inputs.nextSafe, construction_contract before constructor.prototype lower upper next inputs.coherent⟩
  simp [constructorAt, inputs.handleBound, inputs.identity]

private theorem lookup_tag {α : Type} (entries : List (Nat × α)) (tag : α → LookaheadRegExp.TaggedRecord) (reference : Nat) :
    (entries.map (fun (reference, value) => (reference, tag value))).lookup reference = (entries.lookup reference).map tag := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    simp only [List.map_cons, List.lookup_cons, ih]
    split <;> rfl

theorem record_at_new (before : LookaheadRegExp.State) (reference : Nat) (record : LookaheadRegExp.Record)
    (found : before.records.lookup reference = some record) :
    LookaheadRegExp.recordAt before reference = some (.lookahead record) := by
  simp only [LookaheadRegExp.recordAt, LookaheadRegExp.taggedEntries, List.lookup_append]
  rw [lookup_tag before.records LookaheadRegExp.TaggedRecord.lookahead reference, found]
  rfl

theorem exec_satisfies (before : LookaheadRegExp.State) (reference : Nat) (object : OrdinaryObject) (last : Int) (writable : Bool)
    (lower upper : UInt16) (next input : JSString) (rest : List Value)
    (inputs : ExecInputs before reference object last writable lower upper next) :
    ∃ returned after,
      LookaheadRegExp.invokeExec (.object reference) (.string input :: rest) before = .ok (returned, after) ∧
      ExecContract before after returned lower upper next input := by
  have lastRead : getProperty propertyFuel before.base.base.regexp.ambient.objects reference lastIndexKey = .ok (.number last) :=
    getProperty_data _ reference (propertyFuel - 1) lastIndexKey object (.number last) writable false false inputs.objectFound inputs.lastIndex
  have record := record_at_new before reference _ inputs.record
  cases outcome : LiteralLookahead.execute (LiteralLookahead.code lower upper next) input with
  | exhausted =>
    exact False.elim ((LiteralLookahead.execute_ne_exhausted lower upper next input) outcome)
  | noMatch =>
    have absent := (LiteralLookahead.execute_noMatch_iff lower upper next input inputs.lowerSafe).mp outcome
    refine ⟨.null, before, ?_, Or.inl ⟨rfl, rfl, absent⟩⟩
    simp [LookaheadRegExp.invokeExec, LookaheadRegExp.well_formed before inputs.coherent, record, lastRead,
      numericToLength_int last inputs.safeLast, LookaheadRegExp.compiledRecord, outcome]
  | matched result =>
    have matched := (LiteralLookahead.execute_matched_iff lower upper next input result inputs.lowerSafe).mp outcome
    obtain ⟨taken, suffix, shape, nonempty, range, rfl⟩ := matched
    have span : 0 ≤ taken.length ∧ taken.length ≤ input.length := by
      rw [shape, List.length_append]
      omega
    have contents : input.take taken.length = taken := by simp [shape]
    refine ⟨.array before.base.base.regexp.ambient.heap.length, prefixState before input taken, ?_,
      Or.inr ⟨taken, suffix, shape, nonempty, range, rfl, rfl⟩⟩
    simp [LookaheadRegExp.invokeExec, LookaheadRegExp.well_formed before inputs.coherent, record, lastRead,
      numericToLength_int last inputs.safeLast, LookaheadRegExp.compiledRecord, outcome, span, materializeRegExpMatch,
      contents, prefixState, LookaheadRegExp.withBase]

theorem constructed_exec_inputs (before : LookaheadRegExp.State) (context : RegExpConstructContext) (handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (lower upper : UInt16) (next : JSString)
    (inputs : ConstructorInputs before context handle constructor prototypeObject lower upper next) :
    ExecInputs (LookaheadRegExp.constructedState before constructor.prototype (LookaheadRegExp.compiledRecord lower upper next))
      before.base.base.regexp.ambient.objects.length (initializedRegExpObject constructor.prototype) 0 true lower upper next := by
  refine ⟨LookaheadRegExp.coherent_constructed before constructor.prototype _ inputs.coherent, ?_, ?_, rfl, by decide,
    inputs.lowerSafe, inputs.upperSafe, inputs.ordered, inputs.nextSafe⟩
  · simp [LookaheadRegExp.constructedState]
  · exact (construction_contract before constructor.prototype lower upper next inputs.coherent).object

theorem constructor_then_exec_satisfies (before : LookaheadRegExp.State) (context : RegExpConstructContext) (handle : Nat)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (lower upper : UInt16) (next input : JSString)
    (inputs : ConstructorInputs before context handle constructor prototypeObject lower upper next) :
    let constructed := LookaheadRegExp.constructedState before constructor.prototype (LookaheadRegExp.compiledRecord lower upper next)
    ∃ returned after,
      LookaheadRegExp.invokeConstructor context (.function handle) (.string (LiteralLookahead.rawSource lower upper next)) before =
        .ok (.object before.base.base.regexp.ambient.objects.length, constructed) ∧
      LookaheadRegExp.invokeExec (.object before.base.base.regexp.ambient.objects.length) [.string input] constructed = .ok (returned, after) ∧
      ConstructionContract before constructed (.object before.base.base.regexp.ambient.objects.length) constructor.prototype lower upper next ∧
      ExecContract constructed after returned lower upper next input := by
  obtain ⟨constructed, contract⟩ := constructor_satisfies before context handle constructor prototypeObject lower upper next inputs
  obtain ⟨returned, after, executed, result⟩ := exec_satisfies _ _ _ 0 true lower upper next input []
    (constructed_exec_inputs before context handle constructor prototypeObject lower upper next inputs)
  exact ⟨returned, after, constructed, executed, contract, result⟩

/-- The independent decomposition contract determines the exact consumed
prefix, because slash is outside the admitted range. -/
theorem exec_contract_exact_prefix (before after : LookaheadRegExp.State) (returned : Value)
    (lower upper : UInt16) (next taken suffix : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (nonempty : taken ≠ [])
    (inside : ∀ unit ∈ taken, RangeRegExp.InRange lower upper unit)
    (contract : ExecContract before after returned lower upper next (taken ++ (47 :: next ++ suffix))) :
    returned = .array before.base.base.regexp.ambient.heap.length ∧
      after = prefixState before (taken ++ (47 :: next ++ suffix)) taken := by
  rcases contract with ⟨_, _, absent⟩ | ⟨other, rest, shape, _, otherInside, value, state⟩
  · exact False.elim (absent ⟨taken, suffix, rfl, nonempty, inside⟩)
  · have outside := LiteralLookahead.slash_not_in_range lower upper safeLower
    have left := LiteralLookahead.scanRange_delimited lower upper taken next suffix outside inside
    have right := LiteralLookahead.scanRange_delimited lower upper other next rest outside otherInside
    rw [← shape] at right
    have equal : taken = other := congrArg Prod.fst (left.symm.trans right)
    subst other
    exact ⟨value, state⟩

theorem exec_contract_rejects (before after : LookaheadRegExp.State) (returned : Value)
    (lower upper : UInt16) (next input : JSString)
    (absent : ¬ LiteralLookahead.Accepted lower upper next input)
    (contract : ExecContract before after returned lower upper next input) :
    returned = .null ∧ after = before := by
  rcases contract with ⟨value, state, _⟩ | ⟨taken, suffix, shape, nonempty, inside, _, _⟩
  · exact ⟨value, state⟩
  · exact False.elim (absent ⟨taken, suffix, shape, nonempty, inside⟩)

theorem exec_frames (before after : LookaheadRegExp.State) (returned : Value) (lower upper : UInt16) (next input : JSString)
    (contract : ExecContract before after returned lower upper next input) :
    after.base.base.regexp.ambient.objects = before.base.base.regexp.ambient.objects ∧
    after.records = before.records ∧ after.base.base.regexp.brands = before.base.base.regexp.brands ∧
    after.base.brands = before.base.brands ∧ after.base.results = before.base.results ∧
    after.base.base.regexp.ambient.environment = before.base.base.regexp.ambient.environment ∧
    after.base.base.regexp.ambient.thisValue = before.base.base.regexp.ambient.thisValue ∧
    after.base.base.regexp.ambient.functions = before.base.base.regexp.ambient.functions ∧
    after.base.base.regexp.ambient.privates = before.base.base.regexp.ambient.privates ∧
    after.base.base.regexp.ambient.sets = before.base.base.regexp.ambient.sets := by
  rcases contract with ⟨_, rfl, _⟩ | ⟨taken, suffix, _, _, _, _, rfl⟩ <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exec_old_arrays (before after : LookaheadRegExp.State) (returned : Value) (lower upper : UInt16) (next input : JSString)
    (contract : ExecContract before after returned lower upper next input) (reference : Nat)
    (bound : reference < before.base.base.regexp.ambient.heap.length) :
    after.base.base.regexp.ambient.heap[reference]? = before.base.base.regexp.ambient.heap[reference]? := by
  rcases contract with ⟨_, rfl, _⟩ | ⟨taken, suffix, _, _, _, _, rfl⟩
  · rfl
  · exact List.getElem?_append_left bound

end HonoLean.Upstream.GetPatternLookahead
