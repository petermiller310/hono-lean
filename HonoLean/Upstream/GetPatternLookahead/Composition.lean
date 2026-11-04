import HonoLean.Upstream.GetPatternLookahead.Source
import HonoLean.Upstream.GetPatternLookahead.Correctness
import HonoLean.Upstream.SourceSubset.LookaheadRegExp.Expressions

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.GetPatternLookahead
open SourceSubset hiding pinnedSource State
open ECMA2025
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

def matchedState (before : LookaheadRegExp.State) (context : PatternCacheContext) (input : JSString) : LookaheadRegExp.State :=
  LookaheadRegExp.withBase before (PatternCache.matchedState before.base context input)

def preparedState (before : LookaheadRegExp.State) (context : PatternCacheContext) (input next : JSString) : LookaheadRegExp.State :=
  LookaheadRegExp.withBase before (PatternCache.keyedState before.base context input (some next))

/-- Execute the actual selected declarations and tuple extracted from the
complete parsed body. Omitted cache guards/store/source74 and lexical invocation
remain separate; this runner makes no claim to execute those statements. -/
def sourceSelectedTuple (fuel : Nat) (context : PatternCacheContext) (before : LookaheadRegExp.State) :
    Option (Except LookaheadRegExp.Error (Value × LookaheadRegExp.State)) :=
  parsedNodes.map (fun selected => do
    let matched ← LookaheadRegExp.executeDeclaration fuel defaultSplitLimit context selected.labelDeclaration before
    let prepared ← LookaheadRegExp.executeDeclaration fuel defaultSplitLimit context selected.keyDeclaration matched
    LookaheadRegExp.evalExpr fuel defaultSplitLimit context selected.positiveTuple prepared)

/-- Verification-driver observation: get the produced tuple's actual slot2,
then invoke the closed default builtin. This is not a source156 method-call or
search/route-traversal theorem. -/
def sourceSelectedExec (fuel : Nat) (context : PatternCacheContext) (before : LookaheadRegExp.State) (input : JSString) :
    Option (Except LookaheadRegExp.Error (Value × LookaheadRegExp.State)) :=
  (sourceSelectedTuple fuel context before).map (fun produced => do
    let (tuple, after) ← produced
    let matcher ← (cacheReadProperty tuple (.number 2) after.base.base.regexp.ambient).mapError
      (LookaheadRegExp.Error.pattern ∘ PatternCacheError.evaluation)
    LookaheadRegExp.invokeExec matcher [.string input] after)

theorem declaration_label (extra : Nat) (before : LookaheadRegExp.State) (context : PatternCacheContext) (input : JSString)
    (inputs : LabelMatch.Inputs before.base context.label input) :
    LookaheadRegExp.executeDeclaration (extra + 129) defaultSplitLimit context labelDeclaration before =
      .ok (matchedState before context input) := by
  have old := PatternCache.label_declaration extra before.base context input inputs
  rw [labelDeclaration, show extra + 129 = (extra + 128) + 1 by omega, LookaheadRegExp.label_declaration_refines, old]
  rfl

theorem matched_binding (before : LookaheadRegExp.State) (context : PatternCacheContext) (input name : JSString)
    (body : Option JSString) (valid : LabelRegExp.Label input name body) (queryName : String) (value : Value)
    (different : queryName ≠ "match") (binding : before.base.base.regexp.ambient.environment.lookup queryName = some value) :
    (matchedState before context input).base.base.regexp.ambient.environment.lookup queryName = some value := by
  have environment := ((LabelMatch.result_contract before.base context.label input).success name body valid).1
  change (LabelMatch.resultState before.base context.label input).base.regexp.ambient.environment.lookup queryName = _
  rw [environment]
  have differentBool : (queryName == "match") = false := beq_eq_false_iff_ne.mpr different
  simpa only [List.lookup_cons, differentBool, Bool.false_eq_true, ↓reduceIte] using binding

theorem declaration_key (extra : Nat) (before : LookaheadRegExp.State) (context : PatternCacheContext) (input name : JSString)
    (body : Option JSString) (next : JSString) (valid : LabelRegExp.Label input name body)
    (labelBinding : before.base.base.regexp.ambient.environment.lookup "label" = some (.string input))
    (nextBinding : before.base.base.regexp.ambient.environment.lookup "next" = some (.string next)) :
    LookaheadRegExp.executeDeclaration (extra + 4) defaultSplitLimit context keyDeclaration (matchedState before context input) =
      .ok (preparedState before context input next) := by
  have label := matched_binding before context input name body valid "label" _ (by decide) labelBinding
  have nextFound := matched_binding before context input name body valid "next" _ (by decide) nextBinding
  have old := evalPatternCache_key extra defaultSplitLimit context (matchedState before context input).base input (.string next) label nextFound
  have raw : patternCacheKey input (.string next) = .ok (PatternCache.key input (some next)) := PatternCache.raw_key input (some next)
  rw [raw] at old
  have live := LookaheadRegExp.template_refines (extra + 3) defaultSplitLimit context []
    [(.variable "label", [35]), (.variable "next", [])] (matchedState before context input)
  have budget : extra + 3 + 1 = extra + 4 := by omega
  rw [budget, old] at live
  simp only [Except.mapError, Except.map] at live
  rw [keyDeclaration, LookaheadRegExp.executeDeclaration, PatternCache.keyTemplate, live]
  rfl

theorem prepared_coherent (before : LookaheadRegExp.State) (context : PatternCacheContext) (input name : JSString)
    (body : Option JSString) (next : JSString) (valid : LabelRegExp.Label input name body) (coherent : LookaheadRegExp.Coherent before) :
    LookaheadRegExp.Coherent (preparedState before context input next) := by
  have snapshot := PatternCacheTerminal.matched_snapshot before.base context input name body valid
  let left := before.records.map (fun (reference, record) => (reference, LookaheadRegExp.TaggedRecord.lookahead record))
  let right := before.base.brands.map (fun (reference, record) => (reference, LookaheadRegExp.TaggedRecord.label record)) ++
    before.base.base.regexp.brands.map (fun (reference, record) => (reference, LookaheadRegExp.TaggedRecord.range record))
  apply LookaheadRegExp.coherent_insert before (preparedState before context input next) left right (.label labelLiteralRecord)
  · simp only [LookaheadRegExp.taggedEntries, left, right, List.append_assoc]
  · simp only [preparedState, PatternCache.keyedState]
    rw [snapshot]
    simp only [LookaheadRegExp.taggedEntries, LookaheadRegExp.withBase, cacheWithAmbient,
      PatternCacheTerminal.matchedSnapshot, labelFreshState, left, right, List.map_cons, List.append_assoc, List.cons_append]
  · simp only [preparedState, PatternCache.keyedState]
    rw [snapshot]
    simp [LookaheadRegExp.withBase, cacheWithAmbient, PatternCacheTerminal.matchedSnapshot, labelFreshState]
  · exact coherent

theorem prepared_operand_inputs (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next handle constructor prototypeObject) :
    PatternConstruct.Inputs (preparedState before context (LabelMatch.safeRangeLabel name lower upper) next).base.base.regexp
      context.label.iterators.constructors (LabelMatch.safeRangeLabel name lower upper) name before.base.base.regexp.ambient.heap.length handle
      (LabelMatch.captures (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))) lower upper constructor prototypeObject := by
  let realm := inputs.source.toLabelRealm
  have noArg := realm.oldNoArg
  have methods := realm.oldMethods
  have functions := realm.oldFunctions
  have members := realm.oldMembers
  have regexp := realm.oldRegExp
  have initial : LabelMatch.ConstructorInputs before.base context.label name lower upper handle constructor prototypeObject := by
    refine ⟨inputs.source, inputs.nameValid, inputs.lowerSafe, inputs.upperSafe, inputs.ordered, inputs.constructorBinding,
      ?_, ?_, ?_, ?_, regexp, inputs.handleBound, inputs.identity, inputs.prototypeFound⟩
    all_goals omega
  have produced := LabelMatch.produced_constructor_inputs before.base context.label name lower upper handle constructor prototypeObject initial
  constructor
  case labelBinding =>
    change List.lookup "label" (("cacheKey", _) :: _) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, PatternCache.matchedState] using produced.labelBinding
  case matchBinding =>
    change List.lookup "match" (("cacheKey", _) :: _) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, PatternCache.matchedState] using produced.matchBinding
  case constructorBinding =>
    change List.lookup "RegExp" (("cacheKey", _) :: _) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, PatternCache.matchedState] using produced.constructorBinding
  all_goals cases produced <;> assumption

theorem prepared_next (before : LookaheadRegExp.State) (context : PatternCacheContext) (input name : JSString)
    (body : Option JSString) (next : JSString) (valid : LabelRegExp.Label input name body)
    (binding : before.base.base.regexp.ambient.environment.lookup "next" = some (.string next)) :
    (preparedState before context input next).base.base.regexp.ambient.environment.lookup "next" = some (.string next) := by
  have prior := matched_binding before context input name body valid "next" _ (by decide) binding
  change List.lookup "next" (("cacheKey", _) :: _) = _
  simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, matchedState, LookaheadRegExp.withBase] using prior

theorem prepared_key (before : LookaheadRegExp.State) (context : PatternCacheContext) (input next : JSString) :
    (preparedState before context input next).base.base.regexp.ambient.environment.lookup "cacheKey" =
      some (.string (PatternCache.key input (some next))) := rfl

theorem prepared_constructor_inputs (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next handle constructor prototypeObject) :
    ConstructorInputs (preparedState before context (LabelMatch.safeRangeLabel name lower upper) next)
      context.label.iterators.constructors handle constructor prototypeObject lower upper next := by
  have operands := prepared_operand_inputs before context name lower upper next handle constructor prototypeObject inputs
  exact ⟨prepared_coherent before context _ name _ next
      (LabelMatch.safe_range_label name lower upper inputs.nameValid inputs.lowerSafe inputs.upperSafe) inputs.coherent,
    operands.noArgBefore, operands.methodsBefore, operands.functionsBefore, operands.membersBefore, operands.builtinsBefore,
    operands.handleBound, operands.identity, operands.prototypeFound, inputs.lowerSafe, inputs.upperSafe, inputs.ordered, inputs.nextSafe⟩

theorem positive_next_condition (extra : Nat) (before : LookaheadRegExp.State) (context : PatternCacheContext) (next : JSString)
    (binding : before.base.base.regexp.ambient.environment.lookup "next" = some (.string next))
    (safe : LiteralLookahead.SafeNext next) :
    LookaheadRegExp.evalExpr (extra + 10) defaultSplitLimit context PatternCache.nextCondition before = .ok (.boolean true, before) := by
  cases next with
  | nil => exact False.elim (safe.1 rfl)
  | cons unit rest =>
    have unitSafe := safe.2 unit (by simp)
    have notColon : unit ≠ 58 := by intro equal; subst unit; simp [RangeRegExp.SafeEndpoint] at unitSafe
    have notStar : unit ≠ 42 := by intro equal; subst unit; simp [RangeRegExp.SafeEndpoint] at unitSafe
    simp [PatternCache.nextCondition, PatternCache.nextExpr, LookaheadRegExp.evalExpr, evalExpression, lookupVariable,
      binding, cacheReadProperty, truthy, notColon, notStar, LookaheadRegExp.withAmbient, LookaheadRegExp.withBase, cacheWithAmbient]

theorem prepared_objects (before : LookaheadRegExp.State) (context : PatternCacheContext) (input next : JSString) :
    (preparedState before context input next).base.base.regexp.ambient.objects =
      before.base.base.regexp.ambient.objects ++ [initializedRegExpObject context.label.regexpPrototype] :=
  (LabelMatch.result_contract before.base context.label input).objects

theorem selected_prepared (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (prototype : Nat) (valid : LabelRegExp.Label (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))) :
    selectedState before context name lower upper next prototype =
      LookaheadRegExp.constructedState
        (LookaheadRegExp.withBase (preparedState before context (LabelMatch.safeRangeLabel name lower upper) next)
          (cacheArrayCellState (preparedState before context (LabelMatch.safeRangeLabel name lower upper) next).base
            [.string (PatternCache.key (LabelMatch.safeRangeLabel name lower upper) (some next)), .string name,
              .object (preparedState before context (LabelMatch.safeRangeLabel name lower upper) next).base.base.regexp.ambient.objects.length]))
        prototype (LookaheadRegExp.compiledRecord lower upper next) := by
  have snapshot := PatternCacheTerminal.matched_snapshot before.base context _ name _ valid
  have count := congrArg List.length (prepared_objects before context (LabelMatch.safeRangeLabel name lower upper) next)
  simp only [List.length_append, List.length_singleton] at count
  rw [count]
  simp only [selectedState, preparedState, PatternCache.keyedState, LookaheadRegExp.withBase]
  rw [snapshot]

theorem selected_contract (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (prototype : Nat)
    (valid : LabelRegExp.Label (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)))
    (coherent : LookaheadRegExp.Coherent before) :
    SelectedContract before (selectedState before context name lower upper next prototype)
      (.array (before.base.base.regexp.ambient.heap.length + 1)) context name lower upper next prototype := by
  have heap : (selectedState before context name lower upper next prototype).base.base.regexp.ambient.heap =
      before.base.base.regexp.ambient.heap ++
        [LabelMatch.captures (LabelMatch.safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)),
         [.string (PatternCache.key (LabelMatch.safeRangeLabel name lower upper) (some next)), .string name,
          .object (before.base.base.regexp.ambient.objects.length + 1)]] := by
    simp [selectedState, LookaheadRegExp.constructedState, LookaheadRegExp.withAmbient, LookaheadRegExp.withBase,
      PatternCacheTerminal.matchedSnapshot, labelFreshState, cacheArrayCellState, cacheWithAmbient, List.append_assoc]
  have objects : (selectedState before context name lower upper next prototype).base.base.regexp.ambient.objects =
      before.base.base.regexp.ambient.objects ++ [initializedRegExpObject context.label.regexpPrototype, initializedRegExpObject prototype] := by
    simp [selectedState, LookaheadRegExp.constructedState, LookaheadRegExp.withAmbient, LookaheadRegExp.withBase,
      PatternCacheTerminal.matchedSnapshot, labelFreshState, cacheArrayCellState, cacheWithAmbient, List.append_assoc]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [heap]
    simp
  · rw [objects]
    simp
  · simp [selectedState, LookaheadRegExp.constructedState, LookaheadRegExp.withAmbient, LookaheadRegExp.withBase,
      PatternCacheTerminal.matchedSnapshot, labelFreshState, cacheArrayCellState, cacheWithAmbient]
  · rw [selected_prepared before context name lower upper next prototype valid]
    apply LookaheadRegExp.coherent_constructed
    have initial := prepared_coherent before context _ name _ next valid coherent
    exact ⟨initial.allocated, initial.unique⟩

theorem selected_exec_inputs (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next handle constructor prototypeObject) :
    ExecInputs (selectedState before context name lower upper next constructor.prototype)
      (before.base.base.regexp.ambient.objects.length + 1) (initializedRegExpObject constructor.prototype) 0 true lower upper next := by
  have result := selected_contract before context name lower upper next constructor.prototype
    (LabelMatch.safe_range_label name lower upper inputs.nameValid inputs.lowerSafe inputs.upperSafe) inputs.coherent
  exact ⟨result.coherent, result.record, result.matcher, rfl, by decide,
    inputs.lowerSafe, inputs.upperSafe, inputs.ordered, inputs.nextSafe⟩

theorem selected_tuple_get (before after : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (prototype : Nat)
    (contract : SelectedContract before after (.array (before.base.base.regexp.ambient.heap.length + 1)) context name lower upper next prototype) :
    cacheReadProperty (.array (before.base.base.regexp.ambient.heap.length + 1)) (.number 2) after.base.base.regexp.ambient =
      .ok (.object (before.base.base.regexp.ambient.objects.length + 1)) := by
  simp [cacheReadProperty, readProperty, contract.tuple]

theorem source_positive_condition (extra : Nat) (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next handle constructor prototypeObject) :
    LookaheadRegExp.evalExpr (extra + 256) defaultSplitLimit context PatternCache.nextCondition
      (preparedState before context (LabelMatch.safeRangeLabel name lower upper) next) =
        .ok (.boolean true, preparedState before context (LabelMatch.safeRangeLabel name lower upper) next) := by
  have valid := LabelMatch.safe_range_label name lower upper inputs.nameValid inputs.lowerSafe inputs.upperSafe
  simpa only [Nat.add_assoc, Nat.reduceAdd] using positive_next_condition (extra + 246) _ context next
    (prepared_next before context _ name _ next valid inputs.nextBinding) inputs.nextSafe

/-- Actual parsed60→62→67 selected operations, from initial inputs only. The
producer derives match captures and the raw cacheKey. The final tuple contains
that key, the derived name and the newly compiled lookahead matcher. -/
theorem source_selected_tuple_satisfies (extra : Nat) (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next : JSString) (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next handle constructor prototypeObject) :
    sourceSelectedTuple (extra + 256) context before =
      some (.ok (.array (before.base.base.regexp.ambient.heap.length + 1), selectedState before context name lower upper next constructor.prototype)) ∧
    SelectedContract before (selectedState before context name lower upper next constructor.prototype)
      (.array (before.base.base.regexp.ambient.heap.length + 1)) context name lower upper next constructor.prototype := by
  let input := LabelMatch.safeRangeLabel name lower upper
  let prepared := preparedState before context input next
  have valid := LabelMatch.safe_range_label name lower upper inputs.nameValid inputs.lowerSafe inputs.upperSafe
  have label : LookaheadRegExp.executeDeclaration (extra + 256) defaultSplitLimit context labelDeclaration before = .ok (matchedState before context input) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using declaration_label (extra + 127) before context input inputs.source
  have key : LookaheadRegExp.executeDeclaration (extra + 256) defaultSplitLimit context keyDeclaration (matchedState before context input) = .ok prepared := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using declaration_key (extra + 252) before context input name _ next valid inputs.source.labelBinding inputs.nextBinding
  have operands := prepared_operand_inputs before context name lower upper next handle constructor prototypeObject inputs
  have tuple := LookaheadRegExp.eval_positive_tuple (extra + 243) prepared context input name before.base.base.regexp.ambient.heap.length handle
    (LabelMatch.captures input name (some (PatternConstruct.rawBody lower upper))) lower upper constructor prototypeObject next (PatternCache.key input (some next)) operands
    (prepared_coherent before context input name _ next valid inputs.coherent)
    (prepared_next before context input name _ next valid inputs.nextBinding) inputs.nextSafe (prepared_key before context input next)
  have endpoint : LookaheadRegExp.tupleState prepared (PatternCache.key input (some next)) name constructor.prototype lower upper next =
      selectedState before context name lower upper next constructor.prototype := (selected_prepared before context name lower upper next constructor.prototype valid).symm
  have count : prepared.base.base.regexp.ambient.heap.length = before.base.base.regexp.ambient.heap.length + 1 :=
    (PatternCacheTerminal.keyed_captures before.base context input name _ (some next) valid).2.2
  rw [endpoint, count] at tuple
  have tupleEval : LookaheadRegExp.evalExpr (extra + 256) defaultSplitLimit context positiveTuple prepared =
      .ok (.array (before.base.base.regexp.ambient.heap.length + 1), selectedState before context name lower upper next constructor.prototype) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, positiveTuple] using tuple
  refine ⟨?_, selected_contract before context name lower upper next constructor.prototype valid inputs.coherent⟩
  simp only [sourceSelectedTuple, parses_nodes, Option.map_some, nodes]
  rw [label]
  simp only [bind, Except.bind]
  rw [key]
  exact congrArg some tupleEval

theorem source_selected_exec_satisfies (extra : Nat) (before : LookaheadRegExp.State) (context : PatternCacheContext) (name : JSString)
    (lower upper : UInt16) (next query : JSString) (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : Inputs before context name lower upper next handle constructor prototypeObject) :
    ∃ returned after,
      sourceSelectedTuple (extra + 256) context before =
        some (.ok (.array (before.base.base.regexp.ambient.heap.length + 1), selectedState before context name lower upper next constructor.prototype)) ∧
      sourceSelectedExec (extra + 256) context before query = some (.ok (returned, after)) ∧
      SelectedContract before (selectedState before context name lower upper next constructor.prototype)
        (.array (before.base.base.regexp.ambient.heap.length + 1)) context name lower upper next constructor.prototype ∧
      ExecContract (selectedState before context name lower upper next constructor.prototype) after returned lower upper next query := by
  obtain ⟨produced, contract⟩ := source_selected_tuple_satisfies extra before context name lower upper next handle constructor prototypeObject inputs
  obtain ⟨returned, after, executed, result⟩ := exec_satisfies _ _ _ 0 true lower upper next query []
    (selected_exec_inputs before context name lower upper next handle constructor prototypeObject inputs)
  refine ⟨returned, after, produced, ?_, contract, result⟩
  simp [sourceSelectedExec, produced, selected_tuple_get before _ context name lower upper next constructor.prototype contract, executed]

end HonoLean.Upstream.GetPatternLookahead
