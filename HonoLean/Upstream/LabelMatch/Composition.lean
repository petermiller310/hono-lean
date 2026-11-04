import HonoLean.Upstream.LabelMatch.Correctness
import HonoLean.Upstream.NodePatternBinding.Composition

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace HonoLean.Upstream.LabelMatch
open SourceSubset ECMA2025

def safeRangeLabel (name : JSString) (lower upper : UInt16) : JSString :=
  58 :: (name ++ 123 :: (PatternConstruct.rawBody lower upper ++ [125]))

theorem safe_range_body (lower upper : UInt16) (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper) :
    LabelRegExp.Body (PatternConstruct.rawBody lower upper) := by
  constructor
  · simp [PatternConstruct.rawBody]
  · intro unit member
    have lowerRange : 48 ≤ lower.toNat ∧ lower.toNat ≤ 122 := by
      rcases safeLower with range | range | range <;> omega
    have upperRange : 48 ≤ upper.toNat ∧ upper.toNat ≤ 122 := by
      rcases safeUpper with range | range | range <;> omega
    simp only [PatternConstruct.rawBody, List.mem_cons, List.not_mem_nil, or_false] at member
    have bounds : 43 ≤ unit.toNat ∧ unit.toNat ≤ 125 := by
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | omega | decide
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      intro equal
      have number := congrArg UInt16.toNat equal
      simp at number
      omega

theorem safe_range_label (name : JSString) (lower upper : UInt16) (validName : LabelRegExp.Name name)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper) :
    LabelRegExp.Label (safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper)) :=
  ⟨validName, safe_range_body lower upper safeLower safeUpper, rfl⟩

/-- Initial constructor identity/bounds are separate from the intrinsic regex
literal. The label producer itself accepts arbitrary labels and lexical RegExp
shadows; only this downstream selected branch requires the standard constructor. -/
structure ConstructorInputs (before : LabelMatchState) (context : LabelMatchContext) (name : JSString) (lower upper : UInt16)
    (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) : Prop where
  source : Inputs before context (safeRangeLabel name lower upper)
  validName : LabelRegExp.Name name
  lowerSafe : RangeRegExp.SafeEndpoint lower
  upperSafe : RangeRegExp.SafeEndpoint upper
  ordered : lower.toNat ≤ upper.toNat
  constructorBinding : before.base.regexp.ambient.environment.lookup "RegExp" = some (.function handle)
  noArgBefore : before.base.regexp.ambient.functions.length ≤ context.iterators.constructors.constructors.base
  methodsBefore : context.iterators.constructors.methods.base + context.iterators.constructors.methods.entries.length ≤ context.iterators.constructors.constructors.base
  functionsBefore : context.iterators.constructors.functions.base + context.iterators.constructors.functions.entries.length ≤ context.iterators.constructors.constructors.base
  membersBefore : context.iterators.constructors.members.base + context.iterators.constructors.members.entries.length ≤ context.iterators.constructors.constructors.base
  builtinsBefore : context.iterators.constructors.builtins.base + context.iterators.constructors.builtins.entries.length ≤ context.iterators.constructors.constructors.base
  handleBound : context.iterators.constructors.constructors.base ≤ handle
  identity : context.iterators.constructors.constructors.entries[handle - context.iterators.constructors.constructors.base]? = some constructor
  prototypeFound : before.base.regexp.ambient.objects[constructor.prototype]? = some prototypeObject

theorem produced_constructor_inputs (before : LabelMatchState) (context : LabelMatchContext) (name : JSString) (lower upper : UInt16)
    (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : ConstructorInputs before context name lower upper handle constructor prototypeObject) :
    PatternConstruct.Inputs (resultState before context (safeRangeLabel name lower upper)).base.regexp context.iterators.constructors
      (safeRangeLabel name lower upper) name before.base.regexp.ambient.heap.length handle
      (captures (safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))) lower upper constructor prototypeObject := by
  have contract := result_contract before context (safeRangeLabel name lower upper)
  have matched := contract.success name (some (PatternConstruct.rawBody lower upper))
    (safe_range_label name lower upper inputs.validName inputs.lowerSafe inputs.upperSafe)
  have environment := matched.1
  have heap := matched.2.1
  refine ⟨?_, ?_, ?_, rfl, rfl, (by change 3 ≤ 4294967295; decide), inputs.lowerSafe, inputs.upperSafe, inputs.ordered,
    ?_, ?_, inputs.methodsBefore, inputs.functionsBefore, inputs.membersBefore, inputs.builtinsBefore,
    inputs.handleBound, inputs.identity, ?_⟩
  · rw [environment]
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.source.labelBinding
  · rw [environment]
    rfl
  · rw [heap]
    simp
  · rw [environment]
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using inputs.constructorBinding
  · rw [contract.functions]
    exact inputs.noArgBefore
  · exact (contract.oldObjects constructor.prototype (List.getElem?_eq_some_iff.mp inputs.prototypeFound).1).trans inputs.prototypeFound

/-- Actual59B producer supplies the previously assumed capturearray, then actual
46B constructs its tuple/regex. The enclosing if/cache/next selection is a
selected activation handoff, not a proved contiguous execution/reachability. -/
theorem source_match_then_construct_satisfies (extraMatch extraConstruct : Nat) (before : LabelMatchState) (context : LabelMatchContext)
    (name : JSString) (lower upper : UInt16) (handle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject)
    (inputs : ConstructorInputs before context name lower upper handle constructor prototypeObject) :
    sourceMatch (extraMatch + 128) context before = some (.ok (resultState before context (safeRangeLabel name lower upper))) ∧
    PatternConstruct.sourceConstruct (extraConstruct + 16) context.iterators.constructors
      (resultState before context (safeRangeLabel name lower upper)).base.regexp =
      some (.ok (.array (resultState before context (safeRangeLabel name lower upper)).base.regexp.ambient.heap.length,
        PatternConstruct.resultState (resultState before context (safeRangeLabel name lower upper)).base.regexp constructor.prototype lower upper (safeRangeLabel name lower upper) name)) ∧
    PatternConstruct.Contract (resultState before context (safeRangeLabel name lower upper)).base.regexp
      (PatternConstruct.resultState (resultState before context (safeRangeLabel name lower upper)).base.regexp constructor.prototype lower upper (safeRangeLabel name lower upper) name)
      (.array (resultState before context (safeRangeLabel name lower upper)).base.regexp.ambient.heap.length)
      (safeRangeLabel name lower upper) name constructor.prototype lower upper := by
  have source := (source_match_satisfies extraMatch before context _ inputs.source).1
  obtain ⟨constructed, contract, _⟩ := PatternConstruct.source_construct_satisfies extraConstruct _ context.iterators.constructors
    (safeRangeLabel name lower upper) name before.base.regexp.ambient.heap.length handle
    (captures (safeRangeLabel name lower upper) name (some (PatternConstruct.rawBody lower upper))) lower upper constructor prototypeObject
    (produced_constructor_inputs before context name lower upper handle constructor prototypeObject inputs)
  exact ⟨source, constructed, contract⟩

theorem produced_binding_realm (before : LabelMatchState) (context : LabelMatchContext) (input : JSString)
    (valuesHandle nextHandle : Nat) (returned : Value) (source : Inputs before context input)
    (realm : NodePatternBinding.Realm before.base context.iterators valuesHandle nextHandle returned) :
    NodePatternBinding.Realm (resultState before context input).base context.iterators valuesHandle nextHandle returned := by
  have contract := result_contract before context input
  obtain ⟨prototypeObject, prototypeFound, _⟩ := source.regexpFound
  have prototypeOld := (List.getElem?_eq_some_iff.mp prototypeFound).1
  have old := fun (reference : Nat) (object : OrdinaryObject) (found : before.base.regexp.ambient.objects[reference]? = some object) =>
    (contract.oldObjects reference (List.getElem?_eq_some_iff.mp found).1).trans found
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, realm.methodsBefore, realm.functionsBefore, realm.membersBefore,
    realm.regexpBefore, realm.constructorsBefore, realm.valuesBound, realm.valuesIdentity, realm.nextBound, realm.nextIdentity, ?_, ?_, realm.nullish⟩
  · rw [contract.objects]
    exact NodePatternBinding.closed_append_object _ _ realm.closed (by intro parent edge; cases edge; exact prototypeOld)
  · obtain ⟨object, found⟩ := realm.arrayPrototypeFound
    exact ⟨object, old _ _ found⟩
  · obtain ⟨object, found⟩ := realm.iteratorPrototypeFound
    exact ⟨object, old _ _ found⟩
  · obtain ⟨object, found⟩ := realm.resultPrototypeFound
    exact ⟨object, old _ _ found⟩
  · unfold symbolOwn
    rw [show (resultState before context input).base.symbols = before.base.symbols from contract.iteratorSymbols]
    exact realm.symbol
  · rw [contract.functions]
    exact realm.noArgBefore
  · obtain ⟨depth, path, bound⟩ := realm.nextPath
    rw [contract.objects]
    exact ⟨depth, NodeCaptureGuard.descriptor_path_append _ _ _ _ _ _ path, bound⟩
  · obtain ⟨descriptor, depth, path, bound, pureRead⟩ := realm.returnPath
    rw [contract.objects]
    exact ⟨descriptor, depth, NodeCaptureGuard.descriptor_path_append _ _ _ _ _ _ path, bound, pureRead⟩

theorem produced_array_symbols (before : LabelMatchState) (context : LabelMatchContext) (input name : JSString) (body : Option JSString)
    (valid : LabelRegExp.Label input name body) (allocated : ArraySymbolsAllocated before.base) :
    ArraySymbolsAllocated (resultState before context input).base := by
  intro entry member reference equal
  have contract := result_contract before context input
  rw [contract.iteratorSymbols] at member
  have bound := allocated entry member reference equal
  have heap := (contract.success name body valid).2.1
  rw [heap]
  simp only [List.length_append, List.length_singleton]
  omega

theorem produced_exec_realm (before : LabelMatchState) (context : LabelMatchContext) (input : JSString)
    (prototype handle : Nat) (query : JSString) (realm : NodePatternBinding.ExecRealm before.base context.iterators prototype handle query) :
    NodePatternBinding.ExecRealm (resultState before context input).base context.iterators prototype handle query := by
  have contract := result_contract before context input
  refine ⟨?_, ?_, ?_, realm.privateBeforeMember, realm.functionsBeforeMember, realm.membersBeforeBuiltin, realm.handleBound, realm.identity⟩
  · change List.lookup "restPathString" (("match", _) :: before.base.regexp.ambient.environment) = _
    simpa only [List.lookup_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte] using realm.query
  · obtain ⟨writable, enumerable, configurable, depth, path, bound⟩ := realm.current
    rw [contract.objects]
    exact ⟨writable, enumerable, configurable, depth, NodeCaptureGuard.descriptor_path_append _ _ _ _ _ _ path, bound⟩
  · rw [contract.functions]
    exact realm.noArgBeforeMember

/-- Four selected source activations: real capturing producer60, terminal tuple68,
actual138 binding, then genuine builtin156 digits. No early m/capturearray,
future brand or supplied matcher binding; query production and intervening cache,
tree installation/search control remain explicit open links. -/
theorem source_label_construct_binding_digits_exec_satisfies (extraMatch extraConstruct extraBinding extraExec : Nat)
    (before : LabelMatchState) (context : LabelMatchContext) (name query : JSString)
    (constructorHandle valuesHandle nextHandle execHandle : Nat) (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (returned : Value)
    (inputs : ConstructorInputs before context name 48 57 constructorHandle constructor prototypeObject)
    (realm : NodePatternBinding.Realm before.base context.iterators valuesHandle nextHandle returned)
    (allocated : ArraySymbolsAllocated before.base)
    (exec : NodePatternBinding.ExecRealm before.base context.iterators constructor.prototype execHandle query) :
    sourceMatch (extraMatch + 128) context before = some (.ok (resultState before context (safeRangeLabel name 48 57))) ∧
    PatternConstruct.sourceConstruct (extraConstruct + 16) context.iterators.constructors
      (resultState before context (safeRangeLabel name 48 57)).base.regexp =
      some (.ok (.array (resultState before context (safeRangeLabel name 48 57)).base.regexp.ambient.heap.length,
        PatternConstruct.resultState (resultState before context (safeRangeLabel name 48 57)).base.regexp constructor.prototype 48 57 (safeRangeLabel name 48 57) name)) ∧
    NodePatternBinding.sourceBinding (extraBinding + 4) context.iterators
      (NodePatternBinding.constructedActivation (resultState before context (safeRangeLabel name 48 57)).base constructor.prototype 48 57 (safeRangeLabel name 48 57) name) =
      some (.ok (NodePatternBinding.record (NodePatternBinding.constructedActivation (resultState before context (safeRangeLabel name 48 57)).base constructor.prototype 48 57 (safeRangeLabel name 48 57) name) nextHandle,
        NodePatternBinding.boundState (resultState before context (safeRangeLabel name 48 57)).base context.iterators constructor.prototype 48 57 (safeRangeLabel name 48 57) name valuesHandle nextHandle returned)) ∧
    NodeRegExpExec.sourceExec (extraExec + 20) context.iterators.constructors.methods context.iterators.constructors.functions
      context.iterators.constructors.members context.iterators.constructors.builtins
      (NodePatternBinding.boundState (resultState before context (safeRangeLabel name 48 57)).base context.iterators constructor.prototype 48 57 (safeRangeLabel name 48 57) name valuesHandle nextHandle returned).regexp =
      some (.ok (NodeRegExpExec.resultState
        (NodePatternBinding.boundState (resultState before context (safeRangeLabel name 48 57)).base context.iterators constructor.prototype 48 57 (safeRangeLabel name 48 57) name valuesHandle nextHandle returned).regexp query)) ∧
    NodeRegExpExec.Contract (extraExec + 20)
      (NodePatternBinding.boundState (resultState before context (safeRangeLabel name 48 57)).base context.iterators constructor.prototype 48 57 (safeRangeLabel name 48 57) name valuesHandle nextHandle returned).regexp
      (NodeRegExpExec.resultState
        (NodePatternBinding.boundState (resultState before context (safeRangeLabel name 48 57)).base context.iterators constructor.prototype 48 57 (safeRangeLabel name 48 57) name valuesHandle nextHandle returned).regexp query)
      (resultState before context (safeRangeLabel name 48 57)).base.regexp.ambient.objects.length execHandle query
      (initializedRegExpObject constructor.prototype) 0 true := by
  have valid := safe_range_label name 48 57 inputs.validName inputs.lowerSafe inputs.upperSafe
  obtain ⟨constructed, bound, executed, finished⟩ := NodePatternBinding.source_construct_binding_digits_exec_satisfies extraConstruct extraBinding extraExec
    (resultState before context (safeRangeLabel name 48 57)).base context.iterators (safeRangeLabel name 48 57) name query
    before.base.regexp.ambient.heap.length constructorHandle valuesHandle nextHandle execHandle
    (captures (safeRangeLabel name 48 57) name (some (PatternConstruct.rawBody 48 57))) constructor prototypeObject returned
    (produced_constructor_inputs before context name 48 57 constructorHandle constructor prototypeObject inputs)
    (produced_binding_realm before context _ valuesHandle nextHandle returned inputs.source realm)
    (produced_array_symbols before context _ name _ valid allocated)
    (produced_exec_realm before context _ constructor.prototype execHandle query exec)
  exact ⟨(source_match_satisfies extraMatch before context _ inputs.source).1, constructed, bound, executed, finished⟩

end HonoLean.Upstream.LabelMatch
