import HonoLean.Upstream.SourceSubset.ObjectInit

set_option autoImplicit false

namespace HonoLean.Upstream.SourceSubset.ObjectInitChecks

open ECMA2025
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private def source : String := "const params = node.#params === emptyParams ? {} : { ...node.#params }"
private def declaration : ObjectInitDecl :=
  ⟨"params", .conditional (.strictEqual (.privateProperty (.variable "node") "params") (.variable "emptyParams"))
    (.objectLiteral []) (.objectLiteral [.spread (.privateProperty (.variable "node") "params")])⟩
private def rawKey : JSString := [55296, 233]
private def hiddenKey : JSString := [104]
private def inheritedKey : JSString := [105]
private def arrayKey : JSString := [97]
private def selfKey : JSString := [115]
private def sourceObject : OrdinaryObject :=
  {own := [(protoKey, .data (.object 3) false true false),
      (rawKey, .data .undefined false true false), ([102], .data (.boolean false) true true true),
      (arrayKey, .data (.array 0) false true true), (selfKey, .data (.object 1) true true true),
      (hiddenKey, .accessor .unsupported .unsupported false false)]
   prototype := some 2}
private def before : State :=
  {environment := [("node", .object 4), ("emptyParams", .object 5), ("params", .number 99)]
   objects := [objectPrototypeProjection [], sourceObject,
      {own := [(inheritedKey, .accessor .unsupported .unsupported true true)], prototype := some 0},
      emptyNullObject, {prototype := some 0}, emptyNullObject]
   heap := [[.number 9, .object 3]]
   functions := [⟨⟨"opaque", .number 7⟩, [("capture", .array 0)]⟩]
   sets := [[rawKey]]
   thisValue := .object 4
   privates := {names := [("params", 7), ("keep", 8)], elements := [(4, [(7, .data (.object 1)), (8, .method (.function 0))])]}}

theorem parses_original_conditional_and_spread_items :
    parseObjectInit source ["node", "emptyParams"] ["params"] = some declaration := by cbv

theorem ordinary_alias_and_both_empty_source_faults_remain_real_ast :
    parseObjectInit "const params = node.#params" ["node", "emptyParams"] ["params"] =
      some ⟨"params", .ordinary (.privateProperty (.variable "node") "params")⟩ ∧
    parseObjectInit "const params = node.#params === emptyParams ? {} : {}" ["node", "emptyParams"] ["params"] =
      some ⟨"params", .conditional (.strictEqual (.privateProperty (.variable "node") "params") (.variable "emptyParams"))
        (.objectLiteral []) (.objectLiteral [])⟩ := by cbv; exact ⟨rfl, rfl⟩

theorem nested_conditionals_associate_in_the_original_arms :
    parseObjectInit "const result = a ? {} : b ? {} : { ...value }" ["a", "b", "value"] =
      some ⟨"result", .conditional (.variable "a") (.objectLiteral [])
        (.conditional (.variable "b") (.objectLiteral []) (.objectLiteral [.spread (.variable "value")]))⟩ := by
  cbv

theorem rejects_tdz_callbacks_uncomputed_proto_and_trailing_syntax :
    (["const params = params", "const params = node.#unknown === emptyParams ? {} : { ...node.#params }",
      "const params = node.#params === emptyParams ? {} : { ...node.#params", "const params = f()",
      "const params = { '__proto__': node }", "const params = { ...++node }", "const params = {}\n[0]",
      "const params = {}; const extra = {}"] : List String).all
      (fun text => (parseObjectInit text ["node", "emptyParams", "f"] ["params"]).isNone) = true ∧
    parseObjectInit source ["node", "emptyParams", "params"] ["params"] = none := by cbv

private def viewTarget (state : State) : Option (Option Nat × Bool × Option PropertyDescriptor × Option PropertyDescriptor ×
    Option PropertyDescriptor × Option PropertyDescriptor × Option PropertyDescriptor × Option PropertyDescriptor) :=
  state.objects[6]?.map (fun object => (object.prototype, object.extensible, object.own.lookup protoKey,
    object.own.lookup rawKey, object.own.lookup hiddenKey, object.own.lookup inheritedKey,
    object.own.lookup arrayKey, object.own.lookup selfKey))

theorem actual_false_arm_defines_data_proto_and_shallow_values :
    (parseObjectInit source ["node", "emptyParams"] ["params"]).map
      (fun code => (executeObjectInit 64 defaultSplitLimit code before).map
        (fun state => (state.environment.lookup "params", state.objects.length, viewTarget state))) =
      some (.ok (some (.object 6), 7, some (some 0, true,
        some (.data (.object 3) true true true), some (.data .undefined true true true), none, none,
        some (.data (.array 0) true true true), some (.data (.object 1) true true true)))) := by cbv

theorem source_objects_and_complete_nonobject_frame_stay_unchanged :
    (executeObjectInit 64 defaultSplitLimit declaration before).map (fun state =>
      (state.environment, state.objects.take before.objects.length, state.heap,
       state.privates, state.functions, state.sets, state.thisValue)) =
    .ok (("params", .object 6) :: before.environment, before.objects, before.heap,
      before.privates, before.functions, before.sets, before.thisValue) := by cbv

private def equalBefore : State :=
  {before with
    environment := [("node", .object 4), ("emptyParams", .object 1)]
    objects := before.objects.set 1 {own := [([103], .accessor .unsupported .unsupported true true)]}}

/-- Even an otherwise unsupported enumerable getter is irrelevant on identity
match: only the empty literal arm runs, with no spread-source readiness needed. -/
theorem equal_identity_arm_needs_no_copy_readiness :
    (executeObjectInit 64 defaultSplitLimit declaration equalBefore).map
      (fun state => (state.environment.lookup "params", state.objects[6]?.map (fun object => (object.own, object.prototype)))) =
      .ok (some (.object 6), some ([], some 0)) := by cbv

/-- Source evaluation itself allocates a second object. The target remains1,
proving it was allocated BEFORE the source expression produced object2. -/
theorem target_allocation_precedes_spread_source_evaluation :
    (parseObjectInit "const result = { ...Object.create(null) }" []).map
      (fun code => executeObjectInit 64 defaultSplitLimit code {objects := [objectPrototypeProjection []]}) =
      some (.ok {environment := [("result", .object 1)], objects := [objectPrototypeProjection [], emptyLiteralObject, emptyNullObject]}) := by cbv

/-- Computed property definitions and spread both bypass inherited [[Set]]. -/
theorem computed_proto_data_and_nullish_spread :
    (parseObjectInit "const result = { ['__proto__']: null, ...value }" ["value"]).map
      (fun code => executeObjectInit 64 defaultSplitLimit code
        {environment := [("value", .undefined)], objects := [objectPrototypeProjection []]}) =
      some (.ok {
        environment := [("result", .object 1), ("value", .undefined)]
        objects := [objectPrototypeProjection [], newDataObject emptyLiteralObject protoKey .null]}) := by cbv

/-- Enumerable getters execute in native JS but are explicitly unsupported in
this data-only model. This is a scope boundary, not a native error prediction. -/
theorem enumerable_getter_and_nonobject_boxing_are_boundaries :
    (evalObjectInitExpression 32 defaultSplitLimit (.objectLiteral [.spread (.variable "value")])
      {environment := [("value", .object 1)], objects := [objectPrototypeProjection [],
        {own := [([103], .accessor .unsupported .unsupported true true)]}]}).map Prod.fst = .error .unsupported ∧
    (evalObjectInitExpression 32 defaultSplitLimit (.objectLiteral [.spread (.variable "value")])
      {environment := [("value", .string [97])], objects := [objectPrototypeProjection []]}).map Prod.fst = .error .unsupported := by cbv

private def twoFields : OrdinaryObject :=
  {own := [([97], .data .null false true false), ([98], .data (.boolean false) true true true)]}
private theorem twoFields_wellFormed : WellFormedObject twoFields := by
  unfold WellFormedObject twoFields
  decide
private theorem orderAB : OwnStringKeyOrder twoFields [[97], [98]] := ownStringKeys_order twoFields twoFields_wellFormed
private theorem orderBA : OwnStringKeyOrder twoFields [[98], [97]] := by
  refine ⟨by decide, ?_⟩
  intro key
  rw [← orderAB.complete key]
  simp [or_comm]

/-- Raw property-list order really differs. The proved equality is only the
extensional descriptor observation for EVERY UTF16 query key. -/
theorem every_legal_order_has_same_descriptors_not_same_raw_list (key : JSString) :
    (spreadFold twoFields [[97], [98]] emptyLiteralObject).own.lookup key =
      (spreadFold twoFields [[98], [97]] emptyLiteralObject).own.lookup key ∧
    (spreadFold twoFields [[97], [98]] emptyLiteralObject).own ≠
      (spreadFold twoFields [[98], [97]] emptyLiteralObject).own := by
  exact ⟨spreadFold_orders_extensional twoFields _ _ orderAB orderBA key, by decide⟩

theorem symbolic_runtime_copy_contract_for_every_order (extra : Nat) (state : State) (reference : Nat)
    (object : OrdinaryObject) (keys : List JSString)
    (found : state.objects[reference]? = some object) (ready : CopyReady object) (order : OwnStringKeyOrder object keys) :
    let allocated : State := {state with objects := state.objects ++ [emptyLiteralObject]}
    copyDataPropertiesInOrder (extra + keys.length + 1) state.objects.length reference keys allocated =
      .ok (spreadFreshState state object keys) ∧
    FreshObjectSpreadContract state (spreadFreshState state object keys) reference object (.object state.objects.length) :=
  copyDataPropertiesInOrder_fresh extra state reference object keys found ready order

/-- info: 'HonoLean.Upstream.ECMA2025.copyDataPropertiesInOrder_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.ECMA2025.copyDataPropertiesInOrder_fresh
/-- info: 'HonoLean.Upstream.ECMA2025.spreadFold_orders_extensional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.ECMA2025.spreadFold_orders_extensional
/-- info: 'HonoLean.Upstream.SourceSubset.evalObjectInit_spread_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.evalObjectInit_spread_fresh
/-- info: 'HonoLean.Upstream.SourceSubset.evalObjectInit_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.evalObjectInit_empty

end HonoLean.Upstream.SourceSubset.ObjectInitChecks
