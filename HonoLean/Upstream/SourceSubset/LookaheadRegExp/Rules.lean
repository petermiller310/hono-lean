import HonoLean.Upstream.SourceSubset.LookaheadRegExp.Runtime
import HonoLean.Upstream.SourceSubset.RegExpConstructRules

set_option autoImplicit false
set_option maxRecDepth 8192
namespace HonoLean.Upstream.SourceSubset.LookaheadRegExp
open ECMA2025
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

def compiledRecord (lower upper : UInt16) (next : JSString) : Record :=
  ⟨LiteralLookahead.rawSource lower upper next, [], LiteralLookahead.code lower upper next⟩

theorem initialize_record_safe (lower upper : UInt16) (next : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : LiteralLookahead.SafeNext next) :
    initializeRecord (LiteralLookahead.rawSource lower upper next) [] = some (compiledRecord lower upper next) := by
  have parsed := LiteralLookahead.parse_complete _ _ (.lookahead lower upper next safeLower safeUpper ordered safeNext)
  simp only [initializeRecord, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [parsed]
  dsimp only [bind, Option.bind]
  rw [LiteralLookahead.compile_pattern]
  rfl

theorem well_formed (before : State) (coherent : Coherent before) : wellFormed before = true := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨coherent.allocated, coherent.unique⟩

theorem tags_allocated (before : State) (prototype : Nat) :
    taggedEntries (allocatedState before prototype) = taggedEntries before := rfl

theorem tags_constructed (before : State) (prototype : Nat) (record : Record) :
    taggedEntries (constructedState before prototype record) =
      (before.base.base.regexp.ambient.objects.length, .lookahead record) :: taggedEntries before := rfl

theorem coherent_constructed (before : State) (prototype : Nat) (record : Record) (coherent : Coherent before) :
    Coherent (constructedState before prototype record) := by
  constructor
  case allocated =>
    intro entry member
    rw [tags_constructed] at member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · change before.base.base.regexp.ambient.objects.length < (before.base.base.regexp.ambient.objects ++ [_]).length
      simp
    · have bound := coherent.allocated entry member
      change entry.1 < (before.base.base.regexp.ambient.objects ++ [_]).length
      simp only [List.length_append, List.length_singleton]
      omega
  case unique =>
    rw [tags_constructed]
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, coherent.unique⟩
    intro member
    obtain ⟨entry, member, identity⟩ := List.mem_map.mp member
    have bound := coherent.allocated entry member
    omega

/-- Structural preservation when a closed producer inserts its one fresh
record between two existing tagged-store segments. Heap/capture effects do not
alter record identity; freshness follows from the initial allocated bound. -/
theorem coherent_insert (before after : State) (left right : List (Nat × TaggedRecord)) (record : TaggedRecord)
    (oldTags : taggedEntries before = left ++ right)
    (newTags : taggedEntries after = left ++ (before.base.base.regexp.ambient.objects.length, record) :: right)
    (objects : after.base.base.regexp.ambient.objects.length = before.base.base.regexp.ambient.objects.length + 1)
    (coherent : Coherent before) : Coherent after := by
  have oldBound : ∀ entry ∈ left ++ right, entry.1 < before.base.base.regexp.ambient.objects.length := by
    intro entry member
    exact coherent.allocated entry (oldTags.symm ▸ member)
  have oldUnique : ((left ++ right).map Prod.fst).Nodup := oldTags ▸ coherent.unique
  have fresh : before.base.base.regexp.ambient.objects.length ∉ (left ++ right).map Prod.fst := by
    intro member
    obtain ⟨entry, member, identity⟩ := List.mem_map.mp member
    have bound := oldBound entry member
    omega
  constructor
  case allocated =>
    intro entry member
    rw [objects]
    rw [newTags] at member
    rcases List.mem_append.mp member with member | member
    · have bound := oldBound entry (List.mem_append_left _ member)
      omega
    · rcases List.mem_cons.mp member with rfl | member
      · simp
      · have bound := oldBound entry (List.mem_append_right _ member)
        omega
  case unique =>
    rw [newTags, List.map_append, List.map_cons]
    have front : (before.base.base.regexp.ambient.objects.length :: (left.map Prod.fst ++ right.map Prod.fst)).Nodup := by
      apply List.nodup_cons.mpr
      simpa only [List.map_append] using And.intro fresh oldUnique
    exact List.Perm.nodup List.perm_middle.symm front

theorem fresh_record (before : State) (prototype : Nat) (record : Record) :
    recordAt (constructedState before prototype record) before.base.base.regexp.ambient.objects.length = some (.lookahead record) := by
  rw [recordAt, tags_constructed]
  simp

theorem initialize_allocated_safe (before : State) (prototype : Nat) (lower upper : UInt16) (next : JSString)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : LiteralLookahead.SafeNext next) :
    initializeAllocated before.base.base.regexp.ambient.objects.length (LiteralLookahead.rawSource lower upper next)
      (allocatedState before prototype) =
      .ok (.object before.base.base.regexp.ambient.objects.length, constructedState before prototype (compiledRecord lower upper next)) := by
  have found : (before.base.base.regexp.ambient.objects ++ [uninitializedRegExpObject prototype])[before.base.base.regexp.ambient.objects.length]? =
      some (uninitializedRegExpObject prototype) := by simp
  have assigned := writable_data_preserves_attributes
    (before.base.base.regexp.ambient.objects ++ [uninitializedRegExpObject prototype]) before.base.base.regexp.ambient.objects.length
    (propertyFuel - 1) lastIndexKey (uninitializedRegExpObject prototype) .undefined (.number 0) false false found rfl
  have changed : {uninitializedRegExpObject prototype with own :=
      (putOwn lastIndexKey (.data (.number 0) true false false) (uninitializedRegExpObject prototype).own)} = initializedRegExpObject prototype := rfl
  rw [changed] at assigned
  have replaced : (before.base.base.regexp.ambient.objects ++ [uninitializedRegExpObject prototype]).set
      before.base.base.regexp.ambient.objects.length (initializedRegExpObject prototype) =
      before.base.base.regexp.ambient.objects ++ [initializedRegExpObject prototype] := by simp
  rw [replaced] at assigned
  have budget : propertyFuel - 1 + 1 = propertyFuel := by decide
  rw [budget] at assigned
  simp only [initializeAllocated, initialize_record_safe lower upper next safeLower safeUpper ordered safeNext,
    allocatedState, withAmbient, withBase, cacheWithAmbient, bind, Except.bind]
  rw [assigned]
  rfl

theorem constructor_safe (context : RegExpConstructContext) (before : State) (callee : Value)
    (constructor : RegExpConstructor) (prototypeObject : OrdinaryObject) (lower upper : UInt16) (next : JSString)
    (coherent : Coherent before) (separated : constructorTablesSeparated context before.base.base.regexp.ambient = true)
    (identity : constructorAt context.constructors callee = some constructor)
    (prototypeFound : before.base.base.regexp.ambient.objects[constructor.prototype]? = some prototypeObject)
    (safeLower : RangeRegExp.SafeEndpoint lower) (safeUpper : RangeRegExp.SafeEndpoint upper)
    (ordered : lower.toNat ≤ upper.toNat) (safeNext : LiteralLookahead.SafeNext next) :
    invokeConstructor context callee (.string (LiteralLookahead.rawSource lower upper next)) before =
      .ok (.object before.base.base.regexp.ambient.objects.length,
        constructedState before constructor.prototype (compiledRecord lower upper next)) := by
  simp only [invokeConstructor, well_formed before coherent, separated, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, identity, prototypeFound, bind, Except.bind]
  exact initialize_allocated_safe before constructor.prototype lower upper next safeLower safeUpper ordered safeNext

/-- Exact phase order for the retained actual New AST: the current callee is
saved before the multi-substitution template argument is evaluated. -/
theorem construct_saved (fuel limit : Nat) (context : PatternCacheContext) (callee : Expr) (argument : PatternCacheExpr)
    (before : State) (saved : Value) (ambient : SourceSubset.State) (argumentValue : Value) (after : State)
    (calleeRead : evalExpression fuel limit callee before.base.base.regexp.ambient = .ok (saved, ambient))
    (argumentRead : evalExpr fuel limit context argument (withAmbient before ambient) = .ok (argumentValue, after)) :
    evalExpr (fuel + 1) limit context (.construct callee argument) before =
      invokeConstructor context.label.iterators.constructors saved argumentValue after := by
  simp [evalExpr, calleeRead, argumentRead]

theorem template_refines (fuel limit : Nat) (context : PatternCacheContext) (head : JSString)
    (substitutions : List (Expr × JSString)) (before : State) :
    evalExpr (fuel + 1) limit context (.template head substitutions) before =
      ((evalPatternCacheExpr (fuel + 1) limit context (.template head substitutions) before.base).mapError Error.pattern).map
        (fun (value, base) => (value, withBase before base)) := by
  cases evaluated : evalPatternCacheTemplate fuel limit substitutions before.base <;>
    simp [evalExpr, evalPatternCacheExpr, evaluated]

theorem label_declaration_refines (fuel limit : Nat) (context : PatternCacheContext) (name method : String)
    (receiver : Expr) (literal : LabelRegExpLiteral) (before : State) :
    executeDeclaration (fuel + 1) limit context (.declare name (.labelMatch receiver method literal)) before =
      ((executeLabelMatch fuel limit context.label ⟨name, receiver, method, literal⟩ before.base).mapError
        (Error.pattern ∘ PatternCacheError.label)).map (withBase before) := by
  have same : runLabelMatch fuel limit context.label ⟨"", receiver, method, literal⟩ before.base =
      runLabelMatch fuel limit context.label ⟨name, receiver, method, literal⟩ before.base := rfl
  simp only [executeDeclaration, evalExpr, same, executeLabelMatch]
  cases evaluated : runLabelMatch fuel limit context.label ⟨name, receiver, method, literal⟩ before.base <;>
    simp [withAmbient, withBase, cacheWithAmbient]

end HonoLean.Upstream.SourceSubset.LookaheadRegExp
