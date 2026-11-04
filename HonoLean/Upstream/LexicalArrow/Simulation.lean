import HonoLean.Upstream.LexicalArrow.Rules

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace HonoLean.Upstream.LexicalArrow
open SourceSubset ECMA2025 GetPatternBody
attribute [local simp] bind pure Except.bind Except.pure Except.map Except.mapError

theorem evalData_ignores_legacy_data (fuel : Nat) :
    (∀ (limit : Nat) (context : PatternCacheContext) (expression : PatternCacheExpr)
      (lexical : Runtime) (replacement before : LabelMatchState),
      evalDataExpr fuel limit context expression (withData lexical replacement) before =
        evalDataExpr fuel limit context expression lexical before) ∧
    (∀ (limit : Nat) (substitutions : List (Expr × JSString))
      (lexical : Runtime) (replacement before : LabelMatchState),
      evalDataTemplate fuel limit substitutions (withData lexical replacement) before =
        evalDataTemplate fuel limit substitutions lexical before) ∧
    (∀ (limit : Nat) (context : PatternCacheContext) (reference : Nat) (elements : List PatternCacheExpr)
      (lexical : Runtime) (replacement before : LabelMatchState),
      evalDataElements fuel limit context reference elements (withData lexical replacement) before =
        evalDataElements fuel limit context reference elements lexical before) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | succ fuel ih =>
    obtain ⟨expressions, templates, elements⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro limit context expression lexical replacement before
      cases expression <;>
        simp only [evalDataExpr, expressions, templates, elements, withData_withData]
    · intro limit substitutions lexical replacement before
      cases substitutions <;> simp only [evalDataTemplate, templates, withData_withData]
    · intro limit context reference values lexical replacement before
      cases values <;> simp only [evalDataElements, expressions, elements]

theorem ReadsAgree_transport (world : Runtime) (data : LabelMatchState) (names : List String)
    (same : data.base.regexp.ambient.environment = world.data.base.regexp.ambient.environment)
    (agreement : ReadsAgree world names) : ReadsAgree (withData world data) names := by
  intro name member value found
  have binding := agreement name member value (by simpa only [withData, same] using found)
  change getBindingValue (world.environments.length + 1) (withData world data) world.current name = _
  exact (getBindingValue_store_congr _ (withData world data) world rfl rfl world.current name).trans binding

structure StoreExtension (before after : Runtime) : Prop where
  cells : ∀ (reference : Nat) (cell : Cell), before.cells[reference]? = some cell → after.cells[reference]? = some cell
  environments : ∀ (reference : Nat) (frame : Environment), before.environments[reference]? = some frame → after.environments[reference]? = some frame
  length : before.environments.length ≤ after.environments.length

theorem StoreExtension.refl (world : Runtime) : StoreExtension world world :=
  ⟨fun _ _ found => found, fun _ _ found => found, Nat.le_refl _⟩

theorem StoreExtension.trans (first middle last : Runtime) (left : StoreExtension first middle)
    (right : StoreExtension middle last) : StoreExtension first last :=
  ⟨fun reference cell found => right.cells reference cell (left.cells reference cell found),
   fun reference frame found => right.environments reference frame (left.environments reference frame found),
   Nat.le_trans left.length right.length⟩

theorem resolveBinding_extension (fuel : Nat) (before after : Runtime)
    (extension : StoreExtension before after) (environment : EnvironmentRef) (name : String) (reference : CellRef)
    (resolved : resolveBinding fuel before environment name = .ok reference) :
    resolveBinding fuel after environment name = .ok reference := by
  induction fuel generalizing environment with
  | zero => simp [resolveBinding] at resolved
  | succ fuel ih =>
    cases frameFound : before.environments[environment]? with
    | none => simp [resolveBinding, frameFound] at resolved
    | some frame =>
      have afterFound := extension.environments environment frame frameFound
      cases binding : frame.bindings.lookup name with
      | some cell =>
        simp [resolveBinding, frameFound, binding] at resolved
        subst reference
        simp [resolveBinding, afterFound, binding]
      | none =>
        cases parent : frame.parent with
        | none => simp [resolveBinding, frameFound, binding, parent] at resolved
        | some outer =>
          simp [resolveBinding, frameFound, binding, parent] at resolved
          simpa [resolveBinding, afterFound, binding, parent] using ih outer resolved

theorem resolveBinding_add_fuel (fuel extra : Nat) (world : Runtime)
    (environment : EnvironmentRef) (name : String) (reference : CellRef)
    (resolved : resolveBinding fuel world environment name = .ok reference) :
    resolveBinding (fuel + extra) world environment name = .ok reference := by
  induction fuel generalizing environment with
  | zero => simp [resolveBinding] at resolved
  | succ fuel ih =>
    cases frameFound : world.environments[environment]? with
    | none => simp [resolveBinding, frameFound] at resolved
    | some frame =>
      cases binding : frame.bindings.lookup name with
      | some cell =>
        simp [resolveBinding, frameFound, binding] at resolved
        subst reference
        simp [Nat.add_right_comm, Nat.add_assoc, resolveBinding, frameFound, binding]
      | none =>
        cases parent : frame.parent with
        | none => simp [resolveBinding, frameFound, binding, parent] at resolved
        | some outer =>
          simp [resolveBinding, frameFound, binding, parent] at resolved
          simpa [Nat.add_right_comm, Nat.add_assoc, resolveBinding, frameFound, binding, parent] using ih outer resolved

theorem getBindingValue_extension (fuel extra : Nat) (before after : Runtime)
    (extension : StoreExtension before after) (environment : EnvironmentRef) (name : String) (value : Value)
    (read : getBindingValue fuel before environment name = .ok value) :
    getBindingValue (fuel + extra) after environment name = .ok value := by
  cases resolved : resolveBinding fuel before environment name with
  | error error => simp [getBindingValue, resolved] at read
  | ok reference =>
    cases found : before.cells[reference]? with
    | none => simp [getBindingValue, resolved, found] at read
    | some cell =>
      have afterResolved := resolveBinding_add_fuel fuel extra after environment name reference
        (resolveBinding_extension fuel before after extension environment name reference resolved)
      have afterFound := extension.cells reference cell found
      cases contents : cell.value with
      | none => simp [getBindingValue, resolved, found, contents] at read
      | some observed =>
        simp [getBindingValue, resolved, found, contents] at read
        subst value
        simp [getBindingValue, afterResolved, afterFound, contents]

theorem reserve_extends (name : String) (before : Runtime) : StoreExtension before (reserveConstant name before).2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro reference cell found
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  · intro reference frame found
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  · simp [reserveConstant]

theorem declare_extends (name : String) (value : Value) (before : Runtime) : StoreExtension before (declareConstant name value before) := by
  refine ⟨?_, ?_, ?_⟩
  · intro reference cell found
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  · intro reference frame found
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
  · simp [declareConstant, withAmbient, withData]

theorem reserved_lookup_other (before : Runtime) (reserved name : String) (value : Value)
    (different : name ≠ reserved)
    (read : getBindingValue (before.environments.length + 1) before before.current name = .ok value) :
    getBindingValue (((reserveConstant reserved before).2).environments.length + 1)
      (reserveConstant reserved before).2 (reserveConstant reserved before).2.current name = .ok value := by
  have preserved := getBindingValue_extension (before.environments.length + 1) 0 before
    (reserveConstant reserved before).2 (reserve_extends reserved before) before.current name value read
  have differentBool : (name == reserved) = false := beq_eq_false_iff_ne.mpr different
  simpa [getBindingValue, resolveBinding, reserveConstant, List.lookup, differentBool] using preserved

theorem declared_lookup_same (before : Runtime) (name : String) (value : Value) :
    getBindingValue ((declareConstant name value before).environments.length + 1)
      (declareConstant name value before) (declareConstant name value before).current name = .ok value := by
  simp [getBindingValue, resolveBinding, declareConstant, withAmbient, withData, List.lookup]

theorem declared_lookup_other (before : Runtime) (reserved name : String) (bound value : Value)
    (different : name ≠ reserved)
    (read : getBindingValue (before.environments.length + 1) before before.current name = .ok value) :
    getBindingValue ((declareConstant reserved bound before).environments.length + 1)
      (declareConstant reserved bound before) (declareConstant reserved bound before).current name = .ok value := by
  have preserved := getBindingValue_extension (before.environments.length + 1) 0 before
    (declareConstant reserved bound before) (declare_extends reserved bound before) before.current name value read
  have differentBool : (name == reserved) = false := beq_eq_false_iff_ne.mpr different
  simpa [getBindingValue, resolveBinding, declareConstant, withAmbient, withData, List.lookup, differentBool] using preserved

def EnvironmentAgrees (world : Runtime) : Prop :=
  ∀ name value, world.data.base.regexp.ambient.environment.lookup name = some value →
    getBindingValue (world.environments.length + 1) world world.current name = .ok value

theorem declared_agrees (before : Runtime) (name : String) (value : Value) (agreement : EnvironmentAgrees before) :
    EnvironmentAgrees (declareConstant name value before) := by
  intro query observed found
  by_cases same : query = name
  · subst query
    simp [declareConstant, withAmbient, withData, cacheWithAmbient] at found
    subst observed
    exact declared_lookup_same before name value
  · have differentBool : (query == name) = false := beq_eq_false_iff_ne.mpr same
    simp [declareConstant, withAmbient, withData, cacheWithAmbient, List.lookup, differentBool] at found
    exact declared_lookup_other before name query value observed same (agreement query observed found)

theorem finish_reserved (before : Runtime) (name : String) (value : Value) (data : LabelMatchState) :
    finishConstant name before.cells.length value (withData (reserveConstant name before).2 data) =
      .ok (declareConstant name value (withData before data)) := by
  simp [finishConstant, initializeCell, reserveConstant, declareConstant, withAmbient, withData,
    cacheWithAmbient]

theorem EnvironmentAgrees.reads (world : Runtime) (names : List String) (agreement : EnvironmentAgrees world) :
    ReadsAgree world names := fun name _ value found => agreement name value found

theorem ReadsAgree.reserved (before : Runtime) (reserved : String) (names : List String)
    (agreement : ReadsAgree before names) (excluded : reserved ∉ names) :
    ReadsAgree (reserveConstant reserved before).2 names := by
  intro name member value found
  have different : name ≠ reserved := by intro same; subst name; exact excluded member
  exact reserved_lookup_other before reserved name value different (agreement name member value found)

theorem EnvironmentAgrees.transport (world : Runtime) (data : LabelMatchState)
    (same : data.base.regexp.ambient.environment = world.data.base.regexp.ambient.environment)
    (agreement : EnvironmentAgrees world) : EnvironmentAgrees (withData world data) := by
  intro name value found
  have binding := agreement name value (by simpa only [withData, same] using found)
  change getBindingValue (world.environments.length + 1) (withData world data) world.current name = _
  exact (getBindingValue_store_congr _ (withData world data) world rfl rfl world.current name).trans binding

theorem ReadsAgree.mono (world : Runtime) (names smaller : List String)
    (inclusion : ∀ name ∈ smaller, name ∈ names) (agreement : ReadsAgree world names) : ReadsAgree world smaller :=
  fun name member value found => agreement name (inclusion name member) value found

theorem ReadsAgree.append (world : Runtime) (left right : List String) :
    ReadsAgree world (left ++ right) ↔ ReadsAgree world left ∧ ReadsAgree world right := by
  constructor
  · intro agreement
    exact ⟨fun name member value found => agreement name (List.mem_append_left _ member) value found,
      fun name member value found => agreement name (List.mem_append_right _ member) value found⟩
  · intro agreement name member value found
    cases List.mem_append.mp member with
    | inl member => exact agreement.1 name member value found
    | inr member => exact agreement.2 name member value found

theorem ReadsAgree.flatMap {α : Type} (world : Runtime) (entries : List α) (read : α → List String) :
    ReadsAgree world (entries.flatMap read) ↔ ∀ entry ∈ entries, ReadsAgree world (read entry) := by
  constructor
  · intro agreement entry member name readMember value found
    exact agreement name (List.mem_flatMap.mpr ⟨entry, member, readMember⟩) value found
  · intro agreement name member value found
    obtain ⟨entry, member, readMember⟩ := List.mem_flatMap.mp member
    exact agreement entry member name readMember value found

end HonoLean.Upstream.LexicalArrow
