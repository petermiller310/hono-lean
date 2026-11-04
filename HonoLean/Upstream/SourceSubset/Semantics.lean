import HonoLean.Upstream.SourceSubset.Values
import HonoLean.Upstream.ECMA2025.StringSearchSlice
import HonoLean.Upstream.ECMA2025.Objects
import HonoLean.Upstream.ECMA2025.StringSet
import Init.Data.List.SplitOn.Lemmas

namespace HonoLean.Upstream.SourceSubset

def defaultSplitLimit : Nat := 4294967295
def maximumStringLength : Nat := 9007199254740991
def LegalString (contents : JSString) : Prop := contents.length ≤ maximumStringLength

/-- A parsed zero-argument function and its frozen lexical value environment.
This is a closed/immutable-capture specialization, not general mutable lexical
cells, dynamic scope, `this`, generators, async functions or a full JS realm. -/
structure FunctionDefinition where
  program : NoArgFunction
  environment : List (String × Value) := []
  deriving Repr

/-- The supported private element kinds are stored with each value. A method
cannot be made writable by replacing its function value, and a data field
containing a function remains writable. Accessors are outside this subset. -/
inductive PrivateElement where
  | data (value : Value)
  | method (value : Value)
  deriving Repr, DecidableEq

def PrivateElement.value : PrivateElement → Value
  | .data value | .method value => value

@[simp] theorem PrivateElement.data_value (value : Value) : (PrivateElement.data value).value = value := rfl
@[simp] theorem PrivateElement.method_value (value : Value) : (PrivateElement.method value).value = value := rfl

def dataElements (fields : List (Nat × Value)) : List (Nat × PrivateElement) :=
  fields.map (fun (identity, value) => (identity, .data value))

/-- Opaque lexical identities and tagged own private elements. Public and
prototype properties never provide a private brand. -/
structure PrivateStore where
  names : List (String × Nat) := []
  elements : List (Nat × List (Nat × PrivateElement)) := []
  deriving Repr, DecidableEq

/-- Read-only value observation for existing read contracts. This is computed
from the tagged store, never a second cache or a way to overwrite kinds. -/
def PrivateStore.slots (store : PrivateStore) : List (Nat × List (Nat × Value)) :=
  store.elements.map (fun (owner, fields) =>
    (owner, fields.map (fun (identity, element) => (identity, element.value))))

/-- Explicit data-only construction for fixtures/legacy admitted data stores.
Mixed stores must retain their raw tags rather than round-trip through slots. -/
def PrivateStore.ofData (names : List (String × Nat)) (slots : List (Nat × List (Nat × Value))) : PrivateStore :=
  ⟨names, slots.map (fun (owner, fields) => (owner, dataElements fields))⟩

theorem lookup_map_values {α β : Type} (entries : List (Nat × α)) (f : α → β) (identity : Nat) :
    (entries.map (fun (key, value) => (key, f value))).lookup identity =
      (entries.lookup identity).map f := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    by_cases equal : identity == key
    · simp [List.lookup, equal]
    · simp [List.lookup, equal, ih]

theorem PrivateStore.slots_lookup (store : PrivateStore) (owner : Nat) :
    store.slots.lookup owner = (store.elements.lookup owner).map
      (fun fields => fields.map (fun (identity, element) => (identity, element.value))) :=
  lookup_map_values store.elements _ owner

theorem PrivateStore.slots_lookup_none_iff (store : PrivateStore) (owner : Nat) :
    store.slots.lookup owner = none ↔ store.elements.lookup owner = none := by
  rw [store.slots_lookup]
  cases store.elements.lookup owner <;> simp

@[simp] theorem PrivateStore.ofData_slots (names : List (String × Nat)) (slots : List (Nat × List (Nat × Value))) :
    (PrivateStore.ofData names slots).slots = slots := by
  simp [PrivateStore.ofData, PrivateStore.slots, dataElements, List.map_map, Function.comp_def]

structure State where
  environment : List (String × Value) := []
  thisValue : Value := .undefined
  heap : List (List Value) := []
  objects : ECMA2025.ObjectHeap := []
  functions : List FunctionDefinition := []
  /-- Compact ordered live entries. Native Set interpretation requires the
  constructor/add-history uniqueness invariant; arbitrary lists may duplicate. -/
  sets : List (List JSString) := []
  privates : PrivateStore := {}
  deriving Repr

inductive EvalError where
  | exhausted | unsupported | missingVariable | invalidReference | missingReturn
  | objectError (error : ECMA2025.ObjectError)
  | privateScope | privateBrand
  | privateReadOnly
  deriving Repr, DecidableEq

def lookupVariable (state : State) (name : String) : Except EvalError Value :=
  match state.environment.lookup name with
  | some value => .ok value
  | none =>
    if name = "Object" then .ok .objectConstructor
    else if name = "Set" then .ok .setConstructor else .error .missingVariable

/-- Explicit ambient standard-builtin interpretation, respecting local
bindings first. Property lookup, global accessors and mutable Object.create
dispatch are outside the subset; this condition is not a whole-realm proof. -/
def StandardObjectBinding (state : State) : Prop :=
  state.environment.lookup "Object" = none ∨
    state.environment.lookup "Object" = some .objectConstructor

/-- Ambient constructor interpretation only. Standard Set/add/iterator lookup
and successful native resource behavior remain separate interpretation premises. -/
def StandardSetBinding (state : State) : Prop :=
  state.environment.lookup "Set" = none ∨
    state.environment.lookup "Set" = some .setConstructor

/-- Valid ordinary-object owners only. Proxy/exotic embedding is outside this
model. Same-spelling names in different class contexts use different stamps. -/
def privateGet (receiver : Value) (spelling : String) (state : State) : Except EvalError Value := do
  let identity ← match state.privates.names.lookup spelling with
    | none => .error .privateScope
    | some identity => .ok identity
  match receiver with
  | .object owner =>
    match state.objects[owner]? with
    | none => .error .invalidReference
    | some _ =>
      match state.privates.slots.lookup owner with
      | none => .error .privateBrand
      | some fields =>
        match fields.lookup identity with
        | none => .error .privateBrand
        | some value => .ok value
  | _ => .error .privateBrand

theorem privateGet_field (state : State) (owner identity : Nat) (spelling : String)
    (object : ECMA2025.OrdinaryObject) (fields : List (Nat × Value)) (value : Value)
    (lexical : state.privates.names.lookup spelling = some identity)
    (ownerFound : state.objects[owner]? = some object)
    (brand : state.privates.slots.lookup owner = some fields)
    (field : fields.lookup identity = some value) :
    privateGet (.object owner) spelling state = .ok value := by
  simp [privateGet, lexical, ownerFound, brand, field, bind, Except.bind]

/-- Replace the first matching element only. The surrounding private record
order and every other element, including method tags, are preserved. -/
def replacePrivateData (identity : Nat) (value : Value) :
    List (Nat × PrivateElement) → List (Nat × PrivateElement)
  | [] => []
  | (key, element) :: rest =>
    if identity == key then (key, .data value) :: rest
    else (key, element) :: replacePrivateData identity value rest

def replacePrivateOwner (owner identity : Nat) (value : Value) :
    List (Nat × List (Nat × PrivateElement)) → List (Nat × List (Nat × PrivateElement))
  | [] => []
  | (key, fields) :: rest =>
    if owner == key then (key, replacePrivateData identity value fields) :: rest
    else (key, fields) :: replacePrivateOwner owner identity value rest

def writePrivateDataState (state : State) (owner identity : Nat) (value : Value) : State :=
  {state with
    privates := {state.privates with
      elements := replacePrivateOwner owner identity value state.privates.elements}}

/-- Private PutValue checks the current receiver/brand/kind after RHS effects.
It never uses public setters, prototypes or extensibility. The identity was
already resolved by reference evaluation; it is not looked up again here. -/
def privateSet (receiver : Value) (identity : Nat) (value : Value) (state : State) : Except EvalError State := do
  match receiver with
  | .object owner =>
    match state.objects[owner]? with
    | none => .error .invalidReference
    | some _ =>
      match state.privates.elements.lookup owner with
      | none => .error .privateBrand
      | some fields =>
        match fields.lookup identity with
        | none => .error .privateBrand
        | some (.method _) => .error .privateReadOnly
        | some (.data _) => .ok (writePrivateDataState state owner identity value)
  | _ => .error .privateBrand

theorem privateSet_data (state : State) (owner identity : Nat) (value old : Value)
    (object : ECMA2025.OrdinaryObject) (fields : List (Nat × PrivateElement))
    (allocated : state.objects[owner]? = some object)
    (brand : state.privates.elements.lookup owner = some fields)
    (field : fields.lookup identity = some (.data old)) :
    privateSet (.object owner) identity value state = .ok (writePrivateDataState state owner identity value) := by
  simp [privateSet, allocated, brand, field]

theorem privateSet_method (state : State) (owner identity : Nat) (value old : Value)
    (object : ECMA2025.OrdinaryObject) (fields : List (Nat × PrivateElement))
    (allocated : state.objects[owner]? = some object)
    (brand : state.privates.elements.lookup owner = some fields)
    (field : fields.lookup identity = some (.method old)) :
    privateSet (.object owner) identity value state = .error .privateReadOnly := by
  simp [privateSet, allocated, brand, field]

/-- Standard single-code-unit String.prototype.split, with its default limit.
Methods/realm are modeled as standard intrinsics, not mutable JS property lookup. -/
def intrinsic (limit : Nat) (receiver : Value) (method : String) (args : List Value)
    (state : State) : Except EvalError (Value × State) :=
  match receiver, method, args with
  | .string contents, "split", [.string [separator]] =>
    let parts := (contents.splitOn separator).take limit
    .ok (.array state.heap.length,
      {state with heap := state.heap ++ [parts.map Value.string]})
  | .array reference, "shift", [] =>
    match state.heap[reference]? with
    | none => .error .invalidReference
    | some elements =>
      .ok (elements.headD .undefined,
        {state with heap := state.heap.set reference elements.tail})
  | .array reference, "push", values =>
    match state.heap[reference]? with
    | none => .error .invalidReference
    | some elements =>
      .ok (.number (Int.ofNat (elements.length + values.length)),
        {state with heap := state.heap.set reference (elements ++ values)})
  | .array reference, "concat", [.array argument] =>
    match state.heap[reference]?, state.heap[argument]? with
    | some left, some right =>
      .ok (.array state.heap.length, {state with heap := state.heap ++ [left ++ right]})
    | _, _ => .error .invalidReference
  | .array reference, "concat", [argument] =>
    match state.heap[reference]? with
    | some left => .ok (.array state.heap.length, {state with heap := state.heap ++ [left ++ [argument]]})
    | none => .error .invalidReference
  | .string contents, "indexOf", [.string [separator], .number position] =>
    .ok (.number (ECMA2025.stringIndexOf contents separator position), state)
  | .string contents, "slice", [.number start] =>
    .ok (.string (ECMA2025.stringSlice contents start none), state)
  | .string contents, "slice", [.number start, .number stop] =>
    .ok (.string (ECMA2025.stringSlice contents start (some stop)), state)
  | .objectConstructor, "create", [.null] =>
    let allocated := ECMA2025.createNull state.objects
    .ok (.object allocated.1, {state with objects := allocated.2})
  | .objectConstructor, "hasOwn", [.object reference, .string key] =>
    ((ECMA2025.hasOwn state.objects reference key).mapError .objectError).map
      (fun present => (.boolean present, state))
  | .set reference, "add", [.string key] =>
    match state.sets[reference]? with
    | none => .error .invalidReference
    | some entries =>
      .ok (.set reference, {state with sets := state.sets.set reference (ECMA2025.StringSet.add entries key)})
  | _, _, _ => .error .unsupported

/-- Prototype traversal has an explicit model budget, separate from syntax
execution. Long/cyclic chains can exhaust; no full JavaScript claim is made. -/
def propertyFuel : Nat := 32

inductive PreparedMethod where
  | standard (receiver : Value) (method : String)
  | member (receiver callee : Value)
  deriving Repr, DecidableEq

/-- Base/member preparation precedes arguments. Standard rules denote frozen
admitted intrinsic lookup, NOT general mutable Array/String/Set descriptors.
Object-member Get uses the declared ordinary-object model before arguments;
noncallable validation is deferred. Nullish receivers fail before arguments.
Other boxing/lookup domains reject without a full native-exception claim. -/
@[simp] def prepareMethod (receiver : Value) (method : String) (state : State) :
    Except EvalError PreparedMethod :=
  match receiver with
  | .null | .undefined => .error .unsupported
  | .object reference =>
    ((ECMA2025.getProperty propertyFuel state.objects reference
      (method.toList.map (fun char => UInt16.ofNat char.toNat))).mapError .objectError).map
        (PreparedMethod.member receiver)
  | .array reference =>
    match state.heap[reference]? with
    | none => .error .invalidReference
    | some _ =>
      if method == "push" || method == "shift" || method == "concat" then .ok (.standard receiver method)
      else .error .unsupported
  | .set reference =>
    match state.sets[reference]? with
    | none => .error .invalidReference
    | some _ => if method == "add" then .ok (.standard receiver method) else .error .unsupported
  | .string _ =>
    if method == "split" || method == "indexOf" || method == "slice" then
      .ok (.standard receiver method) else .error .unsupported
  | .objectConstructor =>
    if method == "create" || method == "hasOwn" then .ok (.standard receiver method) else .error .unsupported
  | _ => .error .unsupported

theorem prepare_array_push (state : State) (reference : Nat) (elements : List Value)
    (found : state.heap[reference]? = some elements) :
    prepareMethod (.array reference) "push" state = .ok (.standard (.array reference) "push") := by
  simp [found]

/-- Exact signed-integer comparisons. Native interpretation is restricted to
the safe-integer values reachable in the declared source slice. -/
def compareNumbers : NumericComparison → Int → Int → Bool
  | .less, left, right => decide (left < right)
  | .lessEqual, left, right => decide (left ≤ right)

/-- Finite safe-integer/value specialization of ToBoolean. NaN, infinities,
signed zero and unrepresented exotic values are outside this value domain. -/
@[simp] def truthy : Value → Bool
  | .string contents => !contents.isEmpty
  | .number value => decide (value ≠ 0)
  | .boolean value => value
  | .null | .undefined => false
  | .array _ | .object _ | .objectConstructor | .function _ | .set _ | .setConstructor => true

@[simp] def isNullish : Value → Bool
  | .null | .undefined => true
  | _ => false

/-- Supported read domains: object references with already-primitive string
keys, or the previous array/nonnegative-integer index case. No ToPropertyKey
coercion, primitive boxing or general receiver/exception semantics is assumed. -/
@[simp] def readProperty (receiver key : Value) (state : State) : Except EvalError Value :=
  match receiver, key with
  | .object reference, .string name =>
    (ECMA2025.getProperty propertyFuel state.objects reference name).mapError .objectError
  | .array reference, .number (.ofNat index) =>
    match state.heap[reference]? with
    | some elements => .ok (elements[index]?.getD .undefined)
    | none => .error .invalidReference
  | .array reference, .string [108, 101, 110, 103, 116, 104] =>
    match state.heap[reference]? with
    | some elements => .ok (.number (Int.ofNat elements.length))
    | none => .error .invalidReference
  | _, _ => .error .unsupported

/-- Stable standard dense-array/Set iteration only. Strings are intentionally
unsupported: their native iterator uses code points, unlike this UTF-16 storage.
Generic iterator hooks, interleaved mutation and IteratorClose are outside.
The compact Set observation is refined by the separate indexed-step model. -/
def iterableValues (value : Value) (state : State) : Except EvalError (List Value) :=
  match value with
  | .set reference =>
    match state.sets[reference]? with
    | none => .error .invalidReference
    | some entries => .ok ((ECMA2025.StringSet.values entries).map Value.string)
  | .array reference =>
    match state.heap[reference]? with
    | none => .error .invalidReference
    | some entries => .ok entries
  | _ => .error .unsupported

/-- Own dense literal element creation, distinct from calling mutable push or
ordinary inherited setters. Native interpretation additionally restricts the
output count to the Array-index range and assumes successful allocation. -/
def appendLiteralElements (reference : Nat) (elements : List Value) (state : State) :
    Except EvalError State :=
  match state.heap[reference]? with
  | none => .error .invalidReference
  | some prior => .ok {state with heap := state.heap.set reference (prior ++ elements)}

/-- Intrinsic realm Object.prototype address. A successful allocation requires
an existing root cell; native interpretation must identify it with that realm's
intrinsic prototype, rather than merely any arbitrary mathematical object. -/
def ordinaryObjectPrototype : Nat := 0

def emptyLiteralObject : ECMA2025.OrdinaryObject :=
  ⟨[], some ordinaryObjectPrototype, true⟩

def createLiteralObject (state : State) : Except EvalError (Value × State) :=
  match state.objects[ordinaryObjectPrototype]? with
  | none => .error .invalidReference
  | some _ => .ok (.object state.objects.length,
      {state with objects := state.objects ++ [emptyLiteralObject]})

theorem createLiteralObject_of_root (state : State) (root : ECMA2025.OrdinaryObject)
    (found : state.objects[0]? = some root) :
    createLiteralObject state = .ok (.object state.objects.length,
      {state with objects := state.objects ++ [emptyLiteralObject]}) := by
  simp [createLiteralObject, ordinaryObjectPrototype, found]

/-- ComputedPropertyName converts the key before evaluating the field value.
Only already-primitive strings are supported; no effectful coercion is assumed. -/
def literalPropertyName : Value → Except EvalError JSString
  | .string name => .ok name
  | _ => .error .unsupported

/-- Own W/E/C data definition, never inherited Set/setter dispatch. Fresh
literal fields are extensible or replace configurable own fields. Other own
descriptor restrictions reject; property enumeration order is not observed. -/
def defineLiteralProperty (reference : Nat) (key : JSString) (value : Value) (state : State) :
    Except EvalError State := do
  match state.objects[reference]? with
  | none => .error .invalidReference
  | some object =>
    let allowed := match object.own.lookup key with
      | none => object.extensible
      | some (.data _ _ _ configurable) | some (.accessor _ _ _ configurable) => configurable
    if allowed then
      return {state with objects := state.objects.set reference (ECMA2025.newDataObject object key value)}
    else .error .unsupported

def incrementEnvironment (name : String) : List (String × Value) →
    Except EvalError (List (String × Value))
  | [] => .error .missingVariable
  | (key, value) :: rest =>
    if key = name then
      match value with
      | .number value => .ok ((key, .number (value + 1)) :: rest)
      | _ => .error .unsupported
    else (incrementEnvironment name rest).map ((key, value) :: ·)

def incrementVariable (name : String) (state : State) : Except EvalError State := do
  let environment ← incrementEnvironment name state.environment
  return {state with environment}

mutual
  def evalExpression : Nat → Nat → Expr → State → Except EvalError (Value × State)
    | 0, _, _, _ => .error .exhausted
    | fuel + 1, limit, expression, state => do
      match expression with
      | .variable name => return (← lookupVariable state name, state)
      | .this => return (state.thisValue, state)
      | .string contents => return (.string contents, state)
      | .number value => return (.number value, state)
      | .null => return (.null, state)
      | .boolean value => return (.boolean value, state)
      | .index receiver key =>
        let (receiver, state) ← evalExpression fuel limit receiver state
        let (key, state) ← evalExpression fuel limit key state
        let value ← readProperty receiver key state
        return (value, state)
      | .property receiver key =>
        let (receiver, state) ← evalExpression fuel limit receiver state
        let value ← readProperty receiver (.string key) state
        return (value, state)
      | .privateProperty receiver spelling =>
        let (receiver, state) ← evalExpression fuel limit receiver state
        let value ← privateGet receiver spelling state
        return (value, state)
      | .optionalIndex receiver key =>
        let (receiver, state) ← evalExpression fuel limit receiver state
        if isNullish receiver then return (.undefined, state)
        else
          let (key, state) ← evalExpression fuel limit key state
          let value ← readProperty receiver key state
          return (value, state)
      | .call receiver method args =>
        let (receiver, state) ← evalExpression fuel limit receiver state
        let prepared ← prepareMethod receiver method state
        let (args, state) ← evalArguments fuel limit args state
        invokePrepared fuel limit prepared args state
      | .invoke callee arguments =>
        let (callee, state) ← evalExpression fuel limit callee state
        let (arguments, state) ← evalArguments fuel limit arguments state
        match callee, arguments with
        | .function reference, [] =>
          match state.functions[reference]? with
          | none => .error .invalidReference
          | some definition =>
            let caller := state.environment
            let (value, state) ← evalExpression fuel limit definition.program.body
              {state with environment := definition.environment}
            return (value, {state with environment := caller})
        | _, _ => .error .unsupported
      | .construct callee _ arguments =>
        -- Checked type-argument syntax is retained in the AST but has no
        -- runtime operation here; this is not a verified TypeScript eraser.
        let (callee, state) ← evalExpression fuel limit callee state
        let (arguments, state) ← evalArguments fuel limit arguments state
        match callee, arguments with
        | .setConstructor, [] =>
          return (.set state.sets.length, {state with sets := state.sets ++ [[]]})
        | _, _ => .error .unsupported
      | .arrayLiteral elements =>
        -- Allocate first, so nested element allocations cannot steal its ID.
        let reference := state.heap.length
        let state := {state with heap := state.heap ++ [[]]}
        let state ← evalLiteralElements fuel limit reference elements state
        return (.array reference, state)
      | .objectLiteral fields =>
        let (value, state) ← createLiteralObject state
        match value with
        | .object reference =>
          let state ← evalObjectFields fuel limit reference fields state
          return (.object reference, state)
        | _ => .error .unsupported
      | .preIncrement name =>
        -- Native interpretation requires a mutable safe-integer binding.
        -- Flat value environments do not prove const/module shared-cell rules.
        let state ← incrementVariable name state
        let value ← lookupVariable state name
        return (value, state)
      | .strictEqual left right =>
        let (left, state) ← evalExpression fuel limit left state
        let (right, state) ← evalExpression fuel limit right state
        return (.boolean (decide (left = right)), state)
      | .compare operation left right =>
        let (left, state) ← evalExpression fuel limit left state
        let (right, state) ← evalExpression fuel limit right state
        match left, right with
        | .number left, .number right =>
          return (.boolean (compareNumbers operation left right), state)
        | _, _ => .error .unsupported
      | .subtract left right =>
        -- Operand effects occur left-to-right before numeric specialization.
        -- Values are mathematical Ints. Native Number interpretation needs
        -- exact safe integral operands/result, not general JS ToNumeric.
        let (left, state) ← evalExpression fuel limit left state
        let (right, state) ← evalExpression fuel limit right state
        match left, right with
        | .number left, .number right => return (.number (left - right), state)
        | _, _ => .error .unsupported
      | .conditional test yes no =>
        let (test, state) ← evalExpression fuel limit test state
        if truthy test then evalExpression fuel limit yes state
        else evalExpression fuel limit no state
      | .logicalNot value =>
        let (value, state) ← evalExpression fuel limit value state
        return (.boolean (!truthy value), state)
      | .logicalAnd left right =>
        let (left, state) ← evalExpression fuel limit left state
        if truthy left then evalExpression fuel limit right state
        else return (left, state)
      | .logicalOr left right =>
        let (left, state) ← evalExpression fuel limit left state
        if truthy left then return (left, state)
        else evalExpression fuel limit right state
      | .typeAssertion value _ =>
        -- Retained syntax is explicitly erased in this declared model. This
        -- is not a runtime shape guard or a full TS compiler/typechecker proof.
        evalExpression fuel limit value state
      | .nullish left right =>
        let (left, state) ← evalExpression fuel limit left state
        if isNullish left then evalExpression fuel limit right state
        else return (left, state)

  def evalArguments : Nat → Nat → List Expr → State → Except EvalError (List Value × State)
    | 0, _, _, _ => .error .exhausted
    | _ + 1, _, [], state => .ok ([], state)
    | fuel + 1, limit, head :: tail, state => do
      let (value, state) ← evalExpression fuel limit head state
      let (values, state) ← evalArguments fuel limit tail state
      return (value :: values, state)

  /-- The prepared standard method retains the array reference, not a contents
  snapshot. Push reads current contents AFTER argument effects. Object methods
  support the existing zero-argument/no-this parsed function specialization. -/
  @[simp] def invokePrepared : Nat → Nat → PreparedMethod → List Value → State → Except EvalError (Value × State)
    | _, limit, .standard receiver method, arguments, state => intrinsic limit receiver method arguments state
    | 0, _, .member _ _, _, _ => .error .exhausted
    | fuel + 1, limit, .member _ (.function reference), [], state =>
      match state.functions[reference]? with
      | none => .error .invalidReference
      | some definition => do
        let caller := state.environment
        let (value, state) ← evalExpression fuel limit definition.program.body
          {state with environment := definition.environment}
        return (value, {state with environment := caller})
    | _, _, .member _ _, _, _ => .error .unsupported

  def evalLiteralElements : Nat → Nat → Nat → List (Bool × Expr) → State → Except EvalError State
    | 0, _, _, _, _ => .error .exhausted
    | _ + 1, _, _, [], state => .ok state
    | fuel + 1, limit, reference, (spread, expression) :: rest, state => do
      let (value, state) ← evalExpression fuel limit expression state
      let elements ← if spread then iterableValues value state else .ok [value]
      let state ← appendLiteralElements reference elements state
      evalLiteralElements fuel limit reference rest state

  def evalObjectFields : Nat → Nat → Nat → List (Expr × Expr) → State → Except EvalError State
    | 0, _, _, _, _ => .error .exhausted
    | _ + 1, _, _, [], state => .ok state
    | fuel + 1, limit, reference, (keyExpression, valueExpression) :: rest, state => do
      let (keyValue, state) ← evalExpression fuel limit keyExpression state
      let key ← literalPropertyName keyValue
      let (value, state) ← evalExpression fuel limit valueExpression state
      let state ← defineLiteralProperty reference key value state
      evalObjectFields fuel limit reference rest state
end

/-- Explicit erasure in this declared grammar model, not a TypeScript compiler
adequacy theorem or a justification of the asserted runtime object shape. -/
theorem typeAssertion_erases (fuel limit : Nat) (value : Expr) (annotation : TypeSyntax) (state : State) :
    evalExpression (fuel + 1) limit (.typeAssertion value annotation) state =
      evalExpression fuel limit value state := by simp only [evalExpression]

/-- Captured raw base/key values. Domain validation and any future property-key
interpretation belong to PutValue after the RHS, not reference evaluation. -/
structure PropertyReference where
  receiver : Value
  key : Value
  deriving Repr, DecidableEq

/-- The shared assignment evaluator distinguishes public property references
from private references with an already resolved lexical identity. -/
inductive AssignmentReference where
  | property (reference : PropertyReference)
  | privateField (receiver : Value) (identity : Nat)
  deriving Repr, DecidableEq

/-- Capture only the raw base and key, without checking receiver/key domains or
reading the destination property's value/descriptor. In particular, an invalid
outer base does not prevent RHS evaluation after key-expression evaluation. -/
def evalReference : Nat → Nat → Expr → State → Except EvalError (PropertyReference × State)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, limit, target, state => do
    match target with
    | .index receiver key =>
      let (receiver, state) ← evalExpression fuel limit receiver state
      let (key, state) ← evalExpression fuel limit key state
      return (⟨receiver, key⟩, state)
    | .property receiver name =>
      let (receiver, state) ← evalExpression fuel limit receiver state
      return (⟨receiver, .string name⟩, state)
    | _ => .error .unsupported

/-- Descriptor dispatch happens in the state after RHS evaluation. The supported
write domain is an object reference and primitive string key; other receiver
types and effectful key coercions reject here, without a generic JS TypeError
or ToPropertyKey adequacy claim. Errors do not expose an exception-state trace. -/
def putReference (reference : PropertyReference) (value : Value) (state : State) :
    Except EvalError State := do
  match reference.receiver, reference.key with
  | .object receiver, .string key =>
    let objects ← (ECMA2025.setProperty propertyFuel state.objects receiver key value).mapError .objectError
    return {state with objects}
  | _, _ => .error .unsupported

def evalAssignmentReference : Nat → Nat → Expr → State → Except EvalError (AssignmentReference × State)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, limit, target, before => do
    match target with
    | .privateProperty receiver spelling =>
      let (receiver, state) ← evalExpression fuel limit receiver before
      let identity ← match state.privates.names.lookup spelling with
        | some identity => .ok identity
        | none => .error .privateScope
      pure (.privateField receiver identity, state)
    | _ =>
      let (reference, state) ← evalReference (fuel + 1) limit target before
      pure (.property reference, state)

def putAssignmentReference (reference : AssignmentReference) (value : Value) (state : State) : Except EvalError State :=
  match reference with
  | .property reference => putReference reference value state
  | .privateField receiver identity => privateSet receiver identity value state

/-- Assignment evaluates its reference before its RHS, then performs descriptor
dispatch in the resulting state through that saved reference. Its value is the
RHS value. The object model's precise rejection is retained in objectError. -/
def executeAssignment : Nat → Nat → Assignment → State → Except EvalError (Value × State)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, limit, assignment, state => do
    let (reference, state) ← evalAssignmentReference fuel limit assignment.target state
    let (value, state) ← evalExpression fuel limit assignment.value state
    let state ← putAssignmentReference reference value state
    return (value, state)

def runAssignment (assignment : Assignment) (state : State)
    (limit : Nat := defaultSplitLimit) : Except EvalError (Value × State) :=
  executeAssignment 32 limit assignment state

inductive Completion where
  | normal (state : State)
  | returned (value : Value) (state : State)
  deriving Repr

/-- Remove newly scoped names before initialization, so an outer binding cannot
leak through a header/body declaration's temporal dead zone. -/
def withoutBindings (environment : List (String × Value)) (names : List String) :
    List (String × Value) := environment.filter (fun entry => !names.contains entry.1)

theorem lookup_withoutBindings (environment : List (String × Value)) (names : List String)
    (name : String) (outside : name ∉ names) :
    (withoutBindings environment names).lookup name = environment.lookup name := by
  induction environment with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    simp only [withoutBindings, List.contains_eq_mem] at ih
    by_cases removed : key ∈ names
    · have different : name ≠ key := by intro equal; exact outside (equal ▸ removed)
      have unequal : (name == key) = false := beq_eq_false_iff_ne.mpr different
      simp [withoutBindings, removed, List.lookup, unequal, ih]
    · simp [withoutBindings, removed, List.lookup, ih]

def initializeBindings : Nat → Nat → List (String × Expr) → State → Except EvalError State
  | 0, _, _, _ => .error .exhausted
  | _ + 1, _, [], state => .ok state
  | fuel + 1, limit, (name, initializer) :: rest, state => do
    let (value, state) ← evalExpression fuel limit initializer state
    initializeBindings fuel limit rest {state with environment := (name, value) :: state.environment}

def restoreCompletion (environment : List (String × Value)) : Completion → Completion
  | .normal state => .normal {state with environment}
  | .returned value state => .returned value {state with environment}

mutual
/-- Explicit bounded execution. The budget bounds syntax, nested calls and loop
iterations; callers of input-sized loops supply a sufficiently large budget.
The older short-function runners still use32 and make no loop-length claim. -/
def execute : Nat → Nat → List Stmt → State → Except EvalError Completion
  | 0, _, _, _ => .error .exhausted
  | _ + 1, _, [], state => .ok (.normal state)
  | fuel + 1, limit, head :: tail, state => do
    match head with
    | .declare name initializer | .typedDeclare name _ initializer | .mutableDeclare name _ initializer =>
      let (value, state) ← evalExpression fuel limit initializer state
      execute fuel limit tail {state with environment := (name, value) :: state.environment}
    | .evaluate expression =>
      let (_, state) ← evalExpression fuel limit expression state
      execute fuel limit tail state
    | .assign assignment =>
      let (_, state) ← executeAssignment fuel limit assignment state
      execute fuel limit tail state
    | .countedFor initializers condition incrementName body =>
      let outer := state.environment
      let state := {state with environment := withoutBindings outer (initializers.map Prod.fst)}
      let state ← initializeBindings fuel limit initializers state
      let completion ← executeFor fuel limit condition incrementName body state
      match restoreCompletion outer completion with
      | .normal state => execute fuel limit tail state
      | .returned value state => return .returned value state
    | .ret expression =>
      let (value, state) ← evalExpression fuel limit expression state
      return .returned value state
    | .branch condition body =>
      let (value, state) ← evalExpression fuel limit condition state
      if truthy value then
        match ← execute fuel limit body state with
        | .normal state => execute fuel limit tail state
        | .returned value state => return .returned value state
      else execute fuel limit tail state

/-- A generic tested counted loop. The condition is evaluated every iteration;
initializers belong to execute and run once. Body const bindings are fresh each
iteration and removed before the header binding is incremented. No closure may
observe mutable per-iteration lexical cells in this specialized value model. -/
def executeFor : Nat → Nat → Expr → String → List Stmt → State → Except EvalError Completion
  | 0, _, _, _, _, _ => .error .exhausted
  | fuel + 1, limit, condition, incrementName, body, state => do
    let (conditionValue, state) ← evalExpression fuel limit condition state
    if truthy conditionValue then
      let header := state.environment
      let bodyState := {state with environment := withoutBindings header (declaredNames body)}
      let completion ← execute fuel limit body bodyState
      match restoreCompletion header completion with
      | .returned value state => return .returned value state
      | .normal state =>
        let state ← incrementVariable incrementName state
        executeFor fuel limit condition incrementName body state
    else return .normal state
end

/-- Standalone block scope with an explicit execution budget. On successful
normal completion or return, all caller bindings are restored exactly; shared
heaps and the immutable function table retain the executed effects. Errors do
not carry an exception-state trace. -/
def runBlock (budget : Nat) (program : List Stmt) (state : State)
    (limit : Nat := defaultSplitLimit) : Except EvalError Completion := do
  let outer := state.environment
  let state := {state with environment := withoutBindings outer (declaredNames program)}
  let completion ← execute budget limit program state
  return restoreCompletion outer completion

def run (program : Function) (input : JSString) (limit : Nat := defaultSplitLimit) :
    Except EvalError (List Value) := do
  match ← execute 32 limit program.body {environment := [(program.parameter, .string input)]} with
  | .normal _ => .error .missingReturn
  | .returned (.array reference) state =>
    match state.heap[reference]? with
    | some elements => return elements
    | none => .error .invalidReference
  | .returned _ _ => .error .unsupported

/-- String-result observation using the same statement evaluator. The return
annotation is checked by parseString; this does not typecheck arbitrary ASTs. -/
def runString (program : Function) (input : JSString) (limit : Nat := defaultSplitLimit) :
    Except EvalError JSString := do
  match ← execute 32 limit program.body {environment := [(program.parameter, .string input)]} with
  | .normal _ => .error .missingReturn
  | .returned (.string contents) _ => return contents
  | .returned _ _ => .error .unsupported

/-- Preserve the returned value's identity and the entire resulting state.
Expression-bodied zero-argument functions introduce no parameter binding. -/
def runNoArg (program : NoArgFunction) (state : State)
    (limit : Nat := defaultSplitLimit) : Except EvalError (Value × State) :=
  evalExpression 32 limit program.body state

end HonoLean.Upstream.SourceSubset
