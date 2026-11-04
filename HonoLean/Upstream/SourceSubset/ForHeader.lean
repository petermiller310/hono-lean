import HonoLean.Upstream.SourceSubset.PrivateControlParser
import HonoLean.Upstream.SourceSubset.Arithmetic

namespace HonoLean.Upstream.SourceSubset

/-- A source prefix ending at the opening brace. No body or closing brace is
inserted, parsed, executed, or claimed by this header representation. -/
structure ForHeader where
  initializers : List (String × Expr)
  condition : Expr
  incrementName : String
  deriving Repr

private def headerInitializers : Nat → List Token → Option (List (String × Expr) × List Token)
  | 0, _ => none
  | fuel + 1, tokens => do
    match skipTokenLines tokens with
    | .name name :: rest =>
      let rest ← match skipTokenLines rest with
        | .punctuation "=" :: rest => some rest
        | _ => none
      let (value, rest) ← parseRawExpressionTokens rest
      match skipTokenLines rest with
      | .punctuation ";" :: rest => some ([(name, value)], rest)
      | .punctuation "," :: rest =>
        let (tail, rest) ← headerInitializers fuel rest
        some ((name, value) :: tail, rest)
      | _ => none
    | _ => none

/-- Parse only `for (let ...; ...; name++) {` followed by EOF. The empty-body
Stmt is a validation projection for existing binding/TDZ checks ONLY; it is
never used as a substituted source body or passed to the loop evaluator. -/
def parseForHeader (text : String) (allowedBindings : List String)
    (allowedPrivateNames : List String := []) (allowThis : Bool := false) : Option ForHeader := do
  if !allowedBindings.all bindingNameAllowed then none else do
  let tokens ← tokenizeFragment text
  let rest ← match skipTokenLines tokens with | .name "for" :: rest => some rest | _ => none
  let rest ← match skipTokenLines rest with | .punctuation "(" :: rest => some rest | _ => none
  let rest ← match skipTokenLines rest with | .name "let" :: rest => some rest | _ => none
  let (initializers, rest) ← headerInitializers (tokens.length + 1) rest
  let (condition, rest) ← parseRawExpressionTokens rest
  let rest ← match skipTokenLines rest with | .punctuation ";" :: rest => some rest | _ => none
  -- No LineTerminator between the update operand and postfix ++.
  let (incrementName, rest) ← match skipTokenLines rest with
    | .name name :: .punctuation "++" :: rest => some (name, rest)
    | _ => none
  let rest ← match skipTokenLines rest with | .punctuation ")" :: rest => some rest | _ => none
  let rest ← match skipTokenLines rest with | .punctuation "{" :: rest => some rest | _ => none
  if !(skipTokenLines rest).isEmpty ||
      !statementAdmitted (.countedFor initializers condition incrementName []) allowedBindings allowedPrivateNames allowThis ||
      !initializers.all (fun entry => privateControlExpressionAllowed 65536 entry.2) ||
      !privateControlExpressionAllowed 65536 condition then none
  else some ⟨initializers, condition, incrementName⟩

/-- All newly declared names are removed before the first initializer. Earlier
new bindings then become available sequentially via initializeBindings. -/
def enterForHeader (fuel limit : Nat) (header : ForHeader) (before : State) : Except EvalError State :=
  initializeBindings fuel limit header.initializers
    {before with environment := withoutBindings before.environment (header.initializers.map Prod.fst)}

def testForHeader (fuel limit : Nat) (header : ForHeader) (before : State) : Except EvalError (Bool × State) := do
  let (value, after) ← evalExpression fuel limit header.condition before
  pure (truthy value, after)

/-- One postfix update's state effect, with the unused old value discarded.
No body execution, scope-leaving restore, or per-iteration cells are implied. -/
def advanceForHeader (header : ForHeader) (before : State) : Except EvalError State :=
  incrementVariable header.incrementName before

/-- Independent comparison outcome, without invoking the condition evaluator. -/
def NumericGuardOutcome (counter bound : Int) (result : Bool) : Prop :=
  (result = true ∧ counter < bound) ∨ (result = false ∧ bound ≤ counter)

structure HeaderGuardContract (before after : State) (counter bound : Int) (result : Bool) : Prop where
  outcome : NumericGuardOutcome counter bound result
  state : after = before

structure HeaderEntryContract (before after : State) (header : ForHeader) (values : List (String × Value)) : Prop where
  names : values.map Prod.fst = header.initializers.map Prod.fst
  environment : after.environment = values.reverse ++ withoutBindings before.environment (header.initializers.map Prod.fst)
  heap : after.heap = before.heap
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

/-- Exactly the first matching numeric lexical entry changes, retaining the
whole prefix and suffix, including any later shadowed same-name entry. -/
def FirstBindingIncrement (before after : List (String × Value)) (name : String) (value : Int) : Prop :=
  ∃ front suffix, name ∉ front.map Prod.fst ∧
    before = front ++ (name, .number value) :: suffix ∧
    after = front ++ (name, .number (value + 1)) :: suffix

structure HeaderIncrementContract (before after : State) (name : String) (value : Int) : Prop where
  binding : FirstBindingIncrement before.environment after.environment name value
  counter : after.environment.lookup name = some (.number (value + 1))
  otherBindings : ∀ other, other ≠ name → after.environment.lookup other = before.environment.lookup other
  heap : after.heap = before.heap
  objects : after.objects = before.objects
  privates : after.privates = before.privates
  functions : after.functions = before.functions
  sets : after.sets = before.sets
  thisValue : after.thisValue = before.thisValue

theorem testForHeader_evaluated (fuel limit : Nat) (header : ForHeader) (before after : State) (value : Value)
    (evaluated : evalExpression fuel limit header.condition before = .ok (value, after)) :
    testForHeader fuel limit header before = .ok (truthy value, after) := by
  simp [testForHeader, evaluated, bind, pure, Except.bind, Except.pure]

theorem testForHeader_numeric (extra limit : Nat) (header : ForHeader) (before : State)
    (counterName boundName : String) (counter bound : Int)
    (condition : header.condition = .compare .less (.variable counterName) (.variable boundName))
    (counterFound : before.environment.lookup counterName = some (.number counter))
    (boundFound : before.environment.lookup boundName = some (.number bound)) :
    testForHeader (extra + 4) limit header before = .ok (decide (counter < bound), before) := by
  simp [testForHeader, condition, evalExpression, lookupVariable, counterFound, boundFound,
    compareNumbers, bind, pure, Except.bind, Except.pure]

theorem numericGuardOutcome_decide (counter bound : Int) : NumericGuardOutcome counter bound (decide (counter < bound)) := by
  by_cases less : counter < bound
  · exact Or.inl ⟨by simp [less], less⟩
  · exact Or.inr ⟨by simp [less], by omega⟩

theorem testForHeader_numeric_satisfies (extra limit : Nat) (header : ForHeader) (before : State)
    (counterName boundName : String) (counter bound : Int)
    (condition : header.condition = .compare .less (.variable counterName) (.variable boundName))
    (counterFound : before.environment.lookup counterName = some (.number counter))
    (boundFound : before.environment.lookup boundName = some (.number bound)) :
    ∃ result after, testForHeader (extra + 4) limit header before = .ok (result, after) ∧
      HeaderGuardContract before after counter bound result :=
  ⟨_, _, testForHeader_numeric extra limit header before counterName boundName counter bound condition counterFound boundFound,
    numericGuardOutcome_decide counter bound, rfl⟩

/-- A single numeric initializer is an actual initializer evaluation, not an
assumed counter output. Any caller binding of the new name is shadowed. -/
theorem enterForHeader_one_numeric (extra limit : Nat) (header : ForHeader) (before : State)
    (name : String) (value : Int) (initializers : header.initializers = [(name, .number value)]) :
    let after := {before with environment := (name, .number value) :: withoutBindings before.environment [name]}
    enterForHeader (extra + 4) limit header before = .ok after ∧
      HeaderEntryContract before after header [(name, .number value)] := by
  constructor
  · simp [enterForHeader, initializers, initializeBindings, evalExpression, bind, pure, Except.bind, Except.pure]
  · exact ⟨by simp [initializers], by simp [initializers], rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem incrementEnvironment_first (name : String) (front suffix : List (String × Value))
    (value : Int) (absent : front.lookup name = none) :
    incrementEnvironment name (front ++ (name, .number value) :: suffix) =
      .ok (front ++ (name, .number (value + 1)) :: suffix) := by
  induction front with
  | nil => simp [incrementEnvironment]
  | cons head tail ih =>
    obtain ⟨key, prior⟩ := head
    have different : key ≠ name := by intro same; subst key; simp at absent
    have tailAbsent : tail.lookup name = none := by
      simpa [List.lookup_cons, beq_false_of_ne (Ne.symm different)] using absent
    simp [incrementEnvironment, different, ih tailAbsent, Except.map]

theorem advanceForHeader_numeric_satisfies (header : ForHeader) (before : State) (value : Int)
    (found : before.environment.lookup header.incrementName = some (.number value)) :
    ∃ after, advanceForHeader header before = .ok after ∧
      HeaderIncrementContract before after header.incrementName value := by
  obtain ⟨front, suffix, environment, earlier⟩ := List.lookup_eq_some_iff.mp found
  have absent : front.lookup header.incrementName = none := List.lookup_eq_none_iff.mpr earlier
  have notMember : header.incrementName ∉ front.map Prod.fst := by
    intro member
    obtain ⟨entry, atEntry, equal⟩ := List.mem_map.mp member
    have different := earlier entry atEntry
    simp [equal] at different
  let after : State := {before with environment := front ++ (header.incrementName, Value.number (value + 1)) :: suffix}
  refine ⟨after, ?_, ⟨⟨front, suffix, notMember, environment, rfl⟩, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · simp [advanceForHeader, incrementVariable, environment,
      incrementEnvironment_first header.incrementName front suffix value absent, after, bind, pure, Except.bind, Except.pure]
  · simp [after, List.lookup_append, absent]
  · intro other different
    simp [after, environment, List.lookup_append, List.lookup_cons, beq_false_of_ne different]

/-- One explicit update and retest. This concerns the supplied current header
State; it does not prove that an arbitrary body preserved the enclosing cell. -/
theorem advanceForHeader_then_test (extra limit : Nat) (header : ForHeader) (before : State)
    (boundName : String) (counter bound : Int)
    (condition : header.condition = .compare .less (.variable header.incrementName) (.variable boundName))
    (counterFound : before.environment.lookup header.incrementName = some (.number counter))
    (boundFound : before.environment.lookup boundName = some (.number bound))
    (different : boundName ≠ header.incrementName) :
    ∃ after, advanceForHeader header before = .ok after ∧
      HeaderIncrementContract before after header.incrementName counter ∧
      testForHeader (extra + 4) limit header after = .ok (decide (counter + 1 < bound), after) := by
  obtain ⟨after, advanced, contract⟩ := advanceForHeader_numeric_satisfies header before counter counterFound
  exact ⟨after, advanced, contract, testForHeader_numeric extra limit header after header.incrementName boundName
    (counter + 1) bound condition contract.counter ((contract.otherBindings boundName different).trans boundFound)⟩

/-- Native exact-integer interpretation additionally bounds the next value.
This predicate supplies no general Number coercion/rounding/signed-zero rule. -/
def HeaderIncrementDomain (value : Int) : Prop := Arithmetic.SafeInteger value ∧ Arithmetic.SafeInteger (value + 1)

theorem uint32_guard_increment_safe (counter bound : Nat) (inside : counter < bound) (bounded : bound ≤ 4294967295) :
    HeaderIncrementDomain (counter : Int) := by
  unfold HeaderIncrementDomain Arithmetic.SafeInteger Arithmetic.maximumSafeInteger
  omega

end HonoLean.Upstream.SourceSubset
