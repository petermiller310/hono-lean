import HonoLean.Upstream.NodeParamAssignment.Correctness

namespace HonoLean.Upstream.SearchEntry

open SourceSubset ECMA2025

def allKey : JSString := [65, 76, 76]

/-- Explicit module import correspondence. The actual initializer value is
proved separately; this predicate does not prove export/import linking. -/
def AllImportBinding (before : State) : Prop :=
  before.environment.lookup "METHOD_NAME_ALL" = some (.string allKey)

/-- A declaration's first local scope shadows any earlier same-name binding;
this structural relation does not invoke the source evaluator. -/
def boundState (before : State) (name : String) (value : Value) : State :=
  {before with environment := (name, value) :: withoutBindings before.environment [name]}

def collectorState (before : State) : State :=
  {boundState before "handlerSets" (.array before.heap.length) with heap := before.heap ++ [[]]}

def CollectorContract (before after : State) : Prop :=
  after = collectorState before ∧ before.heap[before.heap.length]? = none

def RowContract (before after : State) (value : Value) : Prop := after = boundState before "m" value

/-- Ordinary property lookup includes inherited descriptors. A truthful type
assertion supplies no runtime shape check. The fallback key/binding/read is
required only in the falsy-direct branch, never for a skipped ALL operand. -/
def Choice (before : State) (row : ObjectRef) (method : JSString) (chosen : Value) : Prop :=
  ∃ direct, getProperty propertyFuel before.objects row method = .ok direct ∧
    ((NodeParamAssignment.Truthy direct ∧ chosen = direct) ∨
      (¬ NodeParamAssignment.Truthy direct ∧ ∃ fallbackKey,
        before.environment.lookup "METHOD_NAME_ALL" = some (.string fallbackKey) ∧
        getProperty propertyFuel before.objects row fallbackKey = .ok chosen))

/-- Only normal-domain read admissibility. A desired selected value or future
capture is not an input. Skipped fallback lookup need not succeed or exist. -/
def ChoiceDomain (before : State) (row : ObjectRef) (method : JSString) : Prop :=
  ∃ direct, getProperty propertyFuel before.objects row method = .ok direct ∧
    (¬ NodeParamAssignment.Truthy direct → ∃ fallbackKey fallback,
      before.environment.lookup "METHOD_NAME_ALL" = some (.string fallbackKey) ∧
      getProperty propertyFuel before.objects row fallbackKey = .ok fallback)

def ChoiceContract (before after : State) (row : ObjectRef) (method : JSString) (chosen : Value) : Prop :=
  Choice before row method chosen ∧ after = boundState before "handlerSet" chosen

theorem bound_lookup_self (before : State) (name : String) (value : Value) :
    (boundState before name value).environment.lookup name = some value := by simp [boundState]

theorem bound_lookup_other (before : State) (name : String) (value : Value) (other : String)
    (different : other ≠ name) :
    (boundState before name value).environment.lookup other = before.environment.lookup other := by
  simp only [boundState, List.lookup_cons, beq_false_of_ne different]
  exact lookup_withoutBindings before.environment [name] other (by simpa using different)

theorem collector_found (before : State) :
    (collectorState before).heap[before.heap.length]? = some [] := by simp [collectorState]

theorem collector_other_array (before : State) (reference : Nat) (inside : reference < before.heap.length) :
    (collectorState before).heap[reference]? = before.heap[reference]? := List.getElem?_append_left inside

theorem collector_binding (before : State) :
    (collectorState before).environment.lookup "handlerSets" = some (.array before.heap.length) :=
  bound_lookup_self before "handlerSets" (.array before.heap.length)

end HonoLean.Upstream.SearchEntry
