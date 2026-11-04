import HonoLean.Upstream.NodeParamLoop.Contract

namespace HonoLean.Upstream.NodeParamLoop

open SourceSubset ECMA2025

/-- ASTs of the actual saved-length source header and body. No list traversal
or desired loop result is hidden in these definitions. -/
def keyArray : Expr := .property (.variable "handlerSet") possibleKeysKey
def condition : Expr := .compare .less (.variable "i") (.variable "len")
def body : List Stmt :=
  [.declare "key" (.index keyArray (.variable "i")), .assign NodeParamAssignment.assignment]
def initializers : List (String × Expr) :=
  [("i", .number 0), ("len", .property keyArray lengthKey)]

def headerEnvironment (outer : List (String × Value)) (count length : Nat) : List (String × Value) :=
  [("len", .number (Int.ofNat length)), ("i", .number (Int.ofNat count))] ++
    withoutBindings outer ["i", "len"]

def bodyEnvironment (outer : List (String × Value)) (count length : Nat) (key : JSString) :
    List (String × Value) :=
  ("key", .string key) :: withoutBindings (headerEnvironment outer count length) ["key"]

theorem header_lookup_i (outer : List (String × Value)) (count length : Nat) :
    (headerEnvironment outer count length).lookup "i" = some (.number (Int.ofNat count)) := by
  simp [headerEnvironment, List.lookup]

theorem header_lookup_len (outer : List (String × Value)) (count length : Nat) :
    (headerEnvironment outer count length).lookup "len" = some (.number (Int.ofNat length)) := by
  simp [headerEnvironment]

theorem header_lookup_other (outer : List (String × Value)) (count length : Nat) (name : String)
    (notI : name ≠ "i") (notLen : name ≠ "len") :
    (headerEnvironment outer count length).lookup name = outer.lookup name := by
  have noI : (name == "i") = false := beq_eq_false_iff_ne.mpr notI
  have noLen : (name == "len") = false := beq_eq_false_iff_ne.mpr notLen
  have outside : name ∉ ["i", "len"] := by simp [notI, notLen]
  simpa [headerEnvironment, List.lookup, noI, noLen] using
    lookup_withoutBindings outer ["i", "len"] name outside

theorem body_lookup_key (outer : List (String × Value)) (count length : Nat) (key : JSString) :
    (bodyEnvironment outer count length key).lookup "key" = some (.string key) := by
  simp [bodyEnvironment]

theorem body_lookup_i (outer : List (String × Value)) (count length : Nat) (key : JSString) :
    (bodyEnvironment outer count length key).lookup "i" = some (.number (Int.ofNat count)) := by
  have preserved := lookup_withoutBindings (headerEnvironment outer count length) ["key"] "i" (by decide)
  simpa [bodyEnvironment, List.lookup, header_lookup_i] using preserved

theorem body_lookup_other (outer : List (String × Value)) (count length : Nat) (key : JSString)
    (name : String) (notI : name ≠ "i") (notLen : name ≠ "len") (notKey : name ≠ "key") :
    (bodyEnvironment outer count length key).lookup name = outer.lookup name := by
  have noKey : (name == "key") = false := beq_eq_false_iff_ne.mpr notKey
  have preserved := lookup_withoutBindings (headerEnvironment outer count length) ["key"] name (by simp [notKey])
  simpa [bodyEnvironment, List.lookup, noKey, header_lookup_other outer count length name notI notLen] using preserved

theorem increment_header (state : State) (outer : List (String × Value)) (count length : Nat)
    (environment : state.environment = headerEnvironment outer count length) :
    incrementVariable "i" state =
      .ok {state with environment := headerEnvironment outer (count + 1) length} := by
  simp [incrementVariable, environment, headerEnvironment, incrementEnvironment,
    Int.natCast_add, Except.map, bind, pure, Except.bind, Except.pure]

/-- The actual staged `i=0,len=handlerSet.possibleKeys.length` initialization.
Only initial binding/read/heap facts are premises; no desired initializer result
or future successful execution is assumed. The captured length is mathematical
list length, with native Array/safe-integer adequacy separately scoped. -/
theorem initialize_header (extra limit : Nat) (state : State) (handlerSet : ObjectRef)
    (keysArray : Nat) (keys : List JSString)
    (binding : state.environment.lookup "handlerSet" = some (.object handlerSet))
    (possibleKeys : getProperty propertyFuel state.objects handlerSet possibleKeysKey = .ok (.array keysArray))
    (keysFound : state.heap[keysArray]? = some (keys.map Value.string)) :
    initializeBindings (extra + 8) limit initializers
      {state with environment := withoutBindings state.environment ["i", "len"]} =
      .ok {state with environment := headerEnvironment state.environment 0 keys.length} := by
  have outerBinding : (withoutBindings state.environment ["i", "len"]).lookup "handlerSet" =
      some (.object handlerSet) := by
    rw [lookup_withoutBindings _ _ _ (by decide)]
    exact binding
  simp [initializers, initializeBindings, evalExpression, keyArray, lookupVariable,
    List.lookup, outerBinding, readProperty, possibleKeys, keysFound, lengthKey, headerEnvironment,
    Except.mapError, bind, pure, Except.bind, Except.pure]

theorem eval_condition (extra limit : Nat) (state : State) (outer : List (String × Value))
    (count length : Nat) (environment : state.environment = headerEnvironment outer count length) :
    evalExpression (extra + 3) limit condition state =
      .ok (.boolean (decide (count < length)), state) := by
  simp [condition, evalExpression, lookupVariable, environment, header_lookup_i, header_lookup_len,
    compareNumbers, bind, pure, Except.bind, Except.pure]

theorem eval_current_key (extra limit : Nat) (state : State) (handlerSet : ObjectRef)
    (keysArray count : Nat) (keys : List JSString) (key : JSString)
    (binding : state.environment.lookup "handlerSet" = some (.object handlerSet))
    (iteration : state.environment.lookup "i" = some (.number (Int.ofNat count)))
    (possibleKeys : getProperty propertyFuel state.objects handlerSet possibleKeysKey = .ok (.array keysArray))
    (keysFound : state.heap[keysArray]? = some (keys.map Value.string))
    (atKey : keys[count]? = some key) :
    evalExpression (extra + 4) limit (.index keyArray (.variable "i")) state =
      .ok (.string key, state) := by
  simp [evalExpression, keyArray, lookupVariable, binding, iteration, readProperty,
    possibleKeys, keysFound, atKey, Except.mapError, bind, pure, Except.bind, Except.pure]

/-- info: 'HonoLean.Upstream.NodeParamLoop.initialize_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initialize_header

end HonoLean.Upstream.NodeParamLoop
