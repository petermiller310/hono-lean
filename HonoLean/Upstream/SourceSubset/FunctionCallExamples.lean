import HonoLean.Upstream.SourceSubset.FunctionCall

namespace HonoLean.Upstream.SourceSubset.FunctionCallChecks

open ECMA2025
set_option maxRecDepth 65536

private def echo : Function := ⟨"echo", "value", [.ret (.variable "value")]⟩
private def second : Function := ⟨"second", "value", [.ret (.number 100)]⟩
private def captured : List (String × Value) := [("value", .number 99), ("captured", .number 13)]
private def names : List (String × Nat) := [("frozen", 99)]
private def methods : PrivateMethodTable := ⟨1, [⟨⟨"noop", [], .named "void", []⟩, [], []⟩]⟩
private def table : FunctionTable := ⟨2, [⟨echo, captured, names⟩, ⟨second, captured, names⟩]⟩
private def before : State :=
  {environment := [("f", .function 2), ("notCallable", .number 7),
      ("callees", .array 0), ("values", .array 1), ("this", .object 1)]
   thisValue := .object 0
   heap := [[.function 2, .function 3], [.number 7, .number 9]]
   objects := [emptyNullObject, emptyNullObject]
   functions := [⟨⟨"oldNoArg", .number 0⟩, []⟩]
   sets := [[[105, 100]]]
   privates := ⟨[("caller", 5), ("noop", 6)],
     [(0, [(5, .data (.number 11)), (6, .method (.function 1))])]⟩}

private def observation (result : Value × State) :=
  (result.1, result.2.heap, decide (result.2.environment = before.environment),
    decide (result.2.thisValue = before.thisValue), decide (result.2.privates = before.privates))

theorem explicit_call_declaration_parser :
    parseFunctionStatements "const parts = splitPath(path)" ["splitPath", "path"] [] =
      some [.declare "parts" (.invoke (.variable "splitPath") [.variable "path"])] ∧
    (parseBlock "const parts = splitPath(path)" ["splitPath", "path"]).isNone = true ∧
    (parseString "export const echo = (value: string): string => { return value }").map Function.name = some "echo" := by cbv

theorem parser_keeps_scope_and_reference_restrictions :
    (["const result = object['f'](path)", "const result = (object.f as unknown)(path)",
      "const result = f(g(path))", "const result = f(++path)", "const f = f(path)",
      "if (path) { const result = f(path) }", "const result = f(path) result",
      "/* comment */ const result = f(path)"].all fun source =>
        (parseFunctionStatements source ["f", "g", "path", "object"] []).isNone) = true ∧
    (parseFunctionStatements "const url = 'http://x' // comment\r\nconst result = f(url)" ["f"] []).isSome = true := by cbv

/-- The first argument shadows a captured same-name value. Extra argument
effects are retained even though the one formal binds only the first value. -/
theorem missing_and_extra_arguments_keep_real_values_and_effects :
    (runFunctionCall 64 defaultSplitLimit methods table (.variable "f") [] before).map observation =
      .ok (.undefined, before.heap, true, true, true) ∧
    (runFunctionCall 64 defaultSplitLimit methods table (.variable "f")
      [.call (.variable "values") "shift" [], .call (.variable "values") "shift" []] before).map observation =
      .ok (.number 7, [[.function 2, .function 3], []], true, true, true) := by cbv

/-- Callee evaluation removes function2 first. Argument evaluation then removes
function3; the saved function2 closure still runs and returns that argument. -/
theorem saved_callee_precedes_argument_effects :
    (runFunctionCall 64 defaultSplitLimit methods table (.call (.variable "callees") "shift" [])
      [.call (.variable "callees") "shift" []] before).map observation =
      .ok (.function 3, [[], [.number 7, .number 9]], true, true, true) := by cbv

/-- Raw argument evaluation retains a modeled mutable caller binding update.
The caller's this is read before entering the module-undefined function body. -/
theorem caller_argument_scope_effects_are_retained :
    let caller := {before with environment := ("counter", .number 4) :: before.environment}
    (runFunctionCall 64 defaultSplitLimit methods table (.variable "f") [.preIncrement "counter"] caller).map
      (fun result => (result.1, result.2.environment.lookup "counter", result.2.thisValue)) =
        .ok (.number 5, some (.number 5), before.thisValue) ∧
    (runFunctionCall 64 defaultSplitLimit methods table (.variable "f") [.this] before).map Prod.fst =
      .ok before.thisValue := by cbv

theorem argument_errors_precede_callability_and_partition_checks :
    runFunctionCall 64 defaultSplitLimit methods table (.variable "notCallable") [.variable "missing"] before =
      .error .missingVariable ∧
    runFunctionCall 64 defaultSplitLimit methods ⟨1, [⟨echo, [], []⟩]⟩
      (.variable "f") [.variable "missing"] before = .error .missingVariable ∧
    functionTableSeparated methods ⟨0, [⟨echo, [], []⟩]⟩ before = false ∧
    functionTableSeparated methods ⟨1, [⟨echo, [], []⟩]⟩ before = false ∧
    functionTableSeparated methods table before = true := by cbv

theorem captured_writes_and_counted_loops_are_not_admitted :
    stringFunctionBodyAdmitted ⟨⟨"bad", "value", [.ret (.preIncrement "captured")]⟩, captured, names⟩ = false ∧
    stringFunctionBodyAdmitted ⟨⟨"bad", "value", [.countedFor [("i", .number 0)] (.boolean false) "i" []]⟩,
      captured, names⟩ = false := by cbv

/-- A manually constructed this-reading body observes the MODEL'S declared
undefined-module specialization. Actual parsed Function bodies reject this;
this does not claim arbitrary native arrow lexical-this behavior. -/
theorem explicit_module_undefined_this_boundary :
    (parseString "export const f = (value: string): string => { return this }").isNone = true ∧
    (runFunctionCall 64 defaultSplitLimit methods
      ⟨2, [⟨⟨"modelThis", "value", [.ret .this]⟩, [], []⟩]⟩ (.variable "f") [] before).map observation =
      .ok (.undefined, before.heap, true, true, true) := by cbv

private def splitCaller (input : JSString) : State :=
  {before with environment := [("splitPath", .function 2), ("path", .string input)] ++ before.environment}
private def splitTable (program : Function) : FunctionTable :=
  ⟨2, [⟨program, [("path", .number 99), ("paths", .array 0)], names⟩]⟩
private def splitObservation (caller : State) (result : Value × State) :=
  (result.1, result.2.heap, decide (result.2.environment = caller.environment),
    decide (result.2.thisValue = caller.thisValue), decide (result.2.privates = caller.privates),
    decide (result.2.objects = caller.objects), decide (result.2.functions.length = caller.functions.length),
    decide (result.2.sets = caller.sets))

/-- Actual parsed splitPath mutates the fresh current-heap cell, preserving
all old arrays and the caller's scope/this/private/ordinary/Set state. -/
theorem parsed_split_source_returns_current_heap_array :
    (parse pinnedSource).map (fun program =>
      (runFunctionCall 64 defaultSplitLimit methods (splitTable program) (.variable "splitPath")
        [.variable "path"] (splitCaller [47, 97, 47, 47])).map
          (splitObservation (splitCaller [47, 97, 47, 47]))) =
      some (.ok (.array 2, before.heap ++ [[.string [97], .string [], .string []]],
        true, true, true, true, true, true)) := by
  rw [parses_pinned_source]
  cbv

/-- The ignored second argument first allocates array2. The body then returns
array3, so freshness is measured AFTER argument effects, not before the call. -/
theorem ignored_argument_allocation_precedes_split_result :
    (runFunctionCall 64 defaultSplitLimit methods (splitTable splitPathProgram) (.variable "splitPath")
      [.variable "path", .arrayLiteral [(false, .number 17)]] (splitCaller [47, 97])).map Prod.fst = .ok (.array 3) := by cbv

theorem utf16_and_zero_limit_keep_fresh_identity :
    (invokeStringFunction 64 defaultSplitLimit ⟨splitPathProgram, captured, names⟩
      [.string [55296, 47, 233]] before).map (fun result => (result.1, result.2.heap[2]?)) =
      .ok (.array 2, some [.string [55296], .string [233]]) ∧
    (invokeStringFunction 64 0 ⟨splitPathProgram, captured, names⟩ [.string [47, 97]] before).map
      (fun result => (result.1, result.2.heap[2]?)) = .ok (.array 2, some []) := by cbv

/-- info: 'HonoLean.Upstream.SourceSubset.parsed_splitPath_call_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms HonoLean.Upstream.SourceSubset.parsed_splitPath_call_satisfies

end HonoLean.Upstream.SourceSubset.FunctionCallChecks
