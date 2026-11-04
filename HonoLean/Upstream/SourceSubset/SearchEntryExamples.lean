import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset.SearchEntryChecks

set_option maxRecDepth 65536

private def handlerType : TypeSyntax := .application (.named "HandlerParamsSet") [.named "T"]
private def collectorType : TypeSyntax := .array handlerType

example : parseBlock "const handlerSets: HandlerParamsSet<T>[] = []" [] =
    some [.typedDeclare "handlerSets" collectorType (.arrayLiteral [])] := by cbv
example : declaredNames [.typedDeclare "handlerSets" collectorType (.arrayLiteral [])] = ["handlerSets"] := by cbv

-- The typed collector still allocates a fresh array and binds that reference;
-- the annotation adds neither a runtime type guard nor an allocation shortcut.
example : (parseBlock "const handlerSets: HandlerParamsSet<T>[] = []" []).map
    (fun program => execute 16 defaultSplitLimit program {heap := [[.number 7]]}) =
      some (.ok (.normal {environment := [("handlerSets", .array 1)], heap := [[.number 7], []]})) := by cbv
example : (parseBlock "const handlerSets: HandlerParamsSet<T>[] = []" []).map
    (fun program => runBlock 16 program {environment := [("handlerSets", .array 0)], heap := [[]]}) =
      some (.ok (.normal {environment := [("handlerSets", .array 0)], heap := [[], []]})) := by cbv

example : parseBlock "const m = node.#methods[i]" ["node", "i"] ["methods"] =
    some [.declare "m" (.index (.privateProperty (.variable "node") "methods") (.variable "i"))] := by cbv
example : (parseBlock "const m = node.#methods[i]" ["node", "i"]).isNone = true := by cbv

private def choice : Expr := .logicalOr (.index (.variable "m") (.variable "method"))
  (.index (.variable "m") (.variable "METHOD_NAME_ALL"))

example : parseBlock "const handlerSet = (m[method] || m[METHOD_NAME_ALL]) as HandlerParamsSet<T>"
    ["m", "method", "METHOD_NAME_ALL"] =
      some [.declare "handlerSet" (.typeAssertion choice handlerType)] := by cbv
example : parseExpression "'ALL' as const" [] =
    some (.typeAssertion (.string [65,76,76]) .constAssertion) := by cbv
example : (parseExpression "'ALL' as const" []).map
    (fun expression => evalExpression 16 defaultSplitLimit expression {}) =
      some (.ok (.string [65,76,76], {})) := by cbv

private def falsy : List Value := [.undefined, .null, .boolean false, .number 0, .string []]
private def truthyValues : List Value :=
  [.boolean true, .number (-1), .string [0], .object 0, .array 0, .function 0, .objectConstructor, .set 0, .setConstructor]

-- OR preserves the original chosen operand Value, rather than returning Bool.
example : falsy.map (fun value => evalExpression 8 defaultSplitLimit
    (.logicalOr (.variable "left") (.string [114])) {environment := [("left", value)]}) =
      falsy.map (fun value => .ok (.string [114], {environment := [("left", value)]})) := by cbv
example : truthyValues.map (fun value => evalExpression 8 defaultSplitLimit
    (.logicalOr (.variable "left") (.variable "missing")) {environment := [("left", value)]}) =
      truthyValues.map (fun value => .ok (value, {environment := [("left", value)]})) := by cbv

-- Left-side effects are retained when falsy, then the right side runs next.
example : (parseExpression "(++order) || (++order)" ["order"]).map
    (fun expression => evalExpression 16 defaultSplitLimit expression {environment := [("order", .number (-1))]}) =
      some (.ok (.number 1, {environment := [("order", .number 1)]})) := by cbv
example : (parseExpression "items.shift() || items.shift()" ["items"]).map
    (fun expression => evalExpression 16 defaultSplitLimit expression
      {environment := [("items", .array 0)], heap := [[.string [], .string [98]]]}) =
        some (.ok (.string [98], {environment := [("items", .array 0)], heap := [[]]})) := by cbv

example : (parseExpression "left || bad.x" ["left", "bad"]).map
    (fun expression => evalExpression 16 defaultSplitLimit expression
      {environment := [("left", .string [121]), ("bad", .object 7)]}) =
        some (.ok (.string [121], {environment := [("left", .string [121]), ("bad", .object 7)]})) := by cbv
example : (parseExpression "left || bad.x" ["left", "bad"]).map
    (fun expression => evalExpression 16 defaultSplitLimit expression
      {environment := [("left", .boolean false), ("bad", .object 7)]}) =
        some (.error (.objectError .invalidReference)) := by cbv

-- Assertions do not establish the shape claimed by an arbitrary type name.
example : (parseExpression "0 as HandlerParamsSet<T>" []).map
    (fun expression => evalExpression 16 defaultSplitLimit expression {}) = some (.ok (.number 0, {})) := by cbv

example : parseExpression "a || b && c" ["a", "b", "c"] =
    some (.logicalOr (.variable "a") (.logicalAnd (.variable "b") (.variable "c"))) := by cbv
example : parseExpression "a && b || c" ["a", "b", "c"] =
    some (.logicalOr (.logicalAnd (.variable "a") (.variable "b")) (.variable "c")) := by cbv
example : parseExpression "a || b as T" ["a", "b"] =
    some (.logicalOr (.variable "a") (.typeAssertion (.variable "b") (.named "T"))) := by cbv
example : parseExpression "(a || b) as T" ["a", "b"] =
    some (.typeAssertion (.logicalOr (.variable "a") (.variable "b")) (.named "T")) := by cbv
example : parseExpression "value as Box<List<T>>[][]" ["value"] =
    some (.typeAssertion (.variable "value")
      (.array (.array (.application (.named "Box") [.application (.named "List") [.named "T"]])))) := by cbv

private def malformed : List String := [
  "a || b ?? c", "a ?? b || c", "a && b || c ?? a", "a ?? b && c || a",
  "'ALL'\nas const", "a\nas T", "a as", "a as Box<>", "a as Box<T", "a as Box<T,>",
  "a as T[", "a as const", "null as const", "a as keyof T", "a as const[]"]

example : malformed.all (fun text => (parseExpression text ["a", "b", "c"]).isNone) = true := by cbv
example : (parseBlock "const handlerSets: const = []" []).isNone = true := by cbv
example : (parseBlock "const handlerSets: HandlerParamsSet<>[] = []" []).isNone = true := by cbv
example : (parseBlock "const x: T = a\nas T" ["a"]).isNone = true := by cbv

-- Newline-before-as terminates assertion parsing, while grouping explicitly
-- permits the coalescing/OR combinations rejected in their unparenthesized form.
example : parseBlock "const x: T = a\nas()" ["a", "as"] =
    some [.typedDeclare "x" (.named "T") (.variable "a"), .evaluate (.invoke (.variable "as") [])] := by cbv
example : ["(a ?? b) || c", "a ?? (b || c)", "(a || b) ?? c", "a || (b ?? c)"].all
    (fun text => (parseExpression text ["a", "b", "c"]).isSome) = true := by cbv

end HonoLean.Upstream.SourceSubset.SearchEntryChecks
