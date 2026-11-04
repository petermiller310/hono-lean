import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset.SetChecks

set_option maxRecDepth 65536

private def a : JSString := [97]
private def b : JSString := [98]

-- The generic constructor AST retains the checked TypeScript type argument.
example : parseExpression "new Set<string>()" [] =
    some (.construct (.variable "Set") (some .string) []) := by cbv
example : parseBlock "const possibleKeys = new Set<string>()" [] =
    some [.declare "possibleKeys" (.construct (.variable "Set") (some .string) [])] := by cbv
example : parseExpression "possibleKeys.add(pattern[1])" ["possibleKeys", "pattern"] =
    some (.call (.variable "possibleKeys") "add" [.index (.variable "pattern") (.number 1)]) := by cbv
example : parseExpression "[...possibleKeys]" ["possibleKeys"] =
    some (.arrayLiteral [(true, .variable "possibleKeys")]) := by cbv

-- Constructor syntax is not a Set-name recognizer: an explicit standard alias
-- works, and a shadowed Set binding does not silently resolve to the builtin.
example : (parseExpression "new Factory<string>()" ["Factory"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression
      {environment := [("Factory", .setConstructor)]}) =
        some (.ok (.set 0, {environment := [("Factory", .setConstructor)], sets := [[]]})) := by cbv
example : (parseExpression "new Set<string>()" []).map
    (fun expression => evalExpression 32 defaultSplitLimit expression
      {environment := [("Set", .string [])]}) = some (.error .unsupported) := by cbv

private def withPattern : State :=
  {environment := [("possibleKeys", .set 0), ("pattern", .array 0)],
   heap := [[.string [], .string a]], sets := [[]]}

example : (parseExpression "possibleKeys.add(pattern[1])" ["possibleKeys", "pattern"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression withPattern) =
      some (.ok (.set 0, {withPattern with sets := [[a]]})) := by cbv

private def aliases : State :=
  {environment := [("possibleKeys", .set 0), ("alias", .set 0)], sets := [[a]]}

-- Add mutates the same Set reference and duplicate addition is idempotent.
example : (parseExpression "alias.add('b')" ["alias"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression aliases) =
      some (.ok (.set 0, {aliases with sets := [[a, b]]})) := by cbv
example : intrinsic defaultSplitLimit (.set 0) "add" [.string a] aliases = .ok (.set 0, aliases) := by cbv
example : truthy (.set 0) = true ∧ truthy .setConstructor = true := by cbv

private def snapshotSource : String :=
  "const possibleKeys = new Set<string>()\npossibleKeys.add('a')\nconst first = [...possibleKeys]\npossibleKeys.add('b')\nconst second = [...possibleKeys]"

-- Past spread arrays remain unchanged after later additions. Equal contents
-- are still fresh array identities, and declaration locals do not leak.
example : (parseBlock snapshotSource []).map (fun program => runBlock 60 program {}) =
    some (.ok (.normal {heap := [[.string a], [.string a, .string b]], sets := [[a, b]]})) := by cbv

example : (parseExpression "[[...possibleKeys], [...possibleKeys]]" ["possibleKeys"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression aliases) =
      some (.ok (.array 0, {aliases with heap := [[.array 1, .array 2], [.string a], [.string a]]})) := by cbv

-- Each spread finishes before the next element: later mutation affects the
-- later spread, without retroactively changing the earlier copied prefix.
example : (parseExpression "[...possibleKeys, possibleKeys.add('b'), ...possibleKeys]" ["possibleKeys"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression aliases) =
      some (.ok (.array 0, {aliases with heap := [[.string a, .set 0, .string a, .string b]], sets := [[a, b]]})) := by cbv

-- Array literal allocation precedes normal element effects. Dense-array spread
-- copies reference values, and literal own creation does not call push.
example : (parseExpression "[[], []]" []).map
    (fun expression => evalExpression 32 defaultSplitLimit expression {}) =
      some (.ok (.array 0, {heap := [[.array 1, .array 2], [], []]})) := by cbv
example : (parseExpression "[0, ...items, 1]" ["items"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression
      {environment := [("items", .array 0)], heap := [[.object 0, .object 0]], objects := [ECMA2025.emptyNullObject]}) =
        some (.ok (.array 1,
          {environment := [("items", .array 0)], heap := [[.object 0, .object 0], [.number 0, .object 0, .object 0, .number 1]],
           objects := [ECMA2025.emptyNullObject]})) := by cbv

-- Stable Set iteration preserves UTF-16 strings as whole keys, including lone
-- surrogates and astral pairs. It does not iterate the characters of a string.
example : iterableValues (.set 0) {sets := [[[0xD800], [0xD834, 0xDD1E], [0xDC00]]]} =
    .ok [.string [0xD800], .string [0xD834, 0xDD1E], .string [0xDC00]] := by cbv
example : (parseExpression "[...'abc']" []).map
    (fun expression => evalExpression 32 defaultSplitLimit expression {}) = some (.error .unsupported) := by cbv
example : intrinsic defaultSplitLimit (.set 0) "add" [.number 0] {sets := [[]]} =
    .error .unsupported := by cbv
example : iterableValues (.object 0) {objects := [ECMA2025.emptyNullObject]} = .error .unsupported := by cbv
example : iterableValues (.set 7) {} = .error .invalidReference := by cbv

private def rejected : List String := [
  "new Set<number>()", "new Set<string, string>()", "new Set<string>(['a'])",
  "[...unbound]", "[..possibleKeys]", "[. . .possibleKeys]", "[,,]", "[...possibleKeys,,]",
  "new Set<string>() evil()"]

example : rejected.all (fun source => (parseExpression source ["possibleKeys"]).isNone) = true := by cbv
example : (parseBlock "const Set = new Set<string>()" []).isNone = true := by cbv
example : (parseNoArg "export const Set = () => new Set<string>()").isNone = true := by cbv

end HonoLean.Upstream.SourceSubset.SetChecks
