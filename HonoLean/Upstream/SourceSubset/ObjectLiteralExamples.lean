import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.Semantics

namespace HonoLean.Upstream.SourceSubset.ObjectLiteralChecks

open ECMA2025

set_option maxRecDepth 65536

private def root : State := {objects := [objectPrototypeProjection []]}
private def k : JSString := [107]
private def handlerKey : JSString := [104,97,110,100,108,101,114]
private def keysKey : JSString := [112,111,115,115,105,98,108,101,75,101,121,115]
private def scoreKey : JSString := [115,99,111,114,101]

-- Empty heap cannot allocate a self-prototype literal by accidentally using0
-- as both the intrinsic root and new object identity.
example : (parseExpression "{}" []).map
    (fun expression => evalExpression 32 defaultSplitLimit expression {}) =
      some (.error .invalidReference) := by cbv

example : (parseExpression "{}" []).map
    (fun expression => evalExpression 32 defaultSplitLimit expression root) =
      some (.ok (.object 1, {root with objects := root.objects ++ [emptyLiteralObject]})) := by cbv

-- An inherited prototype setter is bypassed by literal own-data definition.
private def safe : JSString := [115,97,102,101]

example : (parseExpression "{['__proto__']: 'safe'}" []).map
    (fun expression => evalExpression 32 defaultSplitLimit expression root) =
      some (.ok (.object 1, {root with objects :=
        root.objects ++ [newDataObject emptyLiteralObject protoKey (.string safe)]})) := by cbv
example : (parseExpression "{__proto__}" ["__proto__"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression
      {root with environment := [("__proto__", .string safe)]}) =
        some (.ok (.object 1, {environment := [("__proto__", .string safe)], objects :=
          root.objects ++ [newDataObject emptyLiteralObject protoKey (.string safe)]})) := by cbv

private def fields : OrdinaryObject :=
  newDataObject (newDataObject (newDataObject emptyLiteralObject handlerKey (.function 0))
    keysKey (.array 0)) scoreKey (.number 8)

private def input : State :=
  {root with
    environment := [("method", .string [71,69,84]), ("handler", .function 0), ("possibleKeys", .set 0), ("order", .number 7)],
    functions := [⟨⟨"handler", .null⟩, []⟩],
    sets := [[[97], [98]]]}

-- The outer object is allocated first, the nested handler record second, and
-- the spread array third in its own heap. Score holds the incremented value.
example : (parseExpression
    "{ [method]: { handler, possibleKeys: [...possibleKeys], score: ++order, }, }"
    ["method", "handler", "possibleKeys", "order"]).map
      (fun expression => evalExpression 64 defaultSplitLimit expression input) =
        some (.ok (.object 1,
          {input with
            environment := [("method", .string [71,69,84]), ("handler", .function 0), ("possibleKeys", .set 0), ("order", .number 8)],
            heap := [[.string [97], .string [98]]],
            objects := root.objects ++ [newDataObject emptyLiteralObject [71,69,84] (.object 2), fields]})) := by cbv

-- Computed key expression effects precede the value expression. The key is
-- already a string, so no object-to-key coercion assumption is hidden here.
example : (parseExpression "{[(++order) ? 'k' : 'k']: ++order}" ["order"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression
      {root with environment := [("order", .number 0)]}) =
        some (.ok (.object 1, {environment := [("order", .number 2)], objects :=
          root.objects ++ [newDataObject emptyLiteralObject k (.number 2)]})) := by cbv

-- Unsupported key conversion rejects before the value's own failing read.
example : (parseExpression "{[key]: bad.x}" ["key", "bad"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression
      {root with environment := [("key", .number 0), ("bad", .object 9)]}) =
        some (.error .unsupported) := by cbv

-- Duplicate names override the own descriptor/value, not an inherited setter.
example : (parseExpression "{x: 1, x: 2,}" []).map
    (fun expression => evalExpression 32 defaultSplitLimit expression root) =
      some (.ok (.object 1, {root with objects :=
        root.objects ++ [newDataObject emptyLiteralObject [120] (.number 2)]})) := by cbv

example : (parseExpression "++order" ["order"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression
      {environment := [("order", .number 4), ("order", .number 90)]}) =
        some (.ok (.number 5, {environment := [("order", .number 5), ("order", .number 90)]})) := by cbv
example : (parseExpression "++order" ["order"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression {}) =
      some (.error .missingVariable) := by cbv
example : (parseExpression "++order" ["order"]).map
    (fun expression => evalExpression 32 defaultSplitLimit expression {environment := [("order", .string [49])]}) =
      some (.error .unsupported) := by cbv

private def rejected : List String := [
  "{__proto__: value}", "{'__proto__': value}", "{...other}",
  "{get x(){}}", "{set x(value){}}", "{method(){}}", "{0: value}",
  "++obj.x", "++obj[key]", "++obj?.[key]", "++order()", "++(order)", "order++", "++true"]

example : rejected.all (fun source =>
    (parseExpression source ["value", "other", "obj", "key", "order"]).isNone) = true := by cbv

-- Expression-context braces are not silently treated as statement/arrow blocks.
example : (parseBlock "{}" []).isNone = true := by cbv
example : (parseNoArg "export const f = () => {}").isNone = true := by cbv
example : (parseNoArg "export const f = () => ({})").isSome = true := by cbv

end HonoLean.Upstream.SourceSubset.ObjectLiteralChecks
