import HonoLean.Upstream.GetQueryStrings.Correctness

namespace HonoLean.Upstream.GetQueryStrings

open SourceSubset

set_option maxRecDepth 65536

private def ascii (text : String) : JSString :=
  text.toList.map (fun char => UInt16.ofNat char.toNat)

example : runString queryProgram [] = .ok [] := by cbv
example : runString queryProgram (ascii "1234567?x") = .ok [] := by cbv
example : runString queryProgram (ascii "12345678?x") = .ok (ascii "?x") := by cbv
example : runString queryProgram (ascii "1234567#?x") = .ok (ascii "?x") := by cbv
example : runString queryProgram (ascii "12345678#f?q") = .ok [] := by cbv
example : runString queryProgram (ascii "?1234567?a#b") = .ok (ascii "?a") := by cbv
example : runString queryProgram (ascii "12345678?%3F?x#f") = .ok (ascii "?%3F?x") := by cbv
example : runString queryProgram (ascii "12345678?") = .ok [63] := by cbv

-- Four surrogate pairs occupy eight units. The query and its lone surrogate
-- payload are preserved exactly; no Unicode scalar decoding occurs.
example : runString queryProgram
    [0xD834, 0xDD1E, 0xD834, 0xDD1E, 0xD834, 0xDD1E, 0xD834, 0xDD1E, 63, 0xD800, 0] =
      .ok [63, 0xD800, 0] := by cbv

def rejectedSources : List String := [
  "export const f = (url: string): string => { return\nurl.slice(8) }",
  "export const f = (url: string): string => { return url.slice(8)\n*1 }",
  "export const f = (url: string): string => { const n = url.indexOf('?', 8)\n*1\nreturn url }",
  "export const f = (url: string): string => { return url.slice(-0) }",
  "export const f = (url: string): string => { return url.slice(--1) }",
  "export const f = (url: string): string => { return url.slice(-00) }",
  "export const f = (url: string): string => { return url.slice(-9007199254740992) }",
  "export const f = (url: string): string => { return 1 < 2 < 3 ? '' : url }",
  "export const f = (url: string): string => { return url === '' === url ? '' : url }",
  "export const f = (url: string): string => { return 1 === 1 ? url : 1.slice(0) }",
  "export const f = (url: string): string[] => { return url }",
  "export const f = (url: string): string => { return url } evil()"]

example : rejectedSources.all (fun source => (parseString source).isNone) = true := by cbv
example : (parse pinnedSource).isNone = true := by cbv

-- Subtraction after a newline continues the return/initializer. These used
-- to reject when subtraction was unsupported; accepting it must still consume
-- the operator rather than silently truncate the preceding expression.
def newlineSubtractionSources : List String := [
  "export const f = (url: string): string => { return url.slice(8)\n-1 }",
  "export const f = (url: string): string => { const n = url.indexOf('?', 8)\n-1\nreturn url }"]

example : newlineSubtractionSources.all (fun source => (parseString source).isSome) = true := by cbv

def observedNewlineSubtraction : String :=
  "export const f = (url: string): string => { const n = url.indexOf('?', 8)\n-1\nreturn n === 7 ? 'match' : 'miss' }"

example : (parseString observedNewlineSubtraction).map
    (fun program => runString program (ascii "aaaaaaaa?")) = some (.ok (ascii "match")) := by cbv

-- Generic parsing handles nested ternaries with the JavaScript precedence and
-- right association; it does not recognize getQueryStrings as a whole token.
def associativitySource : String :=
  "export const f = (url: string): string => { return url === '' ? 'a' : url === 'x' ? 'b' : 'c' }"

example : ([[], ascii "x", ascii "y"].map (fun input =>
    (parseString associativitySource).map (fun program => runString program input))) =
      [some (.ok (ascii "a")), some (.ok (ascii "b")), some (.ok (ascii "c"))] := by cbv

def precedenceSource : String :=
  "export const f = (url: string): string => { return url.indexOf('?', 8) === 8 ? 'yes' : 'no' }"

example : (parseString precedenceSource).map (fun program => runString program (ascii "12345678?")) =
    some (.ok (ascii "yes")) := by cbv

def lazySource : String :=
  "export const f = (url: string): string => { return url === '' ? '' : url.shift() }"

-- The unsupported wrong-receiver method is never evaluated in the chosen arm.
example : (parseString lazySource).map (fun program => runString program []) =
    some (.ok []) := by cbv

def offsetZeroSource : String :=
  "export const getQueryStrings = (url: string): string => {\n  const queryIndex = url.indexOf('?', 0)\n  if (queryIndex === -1) {\n    return ''\n  }\n\n  const hashIndex = url.indexOf('#', 8)\n  return hashIndex === -1\n    ? url.slice(queryIndex)\n    : queryIndex < hashIndex\n      ? url.slice(queryIndex, hashIndex)\n      : ''\n}"

def hashAfterQuerySource : String :=
  "export const getQueryStrings = (url: string): string => {\n  const queryIndex = url.indexOf('?', 8)\n  if (queryIndex === -1) {\n    return ''\n  }\n\n  const hashIndex = url.indexOf('#', queryIndex)\n  return hashIndex === -1\n    ? url.slice(queryIndex)\n    : queryIndex < hashIndex\n      ? url.slice(queryIndex, hashIndex)\n      : ''\n}"

def reversedOrderSource : String :=
  "export const getQueryStrings = (url: string): string => {\n  const queryIndex = url.indexOf('?', 8)\n  if (queryIndex === -1) {\n    return ''\n  }\n\n  const hashIndex = url.indexOf('#', 8)\n  return hashIndex === -1\n    ? url.slice(queryIndex)\n    : hashIndex < queryIndex\n      ? url.slice(queryIndex, hashIndex)\n      : ''\n}"

def SourceHasContract (source : String) : Prop :=
  ∀ input output,
    (parseString source).map (fun program => runString program input) =
      some (.ok output) ↔ QueryStringsContract input output

theorem offsetZeroSource_not_correct : ¬ SourceHasContract offsetZeroSource := by
  intro claimed
  have actual : (parseString offsetZeroSource).map (fun program => runString program (ascii "abc?x")) =
      some (.ok (ascii "?x")) := by cbv
  have invalid : ¬ QueryStringsContract (ascii "abc?x") (ascii "?x") := by
    rw [contract_iff]
    decide +kernel
  exact invalid ((claimed _ _).mp actual)

theorem hashAfterQuerySource_not_correct : ¬ SourceHasContract hashAfterQuerySource := by
  intro claimed
  have actual : (parseString hashAfterQuerySource).map
      (fun program => runString program (ascii "12345678#f?q")) =
      some (.ok (ascii "?q")) := by cbv
  have invalid : ¬ QueryStringsContract (ascii "12345678#f?q") (ascii "?q") := by
    rw [contract_iff]
    decide +kernel
  exact invalid ((claimed _ _).mp actual)

theorem reversedOrderSource_not_correct : ¬ SourceHasContract reversedOrderSource := by
  intro claimed
  have actual : (parseString reversedOrderSource).map
      (fun program => runString program (ascii "12345678?q#f")) = some (.ok []) := by cbv
  have invalid : ¬ QueryStringsContract (ascii "12345678?q#f") [] := by
    rw [contract_iff]
    decide +kernel
  exact invalid ((claimed _ _).mp actual)

end HonoLean.Upstream.GetQueryStrings
