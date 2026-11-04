import HonoLean.Upstream.SourceSubset.PatternCacheSyntax

set_option autoImplicit false
namespace HonoLean.Upstream.GetPatternBody
open SourceSubset

structure ArrowParameter where
  name : String
  optional : Bool
  annotation : TypeSyntax
  deriving Repr

/-- Retained declaration syntax. `innerSource` includes the original leading
comments verbatim; neither parsing nor this record creates a function object. -/
structure ExportedArrow where
  name : String
  parameters : List ArrowParameter
  resultType : TypeSyntax
  innerSource : String
  body : List PatternCacheStmt
  deriving Repr

private def white (c : Char) : Bool := [' ', '\t', '\n', '\r'].contains c

/-- Only leading whitespace and ASCII // comments terminated by CR/LF are trivia. Once the first
body token is reached, all later bytes go to the existing fail-closed parser.
No comment removal is attempted inside strings, templates or regex literals. -/
def leadingBodyTrivia : Nat → List Char → Option (List Char)
  | 0, _ => none
  | fuel + 1, chars =>
    let rest := chars.dropWhile white
    match rest with
    | '/' :: '/' :: tail =>
      let afterComment := tail.dropWhile (fun c => c != '\n' && c != '\r')
      let comment := tail.takeWhile (fun c => c != '\n' && c != '\r')
      if afterComment.isEmpty || comment.any (fun c => c.toNat > 127) then none else leadingBodyTrivia fuel afterComment
    | _ => some rest

private def parameters : Nat → Bool → List Token → Option (List ArrowParameter × List Token)
  | 0, _, _ => none
  | _ + 1, _, .punctuation ")" :: rest => some ([], rest)
  | fuel + 1, seenOptional, .name name :: rest => do
    if !bindingNameAllowed name then none else
    let (optional, rest) := match rest with
      | .punctuation "?" :: rest => (true, rest)
      | _ => (false, rest)
    if seenOptional && !optional then none else
    let rest ← match rest with | .punctuation ":" :: rest => some rest | _ => none
    let (annotation, rest) ← parseTypeTokens rest
    let (tail, rest) ← match rest with
      | .punctuation "," :: .punctuation ")" :: _ => none
      | .punctuation "," :: rest => parameters fuel (seenOptional || optional) rest
      | .punctuation ")" :: rest => some ([], rest)
      | _ => none
    pure (⟨name, optional, annotation⟩ :: tail, rest)
  | _, _, _ => none

/-- A restricted structural exported-arrow grammar: named TypeSyntax arguments,
optional parameter markers and result annotation are retained. Object type
syntax/default/rest/destructured parameters and multiline headers refuse. -/
def parseExportedArrow (text : String) (ambientBindings : List String) : Option ExportedArrow := do
  let chars := text.toList
  let header := chars.takeWhile (· != '{')
  if header.any (fun c => c == '\n' || c == '\r') then none else
  let afterOpen ← match chars.drop header.length with | '{' :: rest => some rest | _ => none
  let reversed := (afterOpen.reverse.dropWhile white)
  let inner ← match reversed with | '}' :: rest => some rest.reverse | _ => none
  let tokens ← tokenizeFragment (String.ofList header)
  let (name, rest) ← match tokens with
    | .name "export" :: .name "const" :: .name name :: .punctuation "=" :: .punctuation "(" :: rest => some (name, rest)
    | _ => none
  if !bindingNameAllowed name || ambientBindings.contains name then none else
  let (args, rest) ← parameters (tokens.length + 1) false rest
  let names := args.map ArrowParameter.name
  if !(decide names.Nodup) || names.any ambientBindings.contains then none else
  let rest ← match rest with | .punctuation ":" :: rest => some rest | _ => none
  let (resultType, rest) ← parseTypeTokens rest
  match rest with
  | [.punctuation "=>"] =>
    let content ← leadingBodyTrivia (inner.length + 1) inner
    let body ← parsePatternCacheBody (String.ofList content) (names ++ ambientBindings)
    pure ⟨name, args, resultType, String.ofList inner, body⟩
  | _ => none

end HonoLean.Upstream.GetPatternBody
