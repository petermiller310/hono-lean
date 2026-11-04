import HonoLean.Upstream.SourceSubset.PrivateControlParser

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset

/-- Original selected syntax, without changing the frozen ordinary Expr ABI.
A template has exactly one substitution; unsupported escapes/tagged templates
and additional substitutions reject instead of being rewritten. -/
inductive RegExpConstructExpr where
  | ordinary (expression : Expr)
  | template (head : JSString) (operand : Expr) (tail : JSString)
  | construct (callee : Expr) (argument : RegExpConstructExpr)
  | arrayLiteral (elements : List RegExpConstructExpr)
  deriving Repr

private inductive ConstructToken where
  | ordinary (token : Token)
  | template (head : JSString) (operand : Expr) (tail : JSString)
  deriving Repr

/-- Shared quoted-string syntax is still validated by tokenizeFragment. This
scanner only ensures a backtick INSIDE a quote is not mistaken for a template. -/
private def ordinaryChunk : Nat → Option Char → List Char → Option (List Char × List Char)
  | 0, _, _ => none
  | _ + 1, none, [] => some ([], [])
  | _ + 1, some _, [] => none
  | fuel + 1, quote, c :: rest => do
    match quote with
    | some delimiter =>
      if c == '\\' then none else
      let tail ← ordinaryChunk fuel (if c == delimiter then none else quote) rest
      some (c :: tail.1, tail.2)
    | none =>
      if c == '`' then some ([], c :: rest) else
      let tail ← ordinaryChunk fuel (if c == '\'' || c == '"' then some c else none) rest
      some (c :: tail.1, tail.2)

private def templateHead : Nat → List Char → Option (JSString × List Char)
  | 0, _ => none
  | _ + 1, '$' :: '{' :: rest => some ([], rest)
  | fuel + 1, c :: rest => do
    if c == '`' || c == '\\' || c == '\n' || c == '\r' || c.val > 127 then none else
    let tail ← templateHead fuel rest
    some (UInt16.ofNat c.toNat :: tail.1, tail.2)
  | _, [] => none

private def templateOperand : Nat → Option Char → Nat → List Char → Option (List Char × List Char)
  | 0, _, _, _ => none
  | _, _, _, [] => none
  | fuel + 1, quote, depth, c :: rest => do
    if c == '`' || c == '\\' then none else
    match quote with
    | some delimiter =>
      let tail ← templateOperand fuel (if c == delimiter then none else quote) depth rest
      some (c :: tail.1, tail.2)
    | none =>
      if c == '}' && depth == 0 then some ([], rest) else
      let nextDepth := if c == '{' then depth + 1 else if c == '}' then depth - 1 else depth
      let tail ← templateOperand fuel (if c == '\'' || c == '"' then some c else none) nextDepth rest
      some (c :: tail.1, tail.2)

private def templateTail : Nat → List Char → Option (JSString × List Char)
  | 0, _ => none
  | _ + 1, '`' :: rest => some ([], rest)
  | _ + 1, '$' :: '{' :: _ => none
  | fuel + 1, c :: rest => do
    if c == '\\' || c == '\n' || c == '\r' || c.val > 127 then none else
    let tail ← templateTail fuel rest
    some (UInt16.ofNat c.toNat :: tail.1, tail.2)
  | _, [] => none

private def constructTokens : Nat → List Char → Option (List ConstructToken)
  | 0, _ => none
  | fuel + 1, chars => do
    let (chunk, remaining) ← ordinaryChunk (chars.length + 1) none chars
    let tokens ← tokenizeFragment (String.ofList chunk)
    match remaining with
    | [] => some (tokens.map .ordinary)
    | '`' :: rest =>
      let (head, rest) ← templateHead (rest.length + 1) rest
      let (operandText, rest) ← templateOperand (rest.length + 1) none 0 rest
      let operandTokens ← tokenizeFragment (String.ofList operandText)
      let (operand, leftover) ← parseRawExpressionTokens operandTokens
      if !(skipTokenLines leftover).isEmpty then none else
      let (tail, rest) ← templateTail (rest.length + 1) rest
      let remaining ← constructTokens fuel rest
      some (tokens.map .ordinary ++ .template head operand tail :: remaining)
    | _ => none

private def constructSkip (tokens : List ConstructToken) : List ConstructToken :=
  tokens.dropWhile (fun token => match token with | .ordinary .lineBreak => true | _ => false)

/-- Keep grouping inside an ordinary leaf; stop only at a delimiter belonging
to the new surrounding grammar. new-callee mode stops before its argument (. -/
private def constructOrdinaryCut : Nat → Nat → Bool → List ConstructToken → List Token × List ConstructToken
  | 0, _, _, tokens => ([], tokens)
  | _ + 1, _, _, [] => ([], [])
  | fuel + 1, depth, callee, token :: rest =>
    match token with
    | .template _ _ _ => ([], token :: rest)
    | .ordinary value =>
      if depth == 0 && (value == .punctuation "," || value == .punctuation "]" ||
          value == .punctuation ")" || (callee && value == .punctuation "(")) then ([], token :: rest) else
      let nextDepth := match value with
        | .punctuation "(" | .punctuation "[" | .punctuation "{" => depth + 1
        | .punctuation ")" | .punctuation "]" | .punctuation "}" => depth - 1
        | _ => depth
      let tail := constructOrdinaryCut fuel nextDepth callee rest
      (value :: tail.1, tail.2)

private def constructOrdinaryAllowed (expression : Expr) (bindings privateNames : List String) : Bool :=
  expressionAdmitted expression bindings privateNames true && privateControlExpressionAllowed 65536 expression

mutual
  private def parseConstructTokens : Nat → List String → List String → List ConstructToken → Option (RegExpConstructExpr × List ConstructToken)
    | 0, _, _, _ => none
    | fuel + 1, bindings, privateNames, tokens => do
      match constructSkip tokens with
      | .ordinary (.punctuation "[") :: rest =>
        let (elements, rest) ← parseConstructElements fuel bindings privateNames rest
        some (.arrayLiteral elements, rest)
      | .ordinary (.name "new") :: rest =>
        let (calleeTokens, rest) := constructOrdinaryCut (rest.length + 1) 0 true rest
        let (callee, leftover) ← parseRawExpressionTokens calleeTokens
        if !(skipTokenLines leftover).isEmpty || !constructOrdinaryAllowed callee bindings privateNames then none else
        let rest ← match constructSkip rest with | .ordinary (.punctuation "(") :: rest => some rest | _ => none
        let (argument, rest) ← parseConstructTokens fuel bindings privateNames rest
        let rest ← match constructSkip rest with | .ordinary (.punctuation ")") :: rest => some rest | _ => none
        some (.construct callee argument, rest)
      | .template head operand tail :: rest =>
        if constructOrdinaryAllowed operand bindings privateNames then some (.template head operand tail, rest) else none
      | tokens =>
        let (ordinaryTokens, rest) := constructOrdinaryCut (tokens.length + 1) 0 false tokens
        let (expression, leftover) ← parseRawExpressionTokens ordinaryTokens
        if (skipTokenLines leftover).isEmpty && constructOrdinaryAllowed expression bindings privateNames then
          some (.ordinary expression, rest) else none

  private def parseConstructElements : Nat → List String → List String → List ConstructToken → Option (List RegExpConstructExpr × List ConstructToken)
    | 0, _, _, _ => none
    | fuel + 1, bindings, privateNames, tokens => do
      match constructSkip tokens with
      | .ordinary (.punctuation "]") :: rest => some ([], rest)
      | tokens =>
        let (head, rest) ← parseConstructTokens fuel bindings privateNames tokens
        match constructSkip rest with
        | .ordinary (.punctuation "]") :: rest => some ([head], rest)
        | .ordinary (.punctuation ",") :: rest =>
          let (tail, rest) ← parseConstructElements fuel bindings privateNames rest
          some (head :: tail, rest)
        | _ => none
end

/-- New expression entry only. No constructor spelling is interpreted here;
ordinary leaves retain the shared frontend's binding/private admission. The
selected template grammar has one substitution and literal ASCII segments. -/
def parseRegExpConstruct (text : String) (allowedBindings : List String) (allowedPrivateNames : List String := []) : Option RegExpConstructExpr := do
  if !allowedBindings.all bindingNameAllowed then none else
  let tokens ← constructTokens (text.toList.length + 1) text.toList
  let (expression, rest) ← parseConstructTokens (tokens.length + 1) allowedBindings allowedPrivateNames tokens
  if (constructSkip rest).isEmpty then some expression else none

end HonoLean.Upstream.SourceSubset
