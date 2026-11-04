import HonoLean.Upstream.SourceSubset.LabelMatchSyntax

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset

inductive PatternCacheExpr where
  | ordinary (value : Expr)
  | index (base key : PatternCacheExpr)
  | logicalNot (value : PatternCacheExpr)
  | logicalAnd (left right : PatternCacheExpr)
  | strictEqual (left right : PatternCacheExpr)
  | strictNotEqual (left right : PatternCacheExpr)
  | conditional (condition yes no : PatternCacheExpr)
  | template (head : JSString) (substitutions : List (Expr × JSString))
  | construct (callee : Expr) (argument : PatternCacheExpr)
  | arrayLiteral (elements : List PatternCacheExpr)
  | emptyObject
  | labelMatch (receiver : Expr) (method : String) (literal : LabelRegExpLiteral)
  deriving Repr
inductive PatternCacheStmt where
  | declare (name : String) (initializer : PatternCacheExpr)
  | assign (target value : PatternCacheExpr)
  | branch (condition : PatternCacheExpr) (yes no : List PatternCacheStmt)
  | ret (value : PatternCacheExpr)
  deriving Repr
structure PatternCacheInit where
  name : String
  indexName : String
  indexType : TypeSyntax
  valueType : TypeSyntax
  initializer : PatternCacheExpr
  deriving Repr

private inductive CacheToken where
  | ordinary (value : Token)
  | template (head : JSString) (substitutions : List (Expr × JSString))
  | regexp (literal : LabelRegExpLiteral)
  deriving Repr

private def chunk : Nat → Option Char → List Char → Option (List Char × List Char)
  | 0, _, _ => none
  | _ + 1, none, [] => some ([], [])
  | _ + 1, some _, [] => none
  | fuel + 1, quote, c :: rest => do
    match quote with
    | some delimiter =>
      if c == '\\' then none else
      let tail ← chunk fuel (if c == delimiter then none else quote) rest
      some (c :: tail.1, tail.2)
    | none =>
      if c == '`' || c == '/' || (c == '!' && ['=', '='].isPrefixOf rest) then some ([], c :: rest) else
      let tail ← chunk fuel (if c == '\'' || c == '"' then some c else none) rest
      some (c :: tail.1, tail.2)

private def templateSegment : Nat → List Char → Option (JSString × Bool × List Char)
  | 0, _ => none
  | _ + 1, '`' :: rest => some ([], false, rest)
  | _ + 1, '$' :: '{' :: rest => some ([], true, rest)
  | fuel + 1, c :: rest => do
    if c == '\\' || c == '\n' || c == '\r' || c.toNat > 127 then none else
    let (tail, interpolate, rest) ← templateSegment fuel rest
    some (UInt16.ofNat c.toNat :: tail, interpolate, rest)
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
      let depth := if c == '{' then depth + 1 else if c == '}' then depth - 1 else depth
      let tail ← templateOperand fuel (if c == '\'' || c == '"' then some c else none) depth rest
      some (c :: tail.1, tail.2)

private def templateRest : Nat → List Char → Option (List (Expr × JSString) × List Char)
  | 0, _ => none
  | fuel + 1, chars => do
    let (operandText, rest) ← templateOperand (chars.length + 1) none 0 chars
    let tokens ← tokenizeFragment (String.ofList operandText)
    let (operand, leftover) ← parseRawExpressionTokens tokens
    if !(skipTokenLines leftover).isEmpty then none else
    let (literal, more, rest) ← templateSegment (rest.length + 1) rest
    if more then
      let (tail, rest) ← templateRest fuel rest
      some ((operand, literal) :: tail, rest)
    else some ([(operand, literal)], rest)

private def regexpBody : Nat → List Char → Option (JSString × List Char)
  | 0, _ => none
  | _ + 1, '/' :: rest => some ([], rest)
  | fuel + 1, '\\' :: escaped :: rest => do
    if escaped == '\n' || escaped == '\r' || escaped.toNat > 127 then none else
    let (tail, rest) ← regexpBody fuel rest
    some (92 :: UInt16.ofNat escaped.toNat :: tail, rest)
  | fuel + 1, c :: rest => do
    if c == '\n' || c == '\r' || c.toNat > 127 then none else
    let (tail, rest) ← regexpBody fuel rest
    some (UInt16.ofNat c.toNat :: tail, rest)
  | _, [] => none

private def cacheTokens : Nat → List Char → Option (List CacheToken)
  | 0, _ => none
  | fuel + 1, chars => do
    let (ordinary, rest) ← chunk (chars.length + 1) none chars
    let tokens ← tokenizeFragment (String.ofList ordinary)
    let (special, rest) ← match rest with
      | [] => some ([], [])
      | '!' :: '=' :: '=' :: rest => some ([.ordinary (.punctuation "!==")], rest)
      | '`' :: rest => do
        let (head, interpolate, rest) ← templateSegment (rest.length + 1) rest
        if interpolate then
          let (substitutions, rest) ← templateRest (rest.length + 1) rest
          some ([.template head substitutions], rest)
        else some ([.template head []], rest)
      | '/' :: rest => do
        let (source, rest) ← regexpBody (rest.length + 1) rest
        let flags := rest.takeWhile Char.isAlpha
        if !flags.isEmpty then none else
        let ast ← ECMA2025.LabelRegExp.parseLiteral (47 :: source ++ [47])
        if !labelStartAnchored ast then none else
        some ([.regexp ⟨source, []⟩], rest)
      | _ => none
    if rest.isEmpty then some (tokens.map .ordinary ++ special) else
      let tail ← cacheTokens fuel rest
      some (tokens.map .ordinary ++ special ++ tail)

private def cacheSkip (tokens : List CacheToken) : List CacheToken :=
  tokens.dropWhile (fun token => match token with | .ordinary .lineBreak => true | _ => false)
private def cachePunct (symbol : String) (tokens : List CacheToken) : Option (List CacheToken) :=
  match cacheSkip tokens with | .ordinary (.punctuation found) :: rest => if found == symbol then some rest else none | _ => none

/-- Conservative ordinary leaves: no callback, increment, constructor or
method invokes hidden in templates/constructor operands. The dedicated source
label.match and NewExpression paths below have their actual closed dispatch. -/
private def cacheClosed : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, value => match value with
    | .invoke _ _ | .construct _ _ _ | .call _ _ _ | .preIncrement _ => false
    | .variable _ | .this | .number _ | .string _ | .boolean _ | .null => true
    | .index left right | .optionalIndex left right | .strictEqual left right | .subtract left right | .compare _ left right
    | .logicalAnd left right | .logicalOr left right | .nullish left right => cacheClosed fuel left && cacheClosed fuel right
    | .property value _ | .privateProperty value _ | .logicalNot value | .typeAssertion value _ => cacheClosed fuel value
    | .conditional test yes no => cacheClosed fuel test && cacheClosed fuel yes && cacheClosed fuel no
    | .arrayLiteral values => values.all (fun value => cacheClosed fuel value.2)
    | .objectLiteral values => values.all (fun value => cacheClosed fuel value.1 && cacheClosed fuel value.2)
private def cacheAllowed (value : Expr) (bindings : List String) : Bool :=
  expressionAdmitted value bindings [] true && cacheClosed 65536 value

mutual
  private def cacheExpr : Nat → List String → List CacheToken → Option (PatternCacheExpr × List CacheToken)
    | 0, _, _ => none
    | fuel + 1, bindings, tokens => do
      let (condition, rest) ← cacheAnd fuel bindings tokens
      match cacheSkip rest with
      | .ordinary (.punctuation "?") :: after =>
        let (yes, after) ← cacheExpr fuel bindings after
        let after ← cachePunct ":" after
        let (no, after) ← cacheExpr fuel bindings after
        some (.conditional condition yes no, after)
      | _ => some (condition, rest)
  private def cacheAnd : Nat → List String → List CacheToken → Option (PatternCacheExpr × List CacheToken)
    | 0, _, _ => none
    | fuel + 1, bindings, tokens => do
      let (head, rest) ← cacheEqual fuel bindings tokens
      cacheAndTail fuel bindings head rest
  private def cacheAndTail : Nat → List String → PatternCacheExpr → List CacheToken → Option (PatternCacheExpr × List CacheToken)
    | 0, _, _, _ => none
    | fuel + 1, bindings, left, tokens => do
      match cacheSkip tokens with
      | .ordinary (.punctuation "&&") :: rest =>
        let (right, rest) ← cacheEqual fuel bindings rest
        cacheAndTail fuel bindings (.logicalAnd left right) rest
      | _ => some (left, tokens)
  private def cacheEqual : Nat → List String → List CacheToken → Option (PatternCacheExpr × List CacheToken)
    | 0, _, _ => none
    | fuel + 1, bindings, tokens => do
      let (head, rest) ← cacheUnary fuel bindings tokens
      cacheEqualTail fuel bindings head rest
  private def cacheEqualTail : Nat → List String → PatternCacheExpr → List CacheToken → Option (PatternCacheExpr × List CacheToken)
    | 0, _, _, _ => none
    | fuel + 1, bindings, left, tokens => do
      match cacheSkip tokens with
      | .ordinary (.punctuation "!==") :: rest =>
        let (right, rest) ← cacheUnary fuel bindings rest
        cacheEqualTail fuel bindings (.strictNotEqual left right) rest
      | .ordinary (.punctuation "===") :: rest =>
        let (right, rest) ← cacheUnary fuel bindings rest
        cacheEqualTail fuel bindings (.strictEqual left right) rest
      | _ => some (left, tokens)
  private def cacheUnary : Nat → List String → List CacheToken → Option (PatternCacheExpr × List CacheToken)
    | 0, _, _ => none
    | fuel + 1, bindings, tokens => do
      match cacheSkip tokens with
      | .ordinary (.punctuation "!") :: rest =>
        let (value, rest) ← cacheUnary fuel bindings rest
        some (.logicalNot value, rest)
      | tokens =>
        let (head, rest) ← cachePrimary fuel bindings tokens
        cachePostfix fuel bindings head rest
  private def cachePostfix : Nat → List String → PatternCacheExpr → List CacheToken → Option (PatternCacheExpr × List CacheToken)
    | 0, _, _, _ => none
    | fuel + 1, bindings, head, tokens => do
      match cacheSkip tokens with
      | .ordinary (.punctuation "[") :: rest =>
        let (key, rest) ← cacheExpr fuel bindings rest
        let rest ← cachePunct "]" rest
        cachePostfix fuel bindings (.index head key) rest
      | _ => some (head, tokens)
  private def cachePrimary : Nat → List String → List CacheToken → Option (PatternCacheExpr × List CacheToken)
    | 0, _, _ => none
    | fuel + 1, bindings, tokens => do
      match cacheSkip tokens with
      | .ordinary (.name "new") :: .ordinary (.name callee) :: rest =>
        if !cacheAllowed (.variable callee) bindings then none else
        let rest ← cachePunct "(" rest
        let (argument, rest) ← cacheExpr fuel bindings rest
        let rest ← cachePunct ")" rest
        some (.construct (.variable callee) argument, rest)
      | .ordinary (.name receiver) :: .ordinary (.punctuation ".") :: .ordinary (.name method) :: rest =>
        if !bindings.contains receiver then none else
        let rest ← cachePunct "(" rest
        let (literal, rest) ← match cacheSkip rest with | .regexp literal :: rest => some (literal, rest) | _ => none
        let rest ← cachePunct ")" rest
        some (.labelMatch (.variable receiver) method literal, rest)
      | .ordinary (.name "true") :: rest => some (.ordinary (.boolean true), rest)
      | .ordinary (.name "false") :: rest => some (.ordinary (.boolean false), rest)
      | .ordinary (.name "null") :: rest => some (.ordinary .null, rest)
      | .ordinary (.name name) :: rest => if cacheAllowed (.variable name) bindings then some (.ordinary (.variable name), rest) else none
      | .ordinary (.number value) :: rest =>
        if cacheAllowed (.number value) bindings then some (.ordinary (.number value), rest) else none
      | .ordinary (.string value) :: rest => some (.ordinary (.string value), rest)
      | .template head substitutions :: rest =>
        if substitutions.all (fun entry => cacheAllowed entry.1 bindings) then some (.template head substitutions, rest) else none
      | .ordinary (.punctuation "[") :: rest =>
        let (values, rest) ← cacheElements fuel bindings rest
        some (.arrayLiteral values, rest)
      | .ordinary (.punctuation "{") :: rest =>
        let rest ← cachePunct "}" rest
        some (.emptyObject, rest)
      | .ordinary (.punctuation "(") :: rest =>
        let (value, rest) ← cacheExpr fuel bindings rest
        let rest ← cachePunct ")" rest
        some (value, rest)
      | _ => none
  private def cacheElements : Nat → List String → List CacheToken → Option (List PatternCacheExpr × List CacheToken)
    | 0, _, _ => none
    | fuel + 1, bindings, tokens => do
      match cacheSkip tokens with
      | .ordinary (.punctuation "]") :: rest => some ([], rest)
      | tokens =>
        let (value, rest) ← cacheExpr fuel bindings tokens
        match cacheSkip rest with
        | .ordinary (.punctuation "]") :: rest => some ([value], rest)
        | .ordinary (.punctuation ",") :: rest =>
          let (tail, rest) ← cacheElements fuel bindings rest
          some (value :: tail, rest)
        | _ => none
end

private def cacheStatementEnd (tokens : List CacheToken) : Option (List CacheToken) :=
  match tokens with
  | [] => some []
  | .ordinary .lineBreak :: rest => some (cacheSkip rest)
  | .ordinary (.punctuation ";") :: rest => some (cacheSkip rest)
  | .ordinary (.punctuation "}") :: _ => some tokens
  | _ => none

mutual
  private def cacheStatements : Nat → List String → List CacheToken → Option (List PatternCacheStmt × List CacheToken)
    | 0, _, _ => none
    | fuel + 1, bindings, tokens => do
      match cacheSkip tokens with
      | [] => some ([], [])
      | .ordinary (.punctuation "}") :: _ => some ([], cacheSkip tokens)
      | tokens =>
        let (head, introduced, rest) ← cacheStatement fuel bindings tokens
        let (tail, rest) ← cacheStatements fuel (introduced ++ bindings) rest
        some (head :: tail, rest)
  private def cacheStatement : Nat → List String → List CacheToken → Option (PatternCacheStmt × List String × List CacheToken)
    | 0, _, _ => none
    | fuel + 1, bindings, tokens => do
      match cacheSkip tokens with
      | .ordinary (.name "const") :: .ordinary (.name name) :: rest =>
        if !bindingNameAllowed name || bindings.contains name then none else
        let rest ← cachePunct "=" rest
        let (value, rest) ← cacheExpr fuel bindings rest
        let rest ← cacheStatementEnd rest
        some (.declare name value, [name], rest)
      | .ordinary (.name "if") :: rest =>
        let rest ← cachePunct "(" rest
        let (condition, rest) ← cacheExpr fuel bindings rest
        let rest ← cachePunct ")" rest
        let rest ← cachePunct "{" rest
        let (yes, rest) ← cacheStatements fuel bindings rest
        let rest ← cachePunct "}" rest
        let (no, rest) ← match cacheSkip rest with
          | .ordinary (.name "else") :: rest => do
            let rest ← cachePunct "{" rest
            let (body, rest) ← cacheStatements fuel bindings rest
            let rest ← cachePunct "}" rest
            some (body, rest)
          | _ => some ([], rest)
        some (.branch condition yes no, [], rest)
      | .ordinary (.name "return") :: rest =>
        if rest.head?.any (fun token => match token with | .ordinary .lineBreak => true | _ => false) then none else
        let (value, rest) ← cacheExpr fuel bindings rest
        let rest ← cacheStatementEnd rest
        some (.ret value, [], rest)
      | tokens =>
        let (target, rest) ← cacheExpr fuel bindings tokens
        let rest ← cachePunct "=" rest
        match target with | .index _ _ => pure () | _ => none
        let (value, rest) ← cacheExpr fuel bindings rest
        let rest ← cacheStatementEnd rest
        some (.assign target value, [], rest)
end

/-- Original structured selected program, including full nested if/else,
lookahead template and returns. No branch/body is fabricated or erased. -/
def parsePatternCacheBody (text : String) (bindings : List String) : Option (List PatternCacheStmt) := do
  if !bindings.all bindingNameAllowed then none else
  let tokens ← cacheTokens (text.toList.length + 1) text.toList
  let (program, rest) ← cacheStatements (16 * (tokens.length + 1)) bindings tokens
  if (cacheSkip rest).isEmpty then some program else none

def parsePatternCacheBlock (text : String) (bindings : List String) : Option (List PatternCacheStmt) := parsePatternCacheBody text bindings

/-- The actual TS index signature is retained grammar metadata. There is no
external erasure step and it does not add runtime tuple validation. -/
def parsePatternCacheInit (text : String) (bindings : List String := []) : Option PatternCacheInit := do
  if !bindings.all bindingNameAllowed then none else
  let tokens ← tokenizeFragment text
  let (name, rest) ← match skipTokenLines tokens with
    | .name "const" :: .name name :: rest => some (name, rest) | _ => none
  if !bindingNameAllowed name || bindings.contains name then none else
  let rest ← match skipTokenLines rest with | .punctuation ":" :: .punctuation "{" :: .punctuation "[" :: .name indexName :: .punctuation ":" :: rest => some (indexName, rest) | _ => none
  if !bindingNameAllowed rest.1 then none else
  let (indexType, tail) ← parseTypeTokens rest.2
  let tail ← match skipTokenLines tail with | .punctuation "]" :: .punctuation ":" :: tail => some tail | _ => none
  let (valueType, tail) ← parseTypeTokens tail
  let tail ← match skipTokenLines tail with | .punctuation "}" :: .punctuation "=" :: .punctuation "{" :: .punctuation "}" :: tail => some tail | _ => none
  let tail := skipTokenLines tail
  let tail := match tail with | .punctuation ";" :: tail => skipTokenLines tail | _ => tail
  if !tail.isEmpty then none else some ⟨name, rest.1, indexType, valueType, .emptyObject⟩

end HonoLean.Upstream.SourceSubset
