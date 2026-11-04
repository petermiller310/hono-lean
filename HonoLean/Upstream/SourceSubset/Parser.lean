import HonoLean.Upstream.SourceSubset.Syntax

namespace HonoLean.Upstream.SourceSubset

inductive Token where
  | name (text : String)
  | privateName (spelling : String)
  | string (contents : JSString)
  | number (value : Nat)
  | punctuation (text : String)
  | lineBreak
  deriving Repr, DecidableEq

private def identifierStart (c : Char) : Bool :=
  c == '_' || c == '$' || ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

private def identifierPart (c : Char) : Bool := identifierStart c || ('0' ≤ c && c ≤ '9')

private def quoted (delimiter : Char) : List Char → Option (JSString × List Char)
  | [] => none
  | c :: rest =>
    if c == delimiter then some ([], rest)
    else if c == '\\' || c == '\n' || c == '\r' || c.val > 127 then none
    else do
      let (contents, remaining) ← quoted delimiter rest
      return (UInt16.ofNat c.toNat :: contents, remaining)

/-- A fail-closed ASCII lexer. Comments, escapes and unsupported operators reject. -/
private def lex : Nat → List Char → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, c :: rest => do
    if c == '\n' || c == '\r' then
      return .lineBreak :: (← lex fuel rest)
    else if c == ' ' || c == '\t' then
      lex fuel rest
    else if identifierStart c then
      let letters := rest.takeWhile identifierPart
      let tail ← lex fuel (rest.dropWhile identifierPart)
      return .name (String.ofList (c :: letters)) :: tail
    else if c == '#' then
      match rest with
      | first :: remaining =>
        if identifierStart first then
          let letters := remaining.takeWhile identifierPart
          let tail ← lex fuel (remaining.dropWhile identifierPart)
          return .privateName (String.ofList (first :: letters)) :: tail
        else none
      | [] => none
    else if '0' ≤ c && c ≤ '9' then
      let digits := rest.takeWhile (fun c => '0' ≤ c && c ≤ '9')
      if c == '0' && !digits.isEmpty then none else do
      let number ← (String.ofList (c :: digits)).toNat?
      if number > 9007199254740991 then none else do
      let tail ← lex fuel (rest.dropWhile (fun c => '0' ≤ c && c ≤ '9'))
      return .number number :: tail
    else if c == '\'' || c == '"' then
      let (contents, remaining) ← quoted c rest
      return .string contents :: (← lex fuel remaining)
    else if c == '=' then
      match rest with
      | '=' :: '=' :: remaining => return .punctuation "===" :: (← lex fuel remaining)
      | '>' :: remaining => return .punctuation "=>" :: (← lex fuel remaining)
      | _ => return .punctuation "=" :: (← lex fuel rest)
    else if c == '<' then
      match rest with
      | '=' :: remaining => return .punctuation "<=" :: (← lex fuel remaining)
      | _ => return .punctuation "<" :: (← lex fuel rest)
    else if c == '?' then
      match rest with
      | '?' :: remaining => return .punctuation "??" :: (← lex fuel remaining)
      | '.' :: remaining =>
        -- OptionalChainingPunctuator is adjacent `?.`, with no following
        -- decimal digit. Decimal literals themselves remain unsupported.
        match remaining with
        | digit :: _ =>
          if '0' ≤ digit && digit ≤ '9' then none
          else return .punctuation "?." :: (← lex fuel remaining)
        | [] => return [.punctuation "?."]
      | _ => return .punctuation "?" :: (← lex fuel rest)
    else if c == '&' then
      match rest with
      | '&' :: remaining => return .punctuation "&&" :: (← lex fuel remaining)
      | _ => none
    else if c == '|' then
      match rest with
      | '|' :: '=' :: remaining => return .punctuation "||=" :: (← lex fuel remaining)
      | '|' :: remaining => return .punctuation "||" :: (← lex fuel remaining)
      | _ => return .punctuation "|" :: (← lex fuel rest)
    else if c == '+' then
      match rest with
      | '+' :: remaining => return .punctuation "++" :: (← lex fuel remaining)
      | _ => none
    else if c == '-' then
      -- Native maximal munch makes adjacent `--` a decrement token. That
      -- operator is outside this subset; never reinterpret it as two minuses.
      match rest with
      | '-' :: _ => none
      | _ => return .punctuation "-" :: (← lex fuel rest)
    else if c == '.' then
      match rest with
      | '.' :: '.' :: remaining => return .punctuation "..." :: (← lex fuel remaining)
      | _ => return .punctuation "." :: (← lex fuel rest)
    else if [':', '!', '>', '(', ')', '[', ']', '{', '}', ',', ';'].contains c then
      return .punctuation (String.singleton c) :: (← lex fuel rest)
    else none

private abbrev Parser (α : Type) := List Token → Option (α × List Token)

/-- Each nesting level passes through precedence layers as well as consuming
tokens. Reserve a fixed number of syntax steps per token, so short nested
expressions do not fail merely because of the number of grammar layers. -/
private def syntaxFuel (tokens : List Token) : Nat := 16 * (tokens.length + 1)

private def skipLines (tokens : List Token) : List Token :=
  tokens.dropWhile (fun token => match token with | .lineBreak => true | _ => false)

private def comparisonToken : Token → Bool
  | .punctuation "<" | .punctuation "<=" => true
  | _ => false

private def bindingIdentifier (name : String) : Bool :=
  !(["await", "break", "case", "catch", "class", "const", "continue", "debugger",
    "default", "delete", "do", "else", "enum", "export", "extends", "false", "finally",
    "for", "function", "if", "import", "in", "instanceof", "new", "null", "return",
    "super", "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while",
    "with", "yield", "let", "static", "implements", "interface", "package", "private",
    "protected", "public", "arguments", "eval", "string"].contains name)

private def typeNameAllowed (name : String) : Bool :=
  (bindingIdentifier name || ["string", "number", "boolean", "object", "any", "unknown", "never", "symbol", "bigint", "undefined", "void", "null"].contains name) &&
    !(["as", "keyof", "readonly", "infer", "is", "out", "unique", "asserts", "satisfies"].contains name)

mutual
  private def typeSyntax : Nat → Parser TypeSyntax
    | 0, _ => none
    | fuel + 1, tokens => do
      let (base, rest) ← typePrimary fuel tokens
      typeUnionTail fuel base rest

  private def typePrimary : Nat → Parser TypeSyntax
    | 0, _ => none
    | fuel + 1, tokens => do
      let (base, rest) ← match skipLines tokens with
        | .name name :: rest => if typeNameAllowed name then some (TypeSyntax.named name, rest) else none
        | _ => none
      let (base, rest) ← match skipLines rest with
        | .punctuation "<" :: rest => do
          let (arguments, rest) ← typeArguments fuel (skipLines rest)
          some (.application base arguments, rest)
        | _ => some (base, rest)
      arrayTypeSuffix fuel base rest

  private def typeUnionTail : Nat → TypeSyntax → Parser TypeSyntax
    | 0, _, _ => none
    | fuel + 1, base, tokens =>
      match skipLines tokens with
      | .punctuation "|" :: rest => do
        let (right, rest) ← typePrimary fuel rest
        typeUnionTail fuel (.union base right) rest
      | _ => some (base, tokens)

  private def typeArguments : Nat → Parser (List TypeSyntax)
    | 0, _ => none
    | fuel + 1, tokens => do
      let (head, rest) ← typeSyntax fuel tokens
      match skipLines rest with
      | .punctuation ">" :: rest => some ([head], rest)
      | .punctuation "," :: rest =>
        let (tail, rest) ← typeArguments fuel (skipLines rest)
        some (head :: tail, rest)
      | _ => none

  private def arrayTypeSuffix : Nat → TypeSyntax → Parser TypeSyntax
    | 0, _, _ => none
    | fuel + 1, base, tokens =>
      match skipLines tokens with
      | .punctuation "[" :: rest =>
        match skipLines rest with
        | .punctuation "]" :: rest => arrayTypeSuffix fuel (.array base) rest
        | _ => none
      | _ => some (base, tokens)
end

private def constAssertionOperand : Expr → Bool
  | .string _ | .number _ | .boolean _ | .arrayLiteral _ | .objectLiteral _ => true
  | _ => false

mutual
  private def expression : Nat → Parser Expr
    | 0, _ => none
    | fuel + 1, tokens => do
      let (test, rest) ← shortCircuit fuel tokens
      -- A line break may continue an already-started expression with `?`.
      -- It is never skipped at the start of a return expression (ASI).
      match skipLines rest with
      | .punctuation "?" :: remaining =>
        let (yes, remaining) ← expression fuel (skipLines remaining)
        match skipLines remaining with
        | .punctuation ":" :: remaining =>
          let (no, remaining) ← expression fuel (skipLines remaining)
          return (.conditional test yes no, remaining)
        | _ => none
      | _ => return (test, rest)

  private def shortCircuit : Nat → Parser Expr
    | 0, _ => none
    | fuel + 1, tokens => do
      let (left, rest) ← equality fuel tokens
      match skipLines rest with
      | .punctuation "??" :: _ => nullishTail fuel left rest
      | _ =>
        let (left, rest) ← andTail fuel left rest
        orTail fuel left rest

  private def orTail : Nat → Expr → Parser Expr
    | 0, _, _ => none
    | fuel + 1, left, tokens => do
      match skipLines tokens with
      | .punctuation "||" :: rest =>
        let (right, rest) ← equality fuel (skipLines rest)
        let (right, rest) ← andTail fuel right rest
        orTail fuel (.logicalOr left right) rest
      | .punctuation "??" :: _ => none
      | _ => return (left, tokens)

  private def andTail : Nat → Expr → Parser Expr
    | 0, _, _ => none
    | fuel + 1, left, tokens => do
      match skipLines tokens with
      | .punctuation "&&" :: rest =>
        let (right, rest) ← equality fuel (skipLines rest)
        andTail fuel (.logicalAnd left right) rest
      | .punctuation "??" :: _ => none
      | _ => return (left, tokens)

  private def nullishTail : Nat → Expr → Parser Expr
    | 0, _, _ => none
    | fuel + 1, left, tokens => do
      match skipLines tokens with
      | .punctuation "??" :: rest =>
        let (right, rest) ← equality fuel (skipLines rest)
        nullishTail fuel (.nullish left right) rest
      | .punctuation "&&" :: _ | .punctuation "||" :: _ => none
      | _ => return (left, tokens)

  private def equality : Nat → Parser Expr
    | 0, _ => none
    | fuel + 1, tokens => do
      let (left, rest) ← assertion fuel tokens
      match rest with
      | .punctuation "===" :: rest =>
        let (right, rest) ← assertion fuel (skipLines rest)
        match rest with
        | .punctuation "===" :: _ => none
        | _ => return (.strictEqual left right, rest)
      | _ => return (left, rest)

  private def assertion : Nat → Parser Expr
    | 0, _ => none
    | fuel + 1, tokens => do
      let (left, rest) ← relational fuel tokens
      assertionTail fuel left rest

  private def assertionTail : Nat → Expr → Parser Expr
    | 0, _, _ => none
    | fuel + 1, value, tokens => do
      match tokens with
      | .name "as" :: rest =>
        let (annotation, rest) ← match skipLines rest with
          | .name "const" :: rest =>
            if constAssertionOperand value then some (TypeSyntax.constAssertion, rest) else none
          | rest => typeSyntax fuel rest
        assertionTail fuel (.typeAssertion value annotation) rest
      | _ => some (value, tokens)

  private def relational : Nat → Parser Expr
    | 0, _ => none
    | fuel + 1, tokens => do
      let (left, rest) ← additive fuel tokens
      let operation := match rest with
        | .punctuation "<" :: _ => some NumericComparison.less
        | .punctuation "<=" :: _ => some NumericComparison.lessEqual
        | _ => none
      match operation, rest with
      | some operation, _ :: rest =>
        let (right, rest) ← additive fuel (skipLines rest)
        if rest.head?.any comparisonToken then none
        else return (.compare operation left right, rest)
      | _, _ => return (left, rest)

  private def additive : Nat → Parser Expr
    | 0, _ => none
    | fuel + 1, tokens => do
      let (left, rest) ← unary fuel tokens
      subtractTail fuel left rest

  private def subtractTail : Nat → Expr → Parser Expr
    | 0, _, _ => none
    | fuel + 1, left, tokens =>
      match skipLines tokens with
      | .punctuation "-" :: rest => do
        let (right, rest) ← unary fuel (skipLines rest)
        subtractTail fuel (.subtract left right) rest
      | _ => some (left, tokens)

  private def unary : Nat → Parser Expr
    | 0, _ => none
    | fuel + 1, tokens => do
      match tokens with
      | .punctuation "++" :: rest =>
        match skipLines rest with
        | .name name :: rest =>
          match skipLines rest with
          | .punctuation "." :: _ | .punctuation "[" :: _
          | .punctuation "?." :: _ | .punctuation "(" :: _ => none
          | _ => some (.preIncrement name, rest)
        | _ => none
      | .punctuation "!" :: rest =>
        let (value, rest) ← unary fuel (skipLines rest)
        return (.logicalNot value, rest)
      | _ => primary fuel tokens

  private def primary : Nat → Parser Expr
    | 0, _ => none
    | fuel + 1, tokens => do
      let (first, rest) ← match tokens with
        | .name "new" :: rest => do
          let (callee, rest) ← match skipLines rest with
            | .name name :: rest => some (Expr.variable name, rest)
            | _ => none
          let (typeArgument, rest) ← match skipLines rest with
            | .punctuation "<" :: rest =>
              match skipLines rest with
              | .name "string" :: rest =>
                match skipLines rest with
                | .punctuation ">" :: rest => some (some ConstructorType.string, rest)
                | _ => none
              | _ => none
            | _ => some (none, rest)
          let (args, rest) ← match skipLines rest with
            | .punctuation "(" :: rest => arguments fuel (skipLines rest)
            | _ => none
          some (.construct callee typeArgument args, rest)
        | .punctuation "[" :: rest => do
          let (elements, rest) ← arrayElements fuel (skipLines rest)
          some (.arrayLiteral elements, rest)
        | .punctuation "{" :: rest => do
          let (fields, rest) ← objectFields fuel (skipLines rest)
          some (.objectLiteral fields, rest)
        | .name "this" :: rest => some (Expr.this, rest)
        | .name "null" :: rest => some (Expr.null, rest)
        | .name "true" :: rest => some (Expr.boolean true, rest)
        | .name "false" :: rest => some (Expr.boolean false, rest)
        | .name name :: rest => some (Expr.variable name, rest)
        | .string contents :: rest => some (.string contents, rest)
        | .number value :: rest => some (.number (Int.ofNat value), rest)
        | .punctuation "-" :: .number value :: rest =>
          if value = 0 then none else some (.number (-(Int.ofNat value)), rest)
        | .punctuation "(" :: rest => do
          let (value, rest) ← expression fuel (skipLines rest)
          match skipLines rest with
          | .punctuation ")" :: rest => some (value, rest)
          | _ => none
        | _ => none
      match first, rest with
      -- JS numeric-literal/dot tokenization differs from identifier access.
      -- This subset needs no numeric-literal receiver, so reject those suffixes.
      | .number _, .punctuation "." :: _ => none
      | .number _, .punctuation "[" :: _ => none
      | .number _, .punctuation "?." :: _ => none
      | _, _ => suffix fuel first rest

  private def suffix : Nat → Expr → Parser Expr
    | 0, _, _ => none
    | fuel + 1, receiver, tokens => do
      match tokens with
      | .punctuation "(" :: rest =>
        let (args, rest) ← arguments fuel rest
        suffix fuel (.invoke receiver args) rest
      | .punctuation "." :: .name method :: .punctuation "(" :: rest =>
        let (args, rest) ← arguments fuel rest
        suffix fuel (.call receiver method args) rest
      | .punctuation "." :: .name property :: rest =>
        suffix fuel (.property receiver (property.toList.map (fun char => UInt16.ofNat char.toNat))) rest
      | .punctuation "." :: .privateName spelling :: rest =>
        suffix fuel (.privateProperty receiver spelling) rest
      | .punctuation "?." :: .punctuation "[" :: rest =>
        let (key, rest) ← expression fuel (skipLines rest)
        match skipLines rest with
        | .punctuation "]" :: rest =>
          -- Chained optional access would need to preserve the whole optional
          -- chain's short-circuit extent. This slice supports one optional
          -- computed access; grouping can explicitly end that chain.
          return (.optionalIndex receiver key, rest)
        | _ => none
      | .punctuation "[" :: rest =>
        let (key, rest) ← expression fuel rest
        match rest with
        | .punctuation "]" :: rest => suffix fuel (.index receiver key) rest
        | _ => none
      | _ => return (receiver, tokens)

  private def arguments : Nat → Parser (List Expr)
    | 0, _ => none
    | fuel + 1, tokens => do
      match tokens with
      | .punctuation ")" :: rest => return ([], rest)
      | _ =>
        let (arg, rest) ← expression fuel tokens
        match rest with
        | .punctuation ")" :: rest => return ([arg], rest)
        | .punctuation "," :: rest =>
          let (args, rest) ← arguments fuel rest
          return (arg :: args, rest)
        | _ => none

  private def arrayElements : Nat → Parser (List (Bool × Expr))
    | 0, _ => none
    | fuel + 1, tokens => do
      match skipLines tokens with
      | .punctuation "]" :: rest => some ([], rest)
      | tokens =>
        let (spread, tokens) := match tokens with
          | .punctuation "..." :: rest => (true, skipLines rest)
          | _ => (false, tokens)
        let (value, rest) ← expression fuel tokens
        match skipLines rest with
        | .punctuation "]" :: rest => some ([(spread, value)], rest)
        | .punctuation "," :: rest =>
          let (tail, rest) ← arrayElements fuel (skipLines rest)
          some ((spread, value) :: tail, rest)
        | _ => none

  private def objectFields : Nat → Parser (List (Expr × Expr))
    | 0, _ => none
    | fuel + 1, tokens => do
      match skipLines tokens with
      | .punctuation "}" :: rest => some ([], rest)
      | tokens =>
        let (key, value, rest) ← match tokens with
          | .punctuation "[" :: rest => do
            let (key, rest) ← expression fuel (skipLines rest)
            let rest ← match skipLines rest with
              | .punctuation "]" :: rest => some (skipLines rest)
              | _ => none
            match rest with
            | .punctuation ":" :: rest => do
              let (value, rest) ← expression fuel (skipLines rest)
              some (key, value, rest)
            | _ => none
          | .name name :: .punctuation ":" :: rest => do
            if name == "__proto__" then none else do
              let (value, rest) ← expression fuel (skipLines rest)
              some (.string (name.toList.map (fun char => UInt16.ofNat char.toNat)), value, rest)
          | .string contents :: .punctuation ":" :: rest => do
            if contents == [95,95,112,114,111,116,111,95,95] then none else do
              let (value, rest) ← expression fuel (skipLines rest)
              some (.string contents, value, rest)
          | .name name :: rest =>
            some (.string (name.toList.map (fun char => UInt16.ofNat char.toNat)), .variable name, rest)
          | _ => none
        match skipLines rest with
        | .punctuation "}" :: rest => some ([(key, value)], rest)
        | .punctuation "," :: rest =>
          let (tail, rest) ← objectFields fuel (skipLines rest)
          some ((key, value) :: tail, rest)
        | _ => none
end

/-- Enforce a real simple-statement boundary. In particular return-newline is
not silently reinterpreted, and missing same-line semicolons do not get erased. -/
private def statementEnd : List Token → Option (List Token)
  | .punctuation ";" :: rest => some rest
  | .lineBreak :: rest =>
    -- These tokens would continue the preceding expression in JS rather
    -- than start a new ASI-separated statement. Unsupported continuations
    -- must not become differently behaving standalone grouped expressions.
    match skipLines rest with
    | .punctuation "-" :: _ | .punctuation "(" :: _ | .punctuation "[" :: _
    | .punctuation "." :: _ | .punctuation "?." :: _ => none
    | _ => some rest
  | .punctuation "}" :: rest => some (.punctuation "}" :: rest)
  | _ => none

mutual
  private def initializers : Nat → Parser (List (String × Expr))
    | 0, _ => none
    | fuel + 1, tokens => do
      match skipLines tokens with
      | .name name :: .punctuation "=" :: rest =>
        let (value, rest) ← expression fuel (skipLines rest)
        match skipLines rest with
        | .punctuation "," :: rest =>
          let (tail, rest) ← initializers fuel rest
          return ((name, value) :: tail, rest)
        | .punctuation ";" :: rest => return ([(name, value)], rest)
        | _ => none
      | _ => none

  private def statement : Nat → Parser Stmt
    | 0, _ => none
    | fuel + 1, tokens => do
      match tokens with
      | .punctuation "{" :: _ => none
      | .name "for" :: .punctuation "(" :: .name "let" :: rest =>
        let (bindings, rest) ← initializers fuel rest
        let (condition, rest) ← expression fuel (skipLines rest)
        let rest ← match skipLines rest with
          | .punctuation ";" :: rest => some (skipLines rest)
          | _ => none
        match rest with
        | .name incrementName :: .punctuation "++" :: .punctuation ")" :: .punctuation "{" :: rest =>
          let (body, rest) ← statements fuel rest
          return (.countedFor bindings condition incrementName body, rest)
        | _ => none
      | .name "const" :: .name name :: .punctuation "=" :: rest =>
        let (value, rest) ← expression fuel rest
        return (.declare name value, ← statementEnd rest)
      | .name "const" :: .name name :: .punctuation ":" :: rest =>
        let (annotation, rest) ← typeSyntax fuel (skipLines rest)
        match skipLines rest with
        | .punctuation "=" :: rest =>
          let (value, rest) ← expression fuel (skipLines rest)
          return (.typedDeclare name annotation value, ← statementEnd rest)
        | _ => none
      | .name "let" :: .name name :: .punctuation "=" :: rest =>
        let (value, rest) ← expression fuel rest
        return (.mutableDeclare name none value, ← statementEnd rest)
      | .name "let" :: .name name :: .punctuation ":" :: rest =>
        let (annotation, rest) ← typeSyntax fuel (skipLines rest)
        match skipLines rest with
        | .punctuation "=" :: rest =>
          let (value, rest) ← expression fuel (skipLines rest)
          return (.mutableDeclare name (some annotation) value, ← statementEnd rest)
        | _ => none
      | .name "return" :: rest =>
        let (value, rest) ← expression fuel rest
        return (.ret value, ← statementEnd rest)
      | .name "if" :: .punctuation "(" :: rest =>
        let (test, rest) ← expression fuel rest
        match rest with
        | .punctuation ")" :: .punctuation "{" :: rest =>
          let (body, rest) ← statements fuel rest
          return (.branch test body, rest)
        | _ => none
      | _ =>
        let (value, rest) ← expression fuel tokens
        match skipLines rest with
        | .punctuation "=" :: rest =>
          let (rhs, rest) ← expression fuel (skipLines rest)
          return (.assign ⟨value, rhs⟩, ← statementEnd rest)
        | _ => return (.evaluate value, ← statementEnd rest)

  private def statements : Nat → Parser (List Stmt)
    | 0, _ => none
    | fuel + 1, tokens => do
      let tokens := skipLines tokens
      match tokens with
      | .punctuation "}" :: rest => return ([], rest)
      | _ =>
        let (head, rest) ← statement fuel tokens
        let (tail, rest) ← statements fuel rest
        return (head :: tail, rest)
end

private def validExprCore (allowThis : Bool) : Nat → List String → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, bindings, expression =>
    match expression with
    | .variable name => bindingIdentifier name &&
        (bindings.contains name || name == "Object" || name == "Set")
    | .this => allowThis
    | .string _ => true
    | .number value => value.natAbs ≤ 9007199254740991
    | .null => true
    | .boolean _ => true
    | .property receiver _ => validExprCore allowThis fuel bindings receiver
    | .optionalIndex receiver key => validExprCore allowThis fuel bindings receiver && validExprCore allowThis fuel bindings key
    | .logicalNot value => validExprCore allowThis fuel bindings value
    | .logicalAnd left right => validExprCore allowThis fuel bindings left && validExprCore allowThis fuel bindings right
    | .logicalOr left right => validExprCore allowThis fuel bindings left && validExprCore allowThis fuel bindings right
    | .nullish left right => validExprCore allowThis fuel bindings left && validExprCore allowThis fuel bindings right
    | .typeAssertion value _ => validExprCore allowThis fuel bindings value
    | .invoke callee args => validExprCore allowThis fuel bindings callee && args.isEmpty
    | .construct callee _ args => validExprCore allowThis fuel bindings callee && args.isEmpty
    | .arrayLiteral elements => elements.all (fun element => validExprCore allowThis fuel bindings element.2)
    | .objectLiteral fields => fields.all (fun field =>
        validExprCore allowThis fuel bindings field.1 && validExprCore allowThis fuel bindings field.2)
    | .preIncrement name => bindingIdentifier name && bindings.contains name
    | .privateProperty receiver _ => validExprCore allowThis fuel bindings receiver
    | .index receiver key => validExprCore allowThis fuel bindings receiver && validExprCore allowThis fuel bindings key
    | .strictEqual left right => validExprCore allowThis fuel bindings left && validExprCore allowThis fuel bindings right
    | .compare _ left right => validExprCore allowThis fuel bindings left && validExprCore allowThis fuel bindings right
    | .subtract left right => validExprCore allowThis fuel bindings left && validExprCore allowThis fuel bindings right
    | .conditional test yes no => validExprCore allowThis fuel bindings test &&
        validExprCore allowThis fuel bindings yes && validExprCore allowThis fuel bindings no
    | .call receiver method args =>
      validExprCore allowThis fuel bindings receiver &&
        ((method == "split" && (match args with | [.string [_]] => true | _ => false)) ||
         (method == "shift" && args.isEmpty) ||
         (method == "indexOf" && (match args with
           | [.string [_], position] => validExprCore allowThis fuel bindings position
           | _ => false)) ||
         (method == "slice" && (match args with
           | [start] => validExprCore allowThis fuel bindings start
           | [start, stop] => validExprCore allowThis fuel bindings start && validExprCore allowThis fuel bindings stop
           | _ => false)) ||
         (method == "create" && (match args with
           | [prototype] => validExprCore allowThis fuel bindings prototype
           | _ => false)) ||
         (method == "hasOwn" && (match args with
           | [receiver, key] => validExprCore allowThis fuel bindings receiver && validExprCore allowThis fuel bindings key
           | _ => false)) ||
         (method == "push" && args.all (validExprCore allowThis fuel bindings)) ||
         -- Set.add's runtime domain is checked by the interpreter.
         (method == "add" && (match args with
           | [key] => validExprCore allowThis fuel bindings key
           | _ => false)))

private def validInitializersCore (allowThis : Bool) : Nat → List String → List (String × Expr) → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, available, (name, value) :: rest =>
    bindingIdentifier name && name != "Object" && name != "Set" && !available.contains name &&
      validExprCore allowThis fuel available value && validInitializersCore allowThis fuel (name :: available) rest

private def validExpr (fuel : Nat) (bindings : List String) (value : Expr) : Bool :=
  validExprCore false fuel bindings value

private def assignmentTarget : Expr → Bool
  | .index _ _ | .property _ _ | .privateProperty _ _ => true
  | _ => false

/-- Lexical private-name admission is independent of public variable binding.
The class declaration/frontend establishing this scope is outside the fragment. -/
private def privateExpressionAllowed : Nat → List String → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, scope, value =>
    match value with
    | .variable _ | .this | .string _ | .number _ | .boolean _ | .null | .preIncrement _ => true
    | .privateProperty receiver spelling =>
      scope.contains spelling && privateExpressionAllowed fuel scope receiver
    | .index receiver key | .optionalIndex receiver key | .strictEqual receiver key | .subtract receiver key
    | .compare _ receiver key | .logicalAnd receiver key | .logicalOr receiver key | .nullish receiver key =>
      privateExpressionAllowed fuel scope receiver && privateExpressionAllowed fuel scope key
    | .property receiver _ | .logicalNot receiver | .typeAssertion receiver _ => privateExpressionAllowed fuel scope receiver
    | .call receiver _ arguments | .invoke receiver arguments | .construct receiver _ arguments =>
      privateExpressionAllowed fuel scope receiver && arguments.all (privateExpressionAllowed fuel scope)
    | .conditional test yes no => privateExpressionAllowed fuel scope test &&
      privateExpressionAllowed fuel scope yes && privateExpressionAllowed fuel scope no
    | .arrayLiteral elements => elements.all (fun element => privateExpressionAllowed fuel scope element.2)
    | .objectLiteral fields => fields.all (fun field =>
      privateExpressionAllowed fuel scope field.1 && privateExpressionAllowed fuel scope field.2)

private def privateStatementsAllowed : Nat → List String → List Stmt → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, scope, head :: tail =>
    let headAllowed := match head with
      | .declare _ expression | .typedDeclare _ _ expression | .mutableDeclare _ _ expression
      | .evaluate expression | .ret expression => privateExpressionAllowed fuel scope expression
      | .assign assignment => privateExpressionAllowed fuel scope assignment.target &&
          privateExpressionAllowed fuel scope assignment.value
      | .branch condition body => privateExpressionAllowed fuel scope condition && privateStatementsAllowed fuel scope body
      | .countedFor initializers condition _ body =>
          initializers.all (fun initializer => privateExpressionAllowed fuel scope initializer.2) &&
            privateExpressionAllowed fuel scope condition && privateStatementsAllowed fuel scope body
    headAllowed && privateStatementsAllowed fuel scope tail

private def validStatementsCore (allowThis : Bool) : Nat → Bool → List String → List Stmt → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => true
  | fuel + 1, allowDeclarations, bindings, head :: tail =>
    match head with
    | .declare name initializer | .typedDeclare name _ initializer | .mutableDeclare name _ initializer =>
      -- A local Object declaration has block-wide TDZ/shadowing effects; this
      -- subset models explicit ambient lookup but no lexical TDZ machinery.
      allowDeclarations && bindingIdentifier name && name != "Object" && name != "Set" && !bindings.contains name &&
        validExprCore allowThis fuel bindings initializer &&
        validStatementsCore allowThis fuel allowDeclarations (name :: bindings) tail
    | .evaluate expression =>
      validExprCore allowThis fuel bindings expression && validStatementsCore allowThis fuel allowDeclarations bindings tail
    | .ret expression =>
      validExprCore allowThis fuel bindings expression && validStatementsCore allowThis fuel allowDeclarations bindings tail
    | .assign assignment =>
      assignmentTarget assignment.target && validExprCore allowThis fuel bindings assignment.target &&
        validExprCore allowThis fuel bindings assignment.value && validStatementsCore allowThis fuel allowDeclarations bindings tail
    | .countedFor initializers condition incrementName body =>
      let names := initializers.map Prod.fst
      let outer := bindings.filter (fun name => !names.contains name)
      let header := names.reverse ++ outer
      let bodyNames := declaredNames body
      let bodyBindings := header.filter (fun name => !bodyNames.contains name)
      !initializers.isEmpty && decide names.Nodup &&
        validInitializersCore allowThis fuel outer initializers && names.contains incrementName &&
        validExprCore allowThis fuel header condition && validStatementsCore allowThis fuel true bodyBindings body &&
        validStatementsCore allowThis fuel allowDeclarations bindings tail
    | .branch condition body =>
      validExprCore allowThis fuel bindings condition && validStatementsCore allowThis fuel false bindings body &&
        validStatementsCore allowThis fuel allowDeclarations bindings tail

private def validStatements (fuel : Nat) (declarations : Bool) (bindings : List String) (body : List Stmt) : Bool :=
  validStatementsCore false fuel declarations bindings body

/-- Check the entire supported declaration, including its TypeScript annotations.
Fuel bounds source syntax traversal only, never the input string length. This
is a syntax/binding checker, not a proof that every accepted program uses only
welltyped interpreter operations or an adequate semantics of all JavaScript. -/
private def parseResult (arrayResult : Bool) (text : String) : Option Function := do
  let tokens ← lex (text.toList.length + 1) text.toList
  match tokens with
  | .name "export" :: .name "const" :: .name name :: .punctuation "=" ::
      .punctuation "(" :: .name parameter :: .punctuation ":" :: .name "string" ::
      .punctuation ")" :: .punctuation ":" :: .name "string" :: remaining =>
    let remaining ← if arrayResult then
      match remaining with
      | .punctuation "[" :: .punctuation "]" :: rest => some rest
      | _ => none
      else some remaining
    let rest ← match remaining with
      | .punctuation "=>" :: .punctuation "{" :: rest => some rest
      | _ => none
    let (body, rest) ← statements (syntaxFuel tokens) rest
    if (skipLines rest).isEmpty && bindingIdentifier name && name != "Object" && name != "Set" &&
        bindingIdentifier parameter &&
        validStatements (tokens.length + 1) true [parameter] body &&
        privateStatementsAllowed (syntaxFuel tokens) [] body then
      some ⟨name, parameter, body⟩ else none
  | _ => none

/-- Existing array-result parser; shared syntax implementation with parseString. -/
def parse (text : String) : Option Function := parseResult true text

/-- Same lexer, expression precedence and statements, checking a string result. -/
def parseString (text : String) : Option Function := parseResult false text

/-- General zero-parameter expression-bodied declaration. The same lexer,
precedence parser and free-variable validator handle its body. `Object` is the
one explicitly supported ambient binding, resolved by the interpreter. -/
def parseNoArg (text : String) : Option NoArgFunction := do
  let tokens ← lex (text.toList.length + 1) text.toList
  match tokens with
  | .name "export" :: .name "const" :: .name name :: .punctuation "=" ::
      .punctuation "(" :: .punctuation ")" :: .punctuation "=>" :: rest =>
    -- An unparenthesized `{` starts an arrow statement body, not a literal.
    match skipLines rest with
    | .punctuation "{" :: _ => none
    | _ => pure ()
    let (body, rest) ← expression (syntaxFuel tokens) rest
    let rest := match rest with
      | .punctuation ";" :: remaining => remaining
      | _ => rest
    -- A declaration named Object would shadow the ambient builtin with its
    -- own function binding, whose recursive identity is outside this subset.
    if (skipLines rest).isEmpty && bindingIdentifier name && name != "Object" && name != "Set" &&
        validExpr (tokens.length + 1) [] body &&
        privateExpressionAllowed (syntaxFuel tokens) [] body then some ⟨name, body⟩ else none
  | _ => none

/-- One generic property assignment. The lvalue and RHS use the shared source
expression parser; optional assignment targets and free unknown names reject. -/
def parseAssignment (text : String) (allowedBindings : List String)
    (allowedPrivateNames : List String := []) (allowThis : Bool := false) : Option Assignment := do
  let tokens ← lex (text.toList.length + 1) text.toList
  let (target, rest) ← expression (syntaxFuel tokens) (skipLines tokens)
  let rest ← match skipLines rest with
    | .punctuation "=" :: rest => some rest
    | _ => none
  let (value, rest) ← expression (syntaxFuel tokens) (skipLines rest)
  let rest := match rest with
    | .punctuation ";" :: remaining => remaining
    | _ => rest
  let targetAllowed := assignmentTarget target
  if targetAllowed && (skipLines rest).isEmpty &&
      allowedBindings.all bindingIdentifier &&
      validExprCore allowThis (tokens.length + 1) allowedBindings target &&
      validExprCore allowThis (tokens.length + 1) allowedBindings value &&
      privateExpressionAllowed (syntaxFuel tokens) allowedPrivateNames target &&
      privateExpressionAllowed (syntaxFuel tokens) allowedPrivateNames value then
    some ⟨target, value⟩ else none

/-- A standalone statement sequence using the existing block parser's EOF
boundary. All real tokens must be consumed; this is fragment syntax, not a
whole module or a Node recognizer. -/
def parseBlock (text : String) (allowedBindings : List String)
    (allowedPrivateNames : List String := []) (allowThis : Bool := false) : Option (List Stmt) := do
  let tokens ← lex (text.toList.length + 1) text.toList
  let (body, rest) ← statements (syntaxFuel tokens) (tokens ++ [.punctuation "}"])
  let bindings := allowedBindings.filter (fun name => !(declaredNames body).contains name)
  if rest.isEmpty && allowedBindings.all bindingIdentifier &&
      validStatementsCore allowThis (syntaxFuel tokens) true bindings body &&
      privateStatementsAllowed (syntaxFuel tokens) allowedPrivateNames body then some body else none

/-- Complete expression-fragment parsing using the same lexer and grammar. -/
def parseExpression (text : String) (allowedBindings : List String)
    (allowedPrivateNames : List String := []) (allowThis : Bool := false) : Option Expr := do
  let tokens ← lex (text.toList.length + 1) text.toList
  let (value, rest) ← expression (syntaxFuel tokens) (skipLines tokens)
  if (skipLines rest).isEmpty && allowedBindings.all bindingIdentifier &&
      validExprCore allowThis (syntaxFuel tokens) allowedBindings value &&
      privateExpressionAllowed (syntaxFuel tokens) allowedPrivateNames value then some value else none

/-- Field declarations admit semicolons, newlines or EOF, but do not erase a
same-line missing separator or an expression continuation at a newline. -/
private def privateFieldEnd : List Token → Option (List Token)
  | [] => some []
  | .punctuation ";" :: rest => some rest
  | .lineBreak :: rest =>
    match skipLines rest with
    | .punctuation "-" :: _ | .punctuation "(" :: _ | .punctuation "[" :: _
    | .punctuation "." :: _ | .punctuation "?." :: _ => none
    | _ => some rest
  | _ => none

private def privateFieldDeclaration (fuel : Nat) : Parser PrivateField := fun tokens => do
  match skipLines tokens with
  | .privateName name :: rest =>
    if name = "constructor" then none else do
    let (optional, rest) := match rest with
      | .punctuation "?" :: rest => (true, rest)
      | _ => (false, rest)
    let (annotation, rest) ← match rest with
      | .punctuation ":" :: rest => do
        let (annotation, rest) ← typeSyntax fuel rest
        pure (some annotation, rest)
      | _ => pure (none, rest)
    let (initializer, rest) ← match skipLines rest with
      | .punctuation "=" :: rest => do
        let (value, rest) ← expression fuel (skipLines rest)
        pure (some value, rest)
      | _ => pure (none, rest)
    return (⟨name, optional, annotation, initializer⟩, ← privateFieldEnd rest)
  | _ => none

private def privateFieldDeclarations : Nat → Parser (List PrivateField)
  | 0, _ => none
  | fuel + 1, tokens => do
    if (skipLines tokens).isEmpty then pure ([], []) else do
    let (head, rest) ← privateFieldDeclaration fuel tokens
    let (tail, rest) ← privateFieldDeclarations fuel rest
    pure (head :: tail, rest)

/-- Direct lexical writes are outside the frozen class-capture interpretation.
Heap effects of supported expressions still follow the existing evaluator.
General mutable helper closures, this/super and method installation are not
established by this syntax admission. -/
private def initializerNoLexicalWrite : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, value =>
    match value with
    | .this | .preIncrement _ | .privateProperty _ _ => false
    | .variable _ | .string _ | .number _ | .null | .boolean _ => true
    | .index a b | .optionalIndex a b | .strictEqual a b | .compare _ a b | .subtract a b
    | .logicalAnd a b | .logicalOr a b | .nullish a b =>
      initializerNoLexicalWrite fuel a && initializerNoLexicalWrite fuel b
    | .property a _ | .logicalNot a | .typeAssertion a _ => initializerNoLexicalWrite fuel a
    | .call receiver _ arguments | .invoke receiver arguments | .construct receiver _ arguments =>
      initializerNoLexicalWrite fuel receiver && arguments.all (initializerNoLexicalWrite fuel)
    | .conditional condition yes no => initializerNoLexicalWrite fuel condition &&
      initializerNoLexicalWrite fuel yes && initializerNoLexicalWrite fuel no
    | .arrayLiteral elements => elements.all (fun element => initializerNoLexicalWrite fuel element.2)
    | .objectLiteral fields => fields.all (fun field =>
      initializerNoLexicalWrite fuel field.1 && initializerNoLexicalWrite fuel field.2)

/-- Generic supported private DATA-field list, not a class or Node recognizer.
All names are declared lexically before any initializer runs; runtime addition
is separately ordered. Methods/accessors, public/static fields, decorators,
this/super and direct mutable lexical writes are conservatively rejected. -/
def parsePrivateFields (text : String) (allowedBindings : List String) : Option (List PrivateField) := do
  let tokens ← lex (text.toList.length + 1) text.toList
  let (fields, rest) ← privateFieldDeclarations (syntaxFuel tokens) tokens
  let names := fields.map PrivateField.name
  if rest.isEmpty && allowedBindings.all bindingIdentifier && decide names.Nodup &&
      fields.all (fun field => match field.initializer with
        | none => true
        | some value => validExpr (syntaxFuel tokens) allowedBindings value &&
          privateExpressionAllowed (syntaxFuel tokens) names value && initializerNoLexicalWrite (syntaxFuel tokens) value) then
    some fields else none

/-- Narrow extension interface for outer method/signature parsing. These
forwarders reuse the same fail-closed lexer and grammar; they do not broaden
the older expression/block entry points. -/
def tokenizeFragment (text : String) : Option (List Token) :=
  lex (text.toList.length + 1) text.toList

def skipTokenLines (tokens : List Token) : List Token := skipLines tokens

def bindingNameAllowed (name : String) : Bool := bindingIdentifier name

def parseTypeTokens (tokens : List Token) : Option (TypeSyntax × List Token) :=
  typeSyntax (syntaxFuel tokens) tokens

def parseRawExpressionTokens (tokens : List Token) : Option (Expr × List Token) :=
  expression (syntaxFuel tokens) (skipLines tokens)

/-- Raw single-statement syntax for explicit outer control extensions. This
does not bypass admission or broaden parseBlock. -/
def parseRawStatementTokens (tokens : List Token) : Option (Stmt × List Token) :=
  statement (syntaxFuel tokens) (skipLines tokens)

def expressionAdmitted (value : Expr) (allowedBindings allowedPrivateNames : List String) (allowThis : Bool := false) : Bool :=
  validExprCore allowThis 65536 allowedBindings value && privateExpressionAllowed 65536 allowedPrivateNames value

/-- Reuse ordinary statement binding/private-scope checks at an explicit
extension boundary. Its caller must still restrict the statement forms and
lexical effects appropriate to that extension. -/
def statementAdmitted (value : Stmt) (allowedBindings allowedPrivateNames : List String)
    (allowThis : Bool := false) : Bool :=
  validStatementsCore allowThis 65536 true allowedBindings [value] &&
    privateStatementsAllowed 65536 allowedPrivateNames [value]

def parseBodyTokens (tokens : List Token) (allowedBindings allowedPrivateNames : List String) (allowThis : Bool := false) :
    Option (List Stmt × List Token) := do
  let (body, rest) ← statements (syntaxFuel tokens) tokens
  if validStatementsCore allowThis (syntaxFuel tokens) true allowedBindings body &&
      privateStatementsAllowed (syntaxFuel tokens) allowedPrivateNames body then
    some (body, rest) else none

end HonoLean.Upstream.SourceSubset
