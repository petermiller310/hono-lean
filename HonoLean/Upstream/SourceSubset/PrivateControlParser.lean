import HonoLean.Upstream.SourceSubset.PrivateControlSyntax
import HonoLean.Upstream.SourceSubset.MethodParser

namespace HonoLean.Upstream.SourceSubset

/-- A separate line-comment pass for this extension. Quoted slashes survive;
escaped characters are copied together so an escaped quote cannot terminate a
string during preprocessing (the existing lexer subsequently rejects escapes).
CR and LF are retained for the existing statement/ASI checks. Block comments,
slash operators, templates and unsupported Unicode line separators reject. -/
private def controlCommentText : Nat → Option Char → List Char → Option (List Char)
  | 0, _, _ => none
  | _ + 1, none, [] => some []
  | _ + 1, some _, [] => none
  | fuel + 1, quote, c :: rest => do
    if c.val = 0x2028 || c.val = 0x2029 then none else
    match quote with
    | some delimiter =>
      if c == '\n' || c == '\r' then none
      else if c == '\\' then
        match rest with
        | escaped :: tail =>
          if escaped == '\n' || escaped == '\r' || escaped.val = 0x2028 || escaped.val = 0x2029 then none
          else return c :: escaped :: (← controlCommentText fuel quote tail)
        | [] => none
      else return c :: (← controlCommentText fuel (if c == delimiter then none else quote) rest)
    | none =>
      if c == '\'' || c == '"' then return c :: (← controlCommentText fuel (some c) rest)
      else if c == '`' then none
      else if c == '/' then
        match rest with
        | '/' :: tail =>
          let comment := tail.takeWhile (fun c => c != '\n' && c != '\r')
          if comment.any (fun c => c.val = 0x2028 || c.val = 0x2029) then none
          else controlCommentText fuel none (tail.drop comment.length)
        | _ => none
      else return c :: (← controlCommentText fuel none rest)

/-- Existing lexer after explicit line-comment handling; no behavior of the
older lexer or expression/block entry points changes. -/
def tokenizePrivateControl (text : String) : Option (List Token) := do
  let characters ← controlCommentText (text.toList.length + 1) none text.toList
  tokenizeFragment (String.ofList characters)

/-- No direct lexical writes are admitted anywhere in this entry. Private
method invocation is accepted only as its own control leaf, never nested in an
ordinary expression whose old evaluator cannot dispatch block methods. Heap
effects of the existing admitted builtins remain ordinary expression effects. -/
private def controlExpressionAllowedCore (allowPrivate : Bool) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, value =>
    match value with
    | .preIncrement _ => false
    | .variable _ | .this | .string _ | .number _ | .null | .boolean _ => true
    | .privateProperty receiver _ => allowPrivate && controlExpressionAllowedCore allowPrivate fuel receiver
    | .property receiver _ | .logicalNot receiver | .typeAssertion receiver _ =>
      controlExpressionAllowedCore allowPrivate fuel receiver
    | .index left right | .optionalIndex left right | .strictEqual left right | .subtract left right
    | .compare _ left right | .logicalAnd left right | .nullish left right | .logicalOr left right =>
      controlExpressionAllowedCore allowPrivate fuel left && controlExpressionAllowedCore allowPrivate fuel right
    | .conditional test yes no => controlExpressionAllowedCore allowPrivate fuel test &&
      controlExpressionAllowedCore allowPrivate fuel yes && controlExpressionAllowedCore allowPrivate fuel no
    | .invoke receiver arguments =>
      controlExpressionAllowedCore false fuel receiver &&
        arguments.all (controlExpressionAllowedCore allowPrivate fuel)
    | .call receiver _ arguments | .construct receiver _ arguments =>
      controlExpressionAllowedCore allowPrivate fuel receiver &&
        arguments.all (controlExpressionAllowedCore allowPrivate fuel)
    | .arrayLiteral elements => elements.all (fun entry => controlExpressionAllowedCore allowPrivate fuel entry.2)
    | .objectLiteral fields => fields.all (fun field =>
      controlExpressionAllowedCore allowPrivate fuel field.1 && controlExpressionAllowedCore allowPrivate fuel field.2)

/-- Ordinary invoke callees may not contain a private read anywhere, including
under type assertions or conditional expressions. Dedicated private-call leaves
are admitted separately; ordinary private data reads and builtin calls remain
available in other expression positions. -/
def privateControlExpressionAllowed (fuel : Nat) (value : Expr) : Bool :=
  controlExpressionAllowedCore true fuel value

private def controlOrdinaryAllowed (statement : Stmt) : Bool :=
  match statement with
  | .declare _ value | .typedDeclare _ _ value | .mutableDeclare _ _ value
  | .evaluate value | .ret value => privateControlExpressionAllowed 65536 value
  | .assign assignment => privateControlExpressionAllowed 65536 assignment.target &&
      privateControlExpressionAllowed 65536 assignment.value
  | .branch _ _ | .countedFor _ _ _ _ => false

private def controlLeaf (statement : Stmt) (bindings privateNames : List String)
    (allowDeclarations : Bool) : Option PrivateControlStmt := do
  match statement with
  | .evaluate value =>
    match privateMethodCallAdmitted value bindings privateNames with
    | some call =>
      let receiverAllowed := match call.receiver with
        | .this => true
        | .expression value => privateControlExpressionAllowed 65536 value
      if receiverAllowed && call.arguments.all (privateControlExpressionAllowed 65536) then
        some (.privateCall call) else none
    | none =>
      if controlOrdinaryAllowed statement && statementAdmitted statement bindings privateNames true then
        some (.ordinary statement) else none
  | .declare _ _ | .typedDeclare _ _ _ | .mutableDeclare _ _ _ =>
    if allowDeclarations && controlOrdinaryAllowed statement &&
        statementAdmitted statement bindings privateNames true then some (.ordinary statement) else none
  | _ =>
    if controlOrdinaryAllowed statement && statementAdmitted statement bindings privateNames true then
      some (.ordinary statement) else none

private def controlLeafBindings (statement : PrivateControlStmt) (bindings : List String) : List String :=
  match statement with
  | .ordinary (.declare name _) | .ordinary (.typedDeclare name _ _)
  | .ordinary (.mutableDeclare name _ _) => name :: bindings
  | _ => bindings

mutual
  private def controlStatements : Nat → Bool → List String → List String → List Token →
      Option (List PrivateControlStmt × List Token)
    | 0, _, _, _, _ => none
    | fuel + 1, allowDeclarations, bindings, privateNames, tokens => do
      match skipTokenLines tokens with
      | .punctuation "}" :: rest => some ([], rest)
      | tokens =>
        let (head, rest) ← controlStatement fuel allowDeclarations bindings privateNames tokens
        let (tail, rest) ← controlStatements fuel allowDeclarations (controlLeafBindings head bindings) privateNames rest
        some (head :: tail, rest)

  private def controlStatement : Nat → Bool → List String → List String → List Token →
      Option (PrivateControlStmt × List Token)
    | 0, _, _, _, _ => none
    | fuel + 1, allowDeclarations, bindings, privateNames, tokens => do
      match skipTokenLines tokens with
      | .name "if" :: rest =>
        let rest ← match skipTokenLines rest with
          | .punctuation "(" :: rest => some rest
          | _ => none
        let (condition, rest) ← parseRawExpressionTokens rest
        if !expressionAdmitted condition bindings privateNames true ||
            !privateControlExpressionAllowed 65536 condition then none else do
        let rest ← match skipTokenLines rest with
          | .punctuation ")" :: rest => some rest
          | _ => none
        let rest ← match skipTokenLines rest with
          | .punctuation "{" :: rest => some rest
          | _ => none
        let (yes, rest) ← controlStatements fuel false bindings privateNames rest
        match skipTokenLines rest with
        | .name "else" :: rest =>
          let rest ← match skipTokenLines rest with
            | .punctuation "{" :: rest => some rest
            | _ => none
          let (no, rest) ← controlStatements fuel false bindings privateNames rest
          some (.branch condition yes no, rest)
        | _ => some (.branch condition yes [], rest)
      | tokens =>
        let (statement, rest) ← parseRawStatementTokens tokens
        let statement ← controlLeaf statement bindings privateNames allowDeclarations
        some (statement, rest)
end

/-- Structural generic parsing of a selected control fragment, with root-only
fresh declarations. It does not recognize Node-specific text or output. This
is a specialized lexical admission rule, not full block/TDZ/type semantics. -/
def parsePrivateControl (text : String) (allowedBindings allowedPrivateNames : List String) :
    Option (List PrivateControlStmt) := do
  if !allowedBindings.all bindingNameAllowed then none else do
  let tokens ← tokenizePrivateControl text
  let (program, rest) ← controlStatements (tokens.length + 1) true allowedBindings allowedPrivateNames
    (tokens ++ [.punctuation "}"])
  if rest.isEmpty then some program else none

end HonoLean.Upstream.SourceSubset
