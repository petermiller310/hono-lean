import HonoLean.Upstream.SourceSubset.Parser
import HonoLean.Upstream.SourceSubset.MethodSyntax

namespace HonoLean.Upstream.SourceSubset

private def captureReadOnlyExpression : Nat → List String → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, captures, value =>
    match value with
    | .preIncrement name => !captures.contains name
    | .variable _ | .this | .string _ | .number _ | .null | .boolean _ => true
    | .property receiver _ | .privateProperty receiver _ | .logicalNot receiver
    | .typeAssertion receiver _ => captureReadOnlyExpression fuel captures receiver
    | .index left right | .optionalIndex left right | .strictEqual left right | .subtract left right
    | .compare _ left right | .logicalAnd left right | .nullish left right | .logicalOr left right =>
      captureReadOnlyExpression fuel captures left && captureReadOnlyExpression fuel captures right
    | .conditional test yes no => captureReadOnlyExpression fuel captures test &&
      captureReadOnlyExpression fuel captures yes && captureReadOnlyExpression fuel captures no
    | .call receiver _ arguments | .invoke receiver arguments | .construct receiver _ arguments =>
      captureReadOnlyExpression fuel captures receiver && arguments.all (captureReadOnlyExpression fuel captures)
    | .arrayLiteral elements => elements.all (fun entry => captureReadOnlyExpression fuel captures entry.2)
    | .objectLiteral fields => fields.all (fun field =>
      captureReadOnlyExpression fuel captures field.1 && captureReadOnlyExpression fuel captures field.2)

/-- The frozen value-capture specialization cannot interpret direct writes to
captured lexical cells. Formal parameters shadow captures; conservatively even
same-spelling nested loop/local shadows of other captures reject. Ordinary local
counters remain supported. Callback effects and later external cell changes
still need separate live-cell/closure interpretation. -/
private def capturesReadOnlyBody : Nat → List String → List Stmt → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, captures, head :: tail =>
    let permitted := match head with
      | .declare _ value | .typedDeclare _ _ value | .mutableDeclare _ _ value
      | .evaluate value | .ret value => captureReadOnlyExpression fuel captures value
      | .assign assignment => captureReadOnlyExpression fuel captures assignment.target &&
          captureReadOnlyExpression fuel captures assignment.value
      | .branch condition body => captureReadOnlyExpression fuel captures condition &&
          capturesReadOnlyBody fuel captures body
      | .countedFor initializers condition incrementName body =>
          !captures.contains incrementName &&
          initializers.all (fun initializer => captureReadOnlyExpression fuel captures initializer.2) &&
          captureReadOnlyExpression fuel captures condition && capturesReadOnlyBody fuel captures body
    permitted && capturesReadOnlyBody fuel captures tail

private def methodParameters : Nat → List Token → Option (List MethodParameter × List Token)
  | 0, _ => none
  | fuel + 1, tokens => do
    match skipTokenLines tokens with
    | .punctuation ")" :: rest => some ([], rest)
    | .name name :: rest =>
      if !bindingNameAllowed name then none else do
      let (optional, rest) := match rest with
        | .punctuation "?" :: rest => (true, rest)
        | _ => (false, rest)
      let rest ← match skipTokenLines rest with
        | .punctuation ":" :: rest => some rest
        | _ => none
      let (annotation, rest) ← parseTypeTokens rest
      let parameter : MethodParameter := ⟨name, optional, annotation⟩
      match skipTokenLines rest with
      | .punctuation ")" :: rest => some ([parameter], rest)
      | .punctuation "," :: rest => do
        let (tail, rest) ← methodParameters fuel rest
        if optional && tail.any (fun parameter => !parameter.optional) then none
        else some (parameter :: tail, rest)
      | _ => none
    | _ => none

/-- Parse a complete selected private-method declaration through the existing
body grammar. Types/optional markers are retained, not runtime checks. Only
the body subset already admitted by parseBlock is accepted, with an explicit dynamic this binding. Super, arguments and unsupported syntax reject. Nested block-method dispatch
remains unsupported; legacy zero-argument invokes keep their older meaning. -/
def parsePrivateMethod (text : String) (allowedBindings allowedPrivateNames : List String) :
    Option PrivateMethod := do
  let tokens ← tokenizeFragment text
  match skipTokenLines tokens with
  | .privateName name :: rest =>
    if name = "constructor" || !allowedBindings.all bindingNameAllowed then none else do
    let rest ← match skipTokenLines rest with
      | .punctuation "(" :: rest => some rest
      | _ => none
    let (parameters, rest) ← methodParameters (tokens.length + 1) rest
    let names := parameters.map MethodParameter.name
    if !decide names.Nodup then none else do
    let rest ← match skipTokenLines rest with
      | .punctuation ":" :: rest => some rest
      | _ => none
    let (result, rest) ← parseTypeTokens rest
    let rest ← match skipTokenLines rest with
      | .punctuation "{" :: rest => some rest
      | _ => none
    let captures := allowedBindings.filter (fun binding => !names.contains binding)
    let (body, rest) ← parseBodyTokens rest (names ++ captures) allowedPrivateNames true
    if (skipTokenLines rest).isEmpty && capturesReadOnlyBody 65536 captures body then
      some ⟨name, parameters, result, body⟩ else none
  | _ => none

/-- Admission shared by the standalone call parser and explicit control
extensions. Arguments retain the old expression/private-scope checks. -/
def privateMethodCallAdmitted (value : Expr) (allowedBindings allowedPrivateNames : List String) :
    Option PrivateMethodCall := do
  if !allowedBindings.all bindingNameAllowed then none else do
  match value with
  | .invoke (.privateProperty receiver spelling) arguments =>
    let receiver ← match receiver with
      | .this => some MethodReceiver.this
      | other => if expressionAdmitted other allowedBindings allowedPrivateNames then
          some (.expression other) else none
    if allowedPrivateNames.contains spelling &&
        arguments.all (fun argument => expressionAdmitted argument allowedBindings allowedPrivateNames) then
      some ⟨receiver, spelling, arguments⟩ else none
  | _ => none

/-- The added call entry accepts exactly a private-member invoke. It admits
this only in the receiver position, separately from lexical bindings. Each
other operand retains the existing expression/private-scope checks. -/
def parsePrivateMethodCall (text : String) (allowedBindings allowedPrivateNames : List String) :
    Option PrivateMethodCall := do
  let tokens ← tokenizeFragment text
  let (value, rest) ← parseRawExpressionTokens tokens
  let rest := match skipTokenLines rest with
    | .punctuation ";" :: rest => skipTokenLines rest
    | rest => rest
  if !rest.isEmpty then none else
    privateMethodCallAdmitted value allowedBindings allowedPrivateNames

end HonoLean.Upstream.SourceSubset
