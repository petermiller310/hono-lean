import HonoLean.Upstream.SourceSubset.PrivateControlParser

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset

inductive ArrayBindingElement where
  | elision
  | binding (name : String)
  deriving Repr, DecidableEq
structure ArrayBindingDecl where
  elements : List ArrayBindingElement
  initializer : Expr
  deriving Repr

def arrayBindingNames (elements : List ArrayBindingElement) : List String :=
  elements.filterMap (fun element => match element with | .elision => none | .binding name => some name)

private def bindingElements : Nat → List Token → Option (List ArrayBindingElement × List Token)
  | 0, _ => none
  | fuel + 1, tokens => do
    match skipTokenLines tokens with
    | .punctuation "]" :: rest => some ([], rest)
    | .punctuation "," :: rest =>
      let (tail, rest) ← bindingElements fuel rest
      some (.elision :: tail, rest)
    | .name name :: rest =>
      if !bindingNameAllowed name then none else
      match skipTokenLines rest with
      | .punctuation "]" :: rest => some ([.binding name], rest)
      | .punctuation "," :: rest =>
        let (tail, rest) ← bindingElements fuel rest
        some (.binding name :: tail, rest)
      | _ => none
    | _ => none

/-- No callback/visible lexical write can indirectly observe a not-yet-created
selected binding. This is a fresh selected activation specialization, not a
model of mutable lexical cells, defaults, rest, nested patterns or TDZ throws. -/
private def bindingRhsClosed : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
    match expression with
    | .invoke _ _ | .construct _ _ _ | .preIncrement _ | .call _ _ _ => false
    | .variable _ | .this | .number _ | .string _ | .boolean _ | .null => true
    | .index left right | .optionalIndex left right | .strictEqual left right | .subtract left right
    | .compare _ left right | .logicalAnd left right | .logicalOr left right | .nullish left right =>
      bindingRhsClosed fuel left && bindingRhsClosed fuel right
    | .property receiver _ | .privateProperty receiver _ | .logicalNot receiver | .typeAssertion receiver _ =>
      bindingRhsClosed fuel receiver
    | .conditional test yes no => bindingRhsClosed fuel test && bindingRhsClosed fuel yes && bindingRhsClosed fuel no
    | .arrayLiteral elements => elements.all (fun element => bindingRhsClosed fuel element.2)
    | .objectLiteral fields => fields.all (fun field => bindingRhsClosed fuel field.1 && bindingRhsClosed fuel field.2)

/-- Exact full declaration entry, preserving elisions as IteratorStep rather
than translating them to numeric array reads. Outer shadow bindings remain in
the modeled environment tail; RHS references to a new binder fail admission. -/
def parseArrayBinding (text : String) (allowedBindings : List String) (allowedPrivateNames : List String := []) : Option ArrayBindingDecl := do
  if !allowedBindings.all bindingNameAllowed then none else
  let tokens ← tokenizeFragment text
  let rest ← match skipTokenLines tokens with
    | .name "const" :: .punctuation "[" :: rest => some rest
    | _ => none
  let (elements, rest) ← bindingElements (tokens.length + 1) rest
  let names := arrayBindingNames elements
  if !names.Nodup || names.any (fun name => name == "Object" || name == "Set") then none else
  let rest ← match skipTokenLines rest with | .punctuation "=" :: rest => some rest | _ => none
  let (initializer, rest) ← parseRawExpressionTokens rest
  let rest := skipTokenLines rest
  let rest := match rest with | .punctuation ";" :: rest => skipTokenLines rest | _ => rest
  let available := allowedBindings.filter (fun name => !names.contains name)
  if !rest.isEmpty || !expressionAdmitted initializer available allowedPrivateNames true || !bindingRhsClosed 65536 initializer then none else
  some ⟨elements, initializer⟩

end HonoLean.Upstream.SourceSubset
