import HonoLean.Upstream.SourceSubset.ArrayBindingRules
import HonoLean.Upstream.ECMA2025.LabelRegExpSyntax

set_option autoImplicit false
namespace HonoLean.Upstream.SourceSubset
open ECMA2025

/-- Original regexp literal units and flags, not a precomputed capturing result. -/
structure LabelRegExpLiteral where
  source : JSString
  flags : JSString := []
  deriving Repr, DecidableEq
structure LabelMatchDecl where
  name : String
  receiver : Expr
  method : String
  argument : LabelRegExpLiteral
  deriving Repr

private def labelSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
private def labelStart (c : Char) : Bool := c == '_' || c == '$' || c.isAlpha
private def labelPart (c : Char) : Bool := labelStart c || c.isDigit
private def labelToken (token : String) (input : List Char) : Option (List Char) :=
  let input := input.dropWhile labelSpace
  if token.toList.isPrefixOf input then some (input.drop token.toList.length) else none
private def labelName (input : List Char) : Option (String × List Char) := do
  let input := input.dropWhile labelSpace
  match input with
  | [] => none
  | head :: _ =>
    if !labelStart head then none else
    let name := input.takeWhile labelPart
    some (String.ofList name, input.drop name.length)

private def labelLiteralBody : Nat → List Char → Option (JSString × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, '/' :: rest => some ([], rest)
  | fuel + 1, '\\' :: escaped :: rest => do
    if escaped == '\n' || escaped == '\r' || escaped.toNat > 127 then none else
    let (body, rest) ← labelLiteralBody fuel rest
    some (92 :: UInt16.ofNat escaped.toNat :: body, rest)
  | fuel + 1, head :: rest => do
    if head == '\n' || head == '\r' || head.toNat > 127 then none else
    let (body, rest) ← labelLiteralBody fuel rest
    some (UInt16.ofNat head.toNat :: body, rest)

/-- This closed call entry executes the VM at index0. Admit only an explicit
leading start assertion; general RegExpBuiltinExec search remains open. -/
def labelStartAnchored : LabelRegExp.Syntax → Bool
  | .start | .sequence (.start :: _) => true
  | _ => false

/-- Narrow original literal-call declaration parser. It preserves regexp source,
flags, member name and operand order; unsupported receivers/callbacks fail closed.
The literal is not affected by a lexical binding called RegExp. -/
def parseLabelMatch (text : String) (bindings : List String) : Option LabelMatchDecl := do
  let rest ← labelToken "const" text.toList
  if !(rest.head?.map labelSpace |>.getD false) then none else
  let (name, rest) ← labelName rest
  if !bindingNameAllowed name then none else
  let rest ← labelToken "=" rest
  let (receiver, rest) ← labelName rest
  if !bindings.contains receiver || name == receiver then none else
  let rest ← labelToken "." rest
  let (method, rest) ← labelName rest
  let rest ← labelToken "(" rest
  let rest ← labelToken "/" rest
  let (source, rest) ← labelLiteralBody (rest.length + 1) rest
  let flags := rest.takeWhile Char.isAlpha
  let rest := rest.drop flags.length
  if !flags.isEmpty then none else
  let ast ← LabelRegExp.parseLiteral (47 :: source ++ [47])
  if !labelStartAnchored ast then none else
  let rest ← labelToken ")" rest
  let rest := rest.dropWhile labelSpace
  let rest := match rest with | ';' :: rest => rest.dropWhile labelSpace | _ => rest
  if !rest.isEmpty then none else
  some ⟨name, .variable receiver, method, ⟨source, flags.map (fun c => UInt16.ofNat c.toNat)⟩⟩

inductive LabelFlag where
  | hasIndices | global | ignoreCase | multiline | dotAll | unicode | unicodeSets | sticky
  deriving Repr, DecidableEq, BEq

def labelFlags : List LabelFlag := [.hasIndices, .global, .ignoreCase, .multiline, .dotAll, .unicode, .unicodeSets, .sticky]
def labelFlagKey : LabelFlag → JSString
  | .hasIndices => [104,97,115,73,110,100,105,99,101,115]
  | .global => [103,108,111,98,97,108]
  | .ignoreCase => [105,103,110,111,114,101,67,97,115,101]
  | .multiline => [109,117,108,116,105,108,105,110,101]
  | .dotAll => [100,111,116,65,108,108]
  | .unicode => [117,110,105,99,111,100,101]
  | .unicodeSets => [117,110,105,99,111,100,101,83,101,116,115]
  | .sticky => [115,116,105,99,107,121]
def labelFlagUnit : LabelFlag → UInt16
  | .hasIndices => 100 | .global => 103 | .ignoreCase => 105 | .multiline => 109
  | .dotAll => 115 | .unicode => 117 | .unicodeSets => 118 | .sticky => 121

def labelMatchKey : JSString := [109,97,116,99,104]
def labelExecKey : JSString := [101,120,101,99]
def labelFlagsKey : JSString := [102,108,97,103,115]

inductive LabelBuiltin where
  | stringMatch | regexpMatch | flagsGetter | flagGetter (flag : LabelFlag)
  deriving Repr, DecidableEq
structure LabelBuiltinTable where
  base : Nat
  entries : List LabelBuiltin
  deriving Repr, DecidableEq
structure LabelMatchContext where
  iterators : ArrayIteratorContext
  builtins : LabelBuiltinTable
  stringPrototype : Nat
  regexpPrototype : Nat
  deriving Repr
inductive LabelSymbol where
  | match
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq
inductive LabelPropertyKey where
  | string (key : JSString) | symbol (key : LabelSymbol)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq
structure LabelAccessorSlot where
  holder : Nat
  key : LabelPropertyKey
  callee : Value
  deriving Repr, DecidableEq

end HonoLean.Upstream.SourceSubset
