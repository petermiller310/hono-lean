import HonoLean.Upstream.NodeInitialization.Preamble

namespace HonoLean.Upstream.NodeInitialization

open SourceSubset

def stringType : TypeSyntax := .named "string"
def genericNodeType : TypeSyntax := .application (.named "Node") [.named "T"]
def genericHandlerType : TypeSyntax := .application (.named "HandlerSet") [.named "T"]
def mapType (value : TypeSyntax) : TypeSyntax := .application (.named "Record") [stringType, value]

/-- Exact five selected private DATA declarations. The optional marker and type
metadata are retained; no type establishes a runtime shape or suppresses the
undefined field installation for the omitted initializer. -/
def fieldsProgram : List PrivateField :=
  [⟨"methods", false, some (.array (mapType genericHandlerType)), some (.arrayLiteral [])⟩,
   ⟨"children", false, some (mapType genericNodeType), some (.invoke (.variable "createNullObject") [])⟩,
   ⟨"patterns", false, some (.array genericNodeType), some (.arrayLiteral [])⟩,
   ⟨"pattern", true, some (.union (.named "Pattern") stringType), none⟩,
   ⟨"params", false, some (mapType stringType), some (.variable "emptyParams")⟩]

def dataNames : List String := ["methods", "children", "patterns", "pattern", "params"]

theorem field_names : fieldsProgram.map PrivateField.name = dataNames := rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem parses_fields : parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"] = some fieldsProgram := by cbv

end HonoLean.Upstream.NodeInitialization
