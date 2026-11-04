import HonoLean.Upstream.NodeClass.Generated
import HonoLean.Upstream.NodeInitialization.Program
import HonoLean.Upstream.NodePrivateCall.Program

namespace HonoLean.Upstream.NodeClass

open SourceSubset ECMA2025

def fieldsProgram : List PrivateField := NodeInitialization.fieldsProgram
def methodsProgram : List PrivateMethod := [NodePrivateCall.methodProgram]

theorem parses_preamble : parseBlock pinnedPreambleSource ["createNullObject"] =
    some NodeInitialization.preambleProgram := NodeInitialization.parses_preamble

theorem parses_fields : parsePrivateFields pinnedFieldsSource ["createNullObject", "emptyParams"] =
    some fieldsProgram := NodeInitialization.parses_fields

theorem parses_method : parsePrivateMethod pinnedMethodSource NodePrivateCall.lexicalBindings
    NodePrivateCall.classPrivateNames = some NodePrivateCall.methodProgram := NodePrivateCall.parses_method

end HonoLean.Upstream.NodeClass
