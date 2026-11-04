import HonoLean.Upstream.SourceSubset.SplitPath

namespace HonoLean.Upstream.SourceSubset

set_option maxRecDepth 32768

example : run splitPathProgram [] = .ok [] := by cbv
example : run splitPathProgram [47] = .ok [.string []] := by cbv
example : run splitPathProgram [47, 47, 97] = .ok [.string [], .string [97]] := by cbv
example : run splitPathProgram [47, 97, 47] = .ok [.string [97], .string []] := by cbv
example : run splitPathProgram [55296, 47, 56320, 55348, 56606] =
    .ok [.string [55296], .string [56320, 55348, 56606]] := by cbv

/-- Truncation happens before the possible shift; limit zero sees undefined. -/
example : run splitPathProgram [47, 97, 47, 98] 0 = .ok [] := by cbv
example : run splitPathProgram [47, 97, 47, 98] 1 = .ok [] := by cbv
example : run splitPathProgram [47, 97, 47, 98] 2 = .ok [.string [97]] := by cbv

def aliasSource : String := "export const aliases = (path: string): string[] => {\n  const paths = path.split('/')\n  const alias = paths\n  alias.shift()\n  return paths\n}"

/-- The alias and original variable designate the same mutable array reference. -/
example : (parse aliasSource).map (fun program => run program [97, 47, 98]) =
    some (.ok [.string [98]]) := by cbv

def rejectedSources : List String := [
  "export const f = (path: string): string[] => { return\npath }",
  "export const f = (path: string): string[] => { const paths = path.split('/') paths.shift(); return paths }",
  "export const f = (path: string): string[] => { const path = path.split('/'); return path }",
  "export const f = (path: string): string[] => { const paths = path.split('/'); const paths = path; return paths }",
  "export const f = (path: string): string[] => { if (path === '') { const local = path; } return path }",
  "export const f = (eval: string): string[] => { return eval }",
  "export const class = (path: string): string[] => { return path }",
  "export const f = (path: string): string[] => { return path[9007199254740992] }",
  "export const f = (path: string): string[] => { return path[00] }",
  "export const f = (path: string): string[] => { return path === '' === path }",
  "export const f = (path: string): string[] => { const paths = path.split('\\/'); return paths }",
  "export const f = (path: string): string[] => { /* comment */ return path }",
  "export const f = (path: string): string[] => { return path } evil()"]

example : rejectedSources.all (fun source => (parse source).isNone) = true := by cbv

def noShiftSource : String := "export const splitPath = (path: string): string[] => {\n  const paths = path.split('/')\n  if (paths[0] === '') {\n  }\n  return paths\n}"

def wrongIndexSource : String := "export const splitPath = (path: string): string[] => {\n  const paths = path.split('/')\n  if (paths[1] === '') {\n    paths.shift()\n  }\n  return paths\n}"

def wrongDelimiterSource : String := "export const splitPath = (path: string): string[] => {\n  const paths = path.split('-')\n  if (paths[0] === '') {\n    paths.shift()\n  }\n  return paths\n}"

/-- These altered source bodies are accepted by the generic parser and really
execute to outputs violating the pinned source's independent contract. -/
example : ([noShiftSource, wrongIndexSource, wrongDelimiterSource].map
    (fun source => (parse source).map (fun program => run program [47, 97]))) =
      [some (.ok [.string [], .string [97]]),
       some (.ok [.string [], .string [97]]),
       some (.ok [.string [47, 97]])] := by cbv

example : ¬ SplitPathContract defaultSplitLimit [47, 97] [[], [97]] := by
  rw [contract_iff]
  decide +kernel

example : ¬ SplitPathContract defaultSplitLimit [47, 97] [[47, 97]] := by
  rw [contract_iff]
  decide +kernel

def SourceHasContract (source : String) : Prop :=
  ∀ input output,
    (parse source).map (fun program => run program input defaultSplitLimit) =
      some (.ok (output.map Value.string)) ↔ SplitPathContract defaultSplitLimit input output

/-- Kernel-checked counterexamples to the universal property for real source
body mutations; they do not merely fail a file-hash or AST-equality check. -/
example : ¬ SourceHasContract noShiftSource := by
  intro claimed
  have actual : (parse noShiftSource).map (fun program => run program [47, 97]) =
      some (.ok ([[], [97]].map Value.string)) := by cbv
  have invalid : ¬ SplitPathContract defaultSplitLimit [47, 97] [[], [97]] := by
    rw [contract_iff]; decide +kernel
  exact invalid ((claimed _ _).mp actual)

example : ¬ SourceHasContract wrongIndexSource := by
  intro claimed
  have actual : (parse wrongIndexSource).map (fun program => run program [47, 97]) =
      some (.ok ([[], [97]].map Value.string)) := by cbv
  have invalid : ¬ SplitPathContract defaultSplitLimit [47, 97] [[], [97]] := by
    rw [contract_iff]; decide +kernel
  exact invalid ((claimed _ _).mp actual)

example : ¬ SourceHasContract wrongDelimiterSource := by
  intro claimed
  have actual : (parse wrongDelimiterSource).map (fun program => run program [47, 97]) =
      some (.ok ([[47, 97]].map Value.string)) := by cbv
  have invalid : ¬ SplitPathContract defaultSplitLimit [47, 97] [[47, 97]] := by
    rw [contract_iff]; decide +kernel
  exact invalid ((claimed _ _).mp actual)

end HonoLean.Upstream.SourceSubset
