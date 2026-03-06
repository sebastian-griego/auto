import Lean
import AutoformalizationEval.Tools.Common

open Lean Meta Elab Command

namespace AutoformalizationEval.Tools

private structure TheoremMeta where
  name : String
  type : String
  is_sorry : Bool
  local_type_dependencies : Array String
  local_value_dependencies : Array String
  external_type_dependencies : Array String
  external_value_dependencies : Array String
deriving ToJson

private def extractRoot : Name := parseDottedName "ExtractTmp"

private def splitDependencies (root : Name) (deps : Array Name) : Array String × Array String := Id.run do
  let mut localDeps : Array String := #[]
  let mut externalDeps : Array String := #[]
  for dep in deps do
    if isInternalOrAuxName dep then
      pure ()
    else if nameHasRootPrefix dep root then
      let localName := relativeToRootString dep root
      if !localName.isEmpty then
        localDeps := localDeps.push localName
    else
      externalDeps := externalDeps.push (toString dep)
  return (sortUniqueStrings localDeps, sortUniqueStrings externalDeps)

private def theoremPayload : MetaM Json := do
  let env ← getEnv
  let mut theorems : Array TheoremMeta := #[]
  for (name, info) in env.constants.toList do
    if nameHasRootPrefix name extractRoot && !isInternalOrAuxName name then
      let suffix := relativeToRootString name extractRoot
      if !suffix.isEmpty then
        match info with
        | .thmInfo thm =>
            let typeFmt ← ppExpr thm.type
            let typeDeps := collectConstNames thm.type
            let valueDeps := collectConstNames thm.value
            let (localTypeDeps, externalTypeDeps) := splitDependencies extractRoot typeDeps
            let (localValueDeps, externalValueDeps) := splitDependencies extractRoot valueDeps
            theorems := theorems.push
              { name := suffix
              , type := typeFmt.pretty
              , is_sorry := containsSorryAx thm.value
              , local_type_dependencies := localTypeDeps
              , local_value_dependencies := localValueDeps
              , external_type_dependencies := externalTypeDeps
              , external_value_dependencies := externalValueDeps
              }
        | _ => pure ()
  let sortedTheorems := theorems.qsort (fun a b => a.name < b.name)
  return Json.mkObj
    [ ("okay", toJson true)
    , ("theorem_count", toJson sortedTheorems.size)
    , ("theorems", toJson sortedTheorems)
    ]

syntax (name := autoformExtractTheoremsCmd) "autoform_extract_theorems" : command

@[command_elab autoformExtractTheoremsCmd] def elabAutoformExtractTheorems : CommandElab := fun stx => do
  match stx with
  | `(command| autoform_extract_theorems) =>
      let payload ← liftTermElabM theoremPayload
      emitJsonLine payload
  | _ => throwUnsupportedSyntax

end AutoformalizationEval.Tools
