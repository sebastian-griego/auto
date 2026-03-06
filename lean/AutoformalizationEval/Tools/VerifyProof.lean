import Lean
import AutoformalizationEval.Tools.Common

open Lean Meta Elab Command

namespace AutoformalizationEval.Tools

private structure DeclEntry where
  suffix : String
  name : Name
  info : ConstantInfo

private def specRoot : Name := parseDottedName "Spec"
private def candRoot : Name := parseDottedName "Cand"

private def declEntriesUnderRoot (env : Environment) (root : Name) : Array DeclEntry :=
  let entries :=
    env.constants.toList.foldl (init := #[]) fun acc (pair : Name × ConstantInfo) =>
      let name := pair.1
      let info := pair.2
      if !nameHasRootPrefix name root then
        acc
      else
        let suffix := relativeToRootString name root
        if suffix.isEmpty then acc else acc.push { suffix, name, info }
  entries.qsort (fun a b => a.suffix < b.suffix)

private def findBySuffix (entries : Array DeclEntry) (suffix : String) : Option DeclEntry := Id.run do
  for entry in entries do
    if entry.suffix == suffix then
      return some entry
  return none

private def constValue? : ConstantInfo → Option Expr
  | .thmInfo info => some info.value
  | .defnInfo info => some info.value
  | .opaqueInfo info => some info.value
  | _ => none

private def supportedSpecKind (kind : String) : Bool :=
  kind == "thmInfo" || kind == "defnInfo" || kind == "opaqueInfo" || kind == "axiomInfo"

private def compareValueKind (kind : String) : Bool :=
  kind == "defnInfo" || kind == "opaqueInfo"

private def isDefEqClosed (lhs rhs : Expr) : MetaM Bool :=
  withNewMCtxDepth <| isDefEq lhs rhs

private def verifyProofPayload (permittedSorries : Array String) : MetaM Json := do
  let env ← getEnv
  let specDecls := declEntriesUnderRoot env specRoot
  let candDecls := declEntriesUnderRoot env candRoot
  let specSuffixSet :=
    specDecls.foldl (init := ({} : Std.HashSet String)) fun acc decl => acc.insert decl.suffix
  let permittedSet :=
    permittedSorries.foldl (init := ({} : Std.HashSet String)) fun acc suffix => acc.insert suffix

  let mut errors : Array String := #[]
  let mut warnings : Array String := #[]
  let mut failedDecls : Array String := #[]
  let mut matchedDecls : Array String := #[]
  let mut extraCandDecls : Array String := #[]

  for specDecl in specDecls do
    let suffix := specDecl.suffix
    let specKind := declKindTag specDecl.info
    if !supportedSpecKind specKind then
      errors := errors.push s!"unsupported_spec_kind:{suffix}:{specKind}"
      failedDecls := failedDecls.push suffix
    match findBySuffix candDecls suffix with
    | none =>
        errors := errors.push s!"missing_candidate:{suffix}"
        failedDecls := failedDecls.push suffix
    | some candDecl =>
        matchedDecls := matchedDecls.push suffix
        let candKind := declKindTag candDecl.info
        if supportedSpecKind specKind then
          if specKind != candKind then
            errors := errors.push s!"kind_mismatch:{suffix}:{specKind}!={candKind}"
            failedDecls := failedDecls.push suffix
          else
            let typeMatches ← isDefEqClosed specDecl.info.type candDecl.info.type
            unless typeMatches do
              errors := errors.push s!"type_mismatch:{suffix}"
              failedDecls := failedDecls.push suffix
            if typeMatches && compareValueKind specKind then
              match constValue? specDecl.info, constValue? candDecl.info with
              | some specVal, some candVal =>
                  if !containsSorryAx specVal then
                    let valueMatches ← isDefEqClosed specVal candVal
                    unless valueMatches do
                      errors := errors.push s!"value_mismatch:{suffix}"
                      failedDecls := failedDecls.push suffix
              | _, _ => pure ()

  for candDecl in candDecls do
    let suffix := candDecl.suffix
    if !specSuffixSet.contains suffix then
      extraCandDecls := extraCandDecls.push suffix
      let candKind := declKindTag candDecl.info
      if candKind == "axiomInfo" then
        errors := errors.push s!"extra_candidate_axiom:{suffix}"
      else
        warnings := warnings.push s!"extra_candidate_nonaxiom:{suffix}"

  for candDecl in candDecls do
    let suffix := candDecl.suffix
    if !permittedSet.contains suffix then
      match constValue? candDecl.info with
      | some value =>
          if containsSorryAx value then
            errors := errors.push s!"candidate_sorry:{suffix}"
            if specSuffixSet.contains suffix then
              failedDecls := failedDecls.push suffix
      | none => pure ()

  let errorsOut := sortUniqueStrings errors
  let warningsOut := sortUniqueStrings warnings
  let failedDeclsOut := sortUniqueStrings failedDecls
  let matchedDeclsOut := sortUniqueStrings matchedDecls
  let extraCandDeclsOut := sortUniqueStrings extraCandDecls
  let okay := errorsOut.isEmpty
  return Json.mkObj
    [ ("okay", toJson okay)
    , ("errors", toJson errorsOut)
    , ("warnings", toJson warningsOut)
    , ("failed_declarations", toJson failedDeclsOut)
    , ("matched_declarations", toJson matchedDeclsOut)
    , ("extra_candidate_declarations", toJson extraCandDeclsOut)
    ]

syntax (name := autoformVerifyProofCmd) "autoform_verify_proof" ("[" str,* "]")? : command

@[command_elab autoformVerifyProofCmd] def elabAutoformVerifyProof : CommandElab := fun stx => do
  let permittedSorries ←
    match stx with
    | `(command| autoform_verify_proof) => pure #[]
    | `(command| autoform_verify_proof [$[$permitted:str],*]) =>
        pure <| sortUniqueStrings <| permitted.map (fun s => s.getString)
    | _ => throwUnsupportedSyntax
  let payload ← liftTermElabM <| verifyProofPayload permittedSorries
  emitJsonLine payload

end AutoformalizationEval.Tools
