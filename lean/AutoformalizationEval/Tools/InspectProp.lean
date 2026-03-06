import Lean
import AutoformalizationEval.Tools.Common

open Lean Meta Elab Command

namespace AutoformalizationEval.Tools

private structure LeadingForall where
  name : String
  type : String
deriving ToJson

private def inspectRoot : Name := parseDottedName "InspectTmp"
private def targetName : Name := parseDottedName "InspectTmp.target"

private def constValue? : ConstantInfo → Option Expr
  | .thmInfo info => some info.value
  | .defnInfo info => some info.value
  | .opaqueInfo info => some info.value
  | _ => none

private def splitDependencies (deps : Array Name) : Array String × Array String := Id.run do
  let mut localDeps : Array String := #[]
  let mut externalDeps : Array String := #[]
  for dep in deps do
    if isInternalOrAuxName dep then
      pure ()
    else if nameHasRootPrefix dep inspectRoot then
      let localName := relativeToRootString dep inspectRoot
      if !localName.isEmpty then
        localDeps := localDeps.push localName
    else
      externalDeps := externalDeps.push (toString dep)
  return (sortUniqueStrings localDeps, sortUniqueStrings externalDeps)

private partial def leadingForalls (expr : Expr) : MetaM (Array LeadingForall) := do
  let rec loop (current : Expr) (acc : Array LeadingForall) : MetaM (Array LeadingForall) := do
    match current.consumeMData with
    | .forallE binderName binderType body _ =>
        let binderTypeFmt ← ppExpr binderType
        loop body (acc.push { name := binderName.toString, type := binderTypeFmt.pretty })
    | _ => pure acc
  loop expr #[]

private def mkFailurePayload (typePretty : String := "") : Json :=
  Json.mkObj
    [ ("okay", toJson false)
    , ("expr_pretty", toJson "")
    , ("type_pretty", toJson typePretty)
    , ("whnf_pretty", toJson "")
    , ("contains_sorry", toJson false)
    , ("leading_forall_count", toJson (0 : Nat))
    , ("leading_foralls", toJson (#[] : Array LeadingForall))
    , ("local_dependencies", toJson (#[] : Array String))
    , ("external_dependencies", toJson (#[] : Array String))
    ]

private def inspectPropPayload : MetaM Json := do
  let env ← getEnv
  let some targetInfo := env.find? targetName
    | return mkFailurePayload
  let targetTypeFmt ← ppExpr targetInfo.type
  let targetTypeIsProp ← withNewMCtxDepth <| isDefEq targetInfo.type (mkSort levelZero)
  if !targetTypeIsProp then
    return mkFailurePayload targetTypeFmt.pretty
  let some targetExpr := constValue? targetInfo
    | return mkFailurePayload targetTypeFmt.pretty

  let exprFmt ← ppExpr targetExpr
  let inferredType ← inferType targetExpr
  let inferredTypeFmt ← ppExpr inferredType
  let whnfExpr ← whnf targetExpr
  let whnfFmt ← ppExpr whnfExpr
  let leading := (← leadingForalls targetExpr)
  let deps := collectConstNames targetExpr
  let (localDeps, externalDeps) := splitDependencies deps
  return Json.mkObj
    [ ("okay", toJson true)
    , ("expr_pretty", toJson exprFmt.pretty)
    , ("type_pretty", toJson inferredTypeFmt.pretty)
    , ("whnf_pretty", toJson whnfFmt.pretty)
    , ("contains_sorry", toJson <| containsSorryAx targetExpr)
    , ("leading_forall_count", toJson leading.size)
    , ("leading_foralls", toJson leading)
    , ("local_dependencies", toJson localDeps)
    , ("external_dependencies", toJson externalDeps)
    ]

syntax (name := autoformInspectPropCmd) "autoform_inspect_prop" : command

@[command_elab autoformInspectPropCmd] def elabAutoformInspectProp : CommandElab := fun stx => do
  match stx with
  | `(command| autoform_inspect_prop) =>
      let payload ← liftTermElabM inspectPropPayload
      emitJsonLine payload
  | _ => throwUnsupportedSyntax

end AutoformalizationEval.Tools
