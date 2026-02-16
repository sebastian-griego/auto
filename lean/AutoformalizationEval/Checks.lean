import Lean
import AutoformalizationEval.Families.RingIdentity
import AutoformalizationEval.Families.FinTruthTable
import AutoformalizationEval.Families.SetEquality

open Lean Meta Elab Command

namespace AutoformalizationEval

private def throwShapeFail (msg : String) : MetaM Unit :=
  throwError "[shape_fail] {msg}"

private def checkFamilyOuterShape (family : String) (body : Expr) : MetaM Unit := do
  let head := (body.consumeMData.getAppFn).constName?
  if family == "ring_identity" then
    unless head == some ``Eq do
      throwShapeFail "expected_eq"
  else if family == "set_equality" then
    unless head == some ``Eq do
      throwShapeFail "expected_set_eq"
  else if family == "linear_inequality" then
    unless head == some ``LT.lt || head == some ``LE.le do
      throwShapeFail "expected_lt_or_le"
  else
    pure ()

/--
Shape guard:
- checks binder counts
- checks binder type alignment up to definitional equality
- checks coarse outer form for selected families
-/
def checkShape (family : String) (cand expected : Expr) : MetaM Unit := do
  forallTelescopeReducing cand fun candXs candBody => do
    forallTelescopeReducing expected fun expXs expBody => do
      if candXs.size != expXs.size then
        throwShapeFail "binder_arity"
      for i in [0:candXs.size] do
        let candDecl ← (candXs.get! i).fvarId!.getDecl
        let expDecl ← (expXs.get! i).fvarId!.getDecl
        let expTyMapped :=
          expDecl.type.replaceFVars (expXs.extract 0 i) (candXs.extract 0 i)
        unless (← isDefEq candDecl.type expTyMapped) do
          throwShapeFail s!"binder_type:{i}"
      checkFamilyOuterShape family candBody
      checkFamilyOuterShape family expBody

/-- Dispatch into family-specific semantic checkers. -/
def checkFamily (checkKey : String) (cand expected : Expr) : MetaM Unit := do
  match checkKey with
  | "ring_identity_norm" => Families.checkRingIdentityNorm cand expected
  | "fin_truth_table" => Families.checkFinTruthTable cand expected
  | "set_equality_norm" => Families.checkSetEquality cand expected
  | _ => throwError "[semantic_fail] unknown_check_key:{checkKey}"

/-- Command-level entrypoint used by rendered Test2 files. -/
syntax (name := autoformCheckCmd) "autoform_check" str str : command

@[command_elab autoformCheckCmd] def elabAutoformCheck : CommandElab := fun stx => do
  match stx with
  | `(command| autoform_check $family:str $check:str) =>
      liftTermElabM do
        let familyName := family.getString
        let checkKey := check.getString
        let candInfo ← getConstInfo `cand
        let expectedInfo ← getConstInfo `expected
        lambdaTelescope candInfo.value! fun candCtx candExpr => do
          lambdaTelescope expectedInfo.value! fun expCtx expectedExprRaw => do
            if candCtx.size != expCtx.size then
              throwError "[shape_fail] context_binder_arity"
            for i in [0:candCtx.size] do
              let candDecl ← (candCtx.get! i).fvarId!.getDecl
              let expDecl ← (expCtx.get! i).fvarId!.getDecl
              let expTyMapped :=
                expDecl.type.replaceFVars (expCtx.extract 0 i) (candCtx.extract 0 i)
              unless (← isDefEq candDecl.type expTyMapped) do
                throwError s!"[shape_fail] context_binder_type:{i}"
            let expectedExpr := expectedExprRaw.replaceFVars expCtx candCtx
            checkShape familyName candExpr expectedExpr
            checkFamily checkKey candExpr expectedExpr
  | _ => throwUnsupportedSyntax

end AutoformalizationEval
