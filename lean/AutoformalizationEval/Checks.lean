import Lean
import AutoformalizationEval.Families.RingIdentity
import AutoformalizationEval.Families.FinTruthTable
import AutoformalizationEval.Families.SetEquality

open Lean Meta Elab Command

namespace AutoformalizationEval

private def throwShapeFail (msg : String) : MetaM Unit :=
  throwError "[shape_fail] {msg}"

private partial def containsAnyFVar (fvars : Array FVarId) : Expr → Bool
  | .fvar fid => fvars.any (fun fvar => fvar == fid)
  | .app fn arg => containsAnyFVar fvars fn || containsAnyFVar fvars arg
  | .lam _ ty body _ => containsAnyFVar fvars ty || containsAnyFVar fvars body
  | .forallE _ ty body _ => containsAnyFVar fvars ty || containsAnyFVar fvars body
  | .letE _ ty val body _ =>
      containsAnyFVar fvars ty || containsAnyFVar fvars val || containsAnyFVar fvars body
  | .mdata _ body => containsAnyFVar fvars body
  | .proj _ _ body => containsAnyFVar fvars body
  | _ => false

private def checkFamilyOuterShape (family : String) (binders : Array Expr) (body : Expr) : MetaM Unit := do
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
  else if family == "fin_truth_table" then
    let bodyWhnf ← whnf body
    if bodyWhnf.isConstOf ``True || bodyWhnf.isConstOf ``False then
      throwShapeFail "truth_table_constant_prop"
    let binderFVars := binders.map (fun b => b.fvarId!)
    unless containsAnyFVar binderFVars body do
      throwShapeFail "truth_table_no_binder_ref"
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
      checkFamilyOuterShape family candXs candBody
      checkFamilyOuterShape family expXs expBody

private def requireFragmentKey (checkKey fragmentKey expectedFragment : String) : MetaM Unit := do
  unless fragmentKey == expectedFragment do
    throwError
      s!"[semantic_fail] fragment_key_mismatch:{checkKey}:{fragmentKey}!={expectedFragment}"

private def throwFragmentKeyMismatch (checkKey fragmentKey : String) (allowed : List String) : MetaM Unit := do
  let expected := String.intercalate "|" allowed
  throwError s!"[semantic_fail] fragment_key_mismatch:{checkKey}:{fragmentKey}!={expected}"

/-- Dispatch into family-specific semantic checkers. -/
def checkFamily (checkKey : String) (fragmentKey : String) (enumCap : Nat) (cand expected : Expr) : MetaM Unit := do
  match checkKey with
  | "ring_identity_norm" =>
      match fragmentKey with
      | "ring_identity_norm_v1" =>
          Families.checkRingIdentityNormV1 cand expected
      | "ring_identity_norm_v2" =>
          Families.checkRingIdentityNormV2 cand expected
      | _ =>
          throwFragmentKeyMismatch checkKey fragmentKey ["ring_identity_norm_v1", "ring_identity_norm_v2"]
  | "fin_truth_table" =>
      requireFragmentKey checkKey fragmentKey "fin_truth_table_v1"
      Families.checkFinTruthTable cand expected enumCap
  | "set_equality_norm" =>
      requireFragmentKey checkKey fragmentKey "set_equality_norm_v0"
      Families.checkSetEquality cand expected
  | _ => throwError "[semantic_fail] unknown_check_key:{checkKey}"

/-- Command-level entrypoint used by rendered Test2 files. -/
syntax (name := autoformCheckCmd) "autoform_check" str str str num : command

@[command_elab autoformCheckCmd] def elabAutoformCheck : CommandElab := fun stx => do
  match stx with
  | `(command| autoform_check $family:str $check:str $fragment:str $enumCap:num) =>
      liftTermElabM do
        let familyName := family.getString
        let checkKey := check.getString
        let fragmentKey := fragment.getString
        let enumCapNat := enumCap.getNat
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
            checkFamily checkKey fragmentKey enumCapNat candExpr expectedExpr
  | _ => throwUnsupportedSyntax

end AutoformalizationEval
