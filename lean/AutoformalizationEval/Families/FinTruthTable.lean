import Lean

open Lean Meta

namespace AutoformalizationEval.Families

private def boolTypeExpr : Expr := mkConst ``Bool
private def boolFalseExpr : Expr := mkConst ``Bool.false
private def boolTrueExpr : Expr := mkConst ``Bool.true

private def boolPrefixLength (binders : Array Expr) : MetaM Nat := do
  let mut i := 0
  while i < binders.size do
    let decl ← binders.get! i |>.fvarId!.getDecl
    if (← isDefEq decl.type boolTypeExpr) then
      i := i + 1
    else if (← isProp decl.type) then
      return i
    else
      throwError "[semantic_fail] fin_domain_unsupported_binder:{i}"
  return i

private def boolAssignments : Nat → List (Array Expr)
  | 0 => [#[]]
  | n + 1 =>
      (boolAssignments n).bind fun vals =>
        [vals.push boolFalseExpr, vals.push boolTrueExpr]

private def evalPropAsBool (prop : Expr) : MetaM Bool := do
  let decideExpr ← mkDecide prop
  let reduced ← whnf decideExpr
  if reduced.isConstOf ``Bool.true then
    pure true
  else if reduced.isConstOf ``Bool.false then
    pure false
  else
    let reduced' ← reduce reduced
    if reduced'.isConstOf ``Bool.true then
      pure true
    else if reduced'.isConstOf ``Bool.false then
      pure false
    else
      throwError "[semantic_fail] truth_table_noncomputable"

private def checkAssignment (candFn expectedFn : Expr) (vals : Array Expr) : MetaM Unit := do
  let candProp := mkAppN candFn vals
  let expectedProp := mkAppN expectedFn vals
  let candVal ← evalPropAsBool candProp
  let expectedVal ← evalPropAsBool expectedProp
  unless candVal == expectedVal do
    throwError "[semantic_fail] truth_table_mismatch"

/--
Finite truth-table checker for Bool-binder fragments.
This enumerates all assignments and compares `decide` outputs.
-/
def checkFinTruthTable (cand expected : Expr) : MetaM Unit := do
  forallTelescopeReducing cand fun candXs candBody => do
    forallTelescopeReducing expected fun expXs expBody => do
      let candBoolArity ← boolPrefixLength candXs
      let expBoolArity ← boolPrefixLength expXs
      if candBoolArity != expBoolArity then
        throwError "[semantic_fail] truth_table_binder_arity"

      let assignmentCount := Nat.pow 2 candBoolArity
      if assignmentCount > 256 then
        throwError "[semantic_fail] truth_table_enum_cap_exceeded"

      let candBoolBinders := candXs.extract 0 candBoolArity
      let expBoolBinders := expXs.extract 0 expBoolArity

      let candRestBinders := candXs.extract candBoolArity candXs.size
      let expRestBinders := expXs.extract expBoolArity expXs.size

      let candProp ← mkForallFVars candRestBinders candBody
      let expProp ← mkForallFVars expRestBinders expBody

      let candFn ← mkLambdaFVars candBoolBinders candProp
      let expFn ← mkLambdaFVars expBoolBinders expProp

      for vals in boolAssignments candBoolArity do
        checkAssignment candFn expFn vals

end AutoformalizationEval.Families
