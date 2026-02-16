import Lean

open Lean Meta

namespace AutoformalizationEval.Families

private def boolTypeExpr : Expr := mkConst ``Bool
private def boolFalseExpr : Expr := mkConst ``Bool.false
private def boolTrueExpr : Expr := mkConst ``Bool.true

private inductive Domain where
  | bool
  | fin (n : Nat)
  deriving BEq

private def domainSize : Domain → Nat
  | .bool => 2
  | .fin n => n

private partial def natLitValue? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .const ``Nat.zero _ => some 0
  | .app (.const ``Nat.succ _) e => (natLitValue? e).map Nat.succ
  | e =>
      let e := e.consumeMData
      if e.getAppFn.constName? == some ``OfNat.ofNat then
        let args := e.getAppArgs
        if args.size < 2 then
          none
        else
          natLitValue? (args.get! 1)
      else
        none

private def binderDomain? (ty : Expr) : MetaM (Option Domain) := do
  let ty ← whnf ty
  if (← isDefEq ty boolTypeExpr) then
    return some .bool

  let ty := ty.consumeMData
  if ty.getAppFn.constName? == some ``Fin then
    let args := ty.getAppArgs
    if args.size < 1 then
      return none
    match natLitValue? (args.get! 0) with
    | some n => return some (.fin n)
    | none => return none

  return none

private def finitePrefix (binders : Array Expr) : MetaM (Array Domain × Nat) := do
  let mut i := 0
  let mut domains : Array Domain := #[]
  while i < binders.size do
    let decl ← binders.get! i |>.fvarId!.getDecl
    if (← isProp decl.type) then
      return (domains, i)
    match (← binderDomain? decl.type) with
    | some (.fin 0) =>
        throwError "[semantic_fail] fin_domain_empty_binder:{i}"
    | some d =>
        domains := domains.push d
        i := i + 1
    | none =>
        throwError "[semantic_fail] fin_domain_unsupported_binder:{i}"
  return (domains, i)

private def domainValues : Domain → Array Expr
  | .bool =>
      #[boolFalseExpr, boolTrueExpr]
  | .fin n =>
      Id.run do
        if n == 0 then
          return #[]
        let mut out : Array Expr := #[]
        let predN := n - 1
        for k in [0:n] do
          out := out.push (mkApp2 (mkConst ``Fin.ofNat) (mkNatLit predN) (mkNatLit k))
        return out

private def appendValues (vals : List Expr) (arr : Array Expr) : List (Array Expr) :=
  vals.map (fun v => arr.push v)

private def allAssignments (domains : Array Domain) : List (Array Expr) :=
  domains.foldl
    (fun acc domain =>
      let vals := (domainValues domain).toList
      acc.bind (appendValues vals))
    [#[]]

private def assignmentCount (domains : Array Domain) : Nat :=
  domains.foldl (fun acc d => acc * domainSize d) 1

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
Finite truth-table checker for a deterministic fragment over leading binders:
- `Bool`
- `Fin n` for concrete small `n`

This enumerates all assignments and compares `decide` outputs.
-/
def checkFinTruthTable (cand expected : Expr) : MetaM Unit := do
  forallTelescopeReducing cand fun candXs candBody => do
    forallTelescopeReducing expected fun expXs expBody => do
      let (candDomains, candFiniteArity) ← finitePrefix candXs
      let (expDomains, expFiniteArity) ← finitePrefix expXs
      if candFiniteArity != expFiniteArity then
        throwError "[semantic_fail] truth_table_binder_arity"
      if candDomains != expDomains then
        throwError "[semantic_fail] truth_table_domain_mismatch"

      let nAssignments := assignmentCount candDomains
      if nAssignments > 256 then
        throwError "[semantic_fail] truth_table_enum_cap_exceeded"

      let candFiniteBinders := candXs.extract 0 candFiniteArity
      let expFiniteBinders := expXs.extract 0 expFiniteArity

      let candRestBinders := candXs.extract candFiniteArity candXs.size
      let expRestBinders := expXs.extract expFiniteArity expXs.size

      let candProp ← mkForallFVars candRestBinders candBody
      let expProp ← mkForallFVars expRestBinders expBody

      let candFn ← mkLambdaFVars candFiniteBinders candProp
      let expFn ← mkLambdaFVars expFiniteBinders expProp

      for vals in allAssignments candDomains do
        checkAssignment candFn expFn vals

end AutoformalizationEval.Families
