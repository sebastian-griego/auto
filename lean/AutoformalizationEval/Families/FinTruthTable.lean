import Lean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

open Lean Meta

namespace AutoformalizationEval.Families

private def boolTypeExpr : Expr := mkConst ``Bool
private def boolFalseExpr : Expr := mkConst ``Bool.false
private def boolTrueExpr : Expr := mkConst ``Bool.true

private inductive Domain where
  | bool
  | fin (n : Nat)
  | enum (typeName : Name) (ctors : Array Name)
  | fintype (card : Nat)
  deriving BEq

private def domainSize : Domain → Nat
  | .bool => 2
  | .fin n => n
  | .enum _ ctors => ctors.size
  | .fintype card => card

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

  match ty.consumeMData with
  | .const typeName _ =>
      let env ← getEnv
      match env.find? typeName with
      | some (.inductInfo info) =>
          if info.numParams != 0 || info.numIndices != 0 then
            return none
          if info.ctors.isEmpty || info.ctors.length > 32 then
            return none

          -- Keep enum support deterministic by requiring all constructors to be nullary.
          for ctorName in info.ctors do
            let ctorInfo ← getConstInfo ctorName
            let hasArgs ← forallTelescopeReducing ctorInfo.type fun ctorXs _ => do
              pure (!ctorXs.isEmpty)
            if hasArgs then
              return none

          return some (.enum typeName info.ctors.toArray)
      | _ => return none
  | _ =>
      return none

private def fintypeCard? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnf ty
  let fintypeTy := mkApp (mkConst ``Fintype) ty
  match (← synthInstance? fintypeTy) with
  | none => pure none
  | some inst =>
      let cardExpr := mkApp2 (mkConst ``Fintype.card) ty inst
      let cardWhnf ← whnf cardExpr
      match natLitValue? cardWhnf with
      | some n => pure (some n)
      | none =>
          let cardReduced ← reduce cardExpr
          pure (natLitValue? cardReduced)

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
        match (← fintypeCard? decl.type) with
        | some 0 =>
            throwError "[semantic_fail] fin_domain_empty_binder:{i}"
        | some n =>
            domains := domains.push (.fintype n)
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
  | .enum _ ctors =>
      ctors.map mkConst
  | .fintype _ =>
      #[]

private def isExplicitDomain : Domain → Bool
  | .bool => true
  | .fin _ => true
  | .enum _ _ => true
  | .fintype _ => false

private def allDomainsExplicit (domains : Array Domain) : Bool :=
  domains.all isExplicitDomain

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

private def assignmentToString (binders : Array Expr) (vals : Array Expr) : MetaM String := do
  let mut parts : Array String := #[]
  for i in [0:vals.size] do
    let decl ← (binders.get! i).fvarId!.getDecl
    let valFmt ← ppExpr (vals.get! i)
    parts := parts.push s!"{decl.userName} := {valFmt.pretty}"
  pure (String.intercalate ", " parts.toList)

/--
Finite truth-table checker for a deterministic fragment over leading binders:
- `Bool`
- `Fin n` for concrete small `n`
- small enum inductives with nullary constructors

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
      let expPropMapped := expProp.replaceFVars expFiniteBinders candFiniteBinders

      if allDomainsExplicit candDomains then
        let candFn ← mkLambdaFVars candFiniteBinders candProp
        let expFn ← mkLambdaFVars expFiniteBinders expProp
        let mut firstRef : Option Bool := none
        let mut refVaries : Bool := false
        for vals in allAssignments candDomains do
          let candProp := mkAppN candFn vals
          let expectedProp := mkAppN expFn vals
          let candVal ← evalPropAsBool candProp
          let expectedVal ← evalPropAsBool expectedProp

          match firstRef with
          | none =>
              firstRef := some expectedVal
          | some b =>
              if expectedVal != b then
                refVaries := true

          unless candVal == expectedVal do
            let witness := (← assignmentToString candFiniteBinders vals)
            throwError s!"[semantic_fail] truth_table_mismatch:{witness}"
        unless refVaries do
          throwError "[semantic_fail] truth_table_reference_constant"
      else
        -- Fallback path for supported finite binders with `Fintype` instances:
        -- compare universally quantified equivalence via `decide`.
        let iffProp := mkApp2 (mkConst ``Iff) candProp expPropMapped
        let fullProp ← mkForallFVars candFiniteBinders iffProp
        unless (← evalPropAsBool fullProp) do
          throwError "[semantic_fail] truth_table_mismatch"

end AutoformalizationEval.Families
