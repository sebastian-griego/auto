import Lean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Basic

open Lean Meta

namespace AutoformalizationEval.Families

private def boolTypeExpr : Expr := mkConst ``Bool
private def boolFalseExpr : Expr := mkConst ``Bool.false
private def boolTrueExpr : Expr := mkConst ``Bool.true

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

private def fintypeInstCard (ty : Expr) : MetaM (Expr × Nat) := do
  let fintypeConst ← mkConstWithFreshMVarLevels ``Fintype
  let fintypeTy := mkApp fintypeConst ty
  match (← synthInstance? fintypeTy) with
  | none =>
      let tyFmt ← ppExpr ty
      throwError s!"[semantic_fail] set_fintype_missing:{tyFmt.pretty}"
  | some inst =>
      let cardConst ← mkConstWithFreshMVarLevels ``Fintype.card
      let cardExpr := mkApp2 cardConst ty inst
      let cardWhnf ← whnf cardExpr
      match natLitValue? cardWhnf with
      | some n => pure (inst, n)
      | none =>
          let cardReduced ← reduce cardExpr
          match natLitValue? cardReduced with
          | some n => pure (inst, n)
          | none => throwError "[semantic_fail] set_domain_card_nonliteral"

private def fintypeValues (ty : Expr) (inst : Expr) (card : Nat) : MetaM (Array Expr) := do
  if card == 0 then
    pure #[]
  else
    let equiv ←
      try
        let equivConst ← mkConstWithFreshMVarLevels ``Fintype.equivFin
        pure (mkApp2 equivConst ty inst)
      catch e =>
        throwError "[semantic_fail] set_equivfin_failed:{e.toMessageData}"
    let symmConst ← mkConstWithFreshMVarLevels ``Equiv.symm
    let inv := mkApp symmConst equiv
    let predN := card - 1
    let mut out : Array Expr := #[]
    for k in [0:card] do
      let finVal := mkApp2 (mkConst ``Fin.ofNat) (mkNatLit predN) (mkNatLit k)
      out := out.push (mkApp inv finVal)
    pure out

private def explicitDomainValues? (ty : Expr) : MetaM (Option (Array Expr)) := do
  let ty ← whnf ty
  if (← isDefEq ty boolTypeExpr) then
    return some #[boolFalseExpr, boolTrueExpr]

  let ty := ty.consumeMData
  if ty.getAppFn.constName? == some ``Fin then
    let args := ty.getAppArgs
    if args.size < 1 then
      return none
    match natLitValue? (args.get! 0) with
    | some n =>
        if n == 0 then
          return some #[]
        let predN := n - 1
        let vals := Id.run do
          let mut vals : Array Expr := #[]
          for k in [0:n] do
            vals := vals.push (mkApp2 (mkConst ``Fin.ofNat) (mkNatLit predN) (mkNatLit k))
          return vals
        return some vals
    | none =>
        return none

  match ty with
  | .const typeName _ =>
      let env ← getEnv
      match env.find? typeName with
      | some (.inductInfo info) =>
          if info.numParams != 0 || info.numIndices != 0 then
            return none
          if info.ctors.isEmpty || info.ctors.length > 32 then
            return none
          for ctorName in info.ctors do
            let ctorInfo ← getConstInfo ctorName
            let hasArgs ← forallTelescopeReducing ctorInfo.type fun ctorXs _ => do
              pure (!ctorXs.isEmpty)
            if hasArgs then
              return none
          return some (info.ctors.toArray.map mkConst)
      | _ =>
          return none
  | _ =>
      return none

private def appendValues (vals : List Expr) (arr : Array Expr) : List (Array Expr) :=
  vals.map (fun v => arr.push v)

private def allAssignments (domains : Array (Array Expr)) : List (Array Expr) :=
  domains.foldl
    (fun acc vals => acc.bind (appendValues vals.toList))
    [#[]]

private def assignmentToString (binders : Array Expr) (vals : Array Expr) : MetaM String := do
  let mut parts : Array String := #[]
  for i in [0:vals.size] do
    let decl ← (binders.get! i).fvarId!.getDecl
    let valFmt ← ppExpr (vals.get! i)
    parts := parts.push s!"{decl.userName} := {valFmt.pretty}"
  pure (String.intercalate ", " parts.toList)

private def collectDomains (binders : Array Expr) (enumCap : Nat) : MetaM (Array (Array Expr) × Nat) := do
  let mut domains : Array (Array Expr) := #[]
  let mut cap := 1
  for i in [0:binders.size] do
    let decl ← (binders.get! i).fvarId!.getDecl
    match (← explicitDomainValues? decl.type) with
    | some vals =>
        let card := vals.size
        if card == 0 then
          throwError "[semantic_fail] set_domain_empty_binder:{i}"
        cap := cap * card
        if cap > enumCap then
          throwError s!"[semantic_fail] set_enum_cap_exceeded:{cap}>{enumCap}"
        domains := domains.push vals
    | none =>
        let (inst, card) ←
          try
            fintypeInstCard decl.type
          catch _ =>
            throwError s!"[semantic_fail] set_domain_unsupported_binder:{i}:type={decl.type}"
        if card == 0 then
          throwError "[semantic_fail] set_domain_empty_binder:{i}"
        cap := cap * card
        if cap > enumCap then
          throwError s!"[semantic_fail] set_enum_cap_exceeded:{cap}>{enumCap}"
        let vals ← fintypeValues decl.type inst card
        domains := domains.push vals
  pure (domains, cap)

private def setCarrierType? (ty : Expr) : MetaM (Option Expr) := do
  let ty := ty.consumeMData
  if ty.getAppFn.constName? == some ``Set then
    let args := ty.getAppArgs
    if args.size < 1 then
      return none
    else
      return some (args.get! 0)

  let tyWhnf ← whnf ty
  let tyWhnf := tyWhnf.consumeMData
  if tyWhnf.getAppFn.constName? == some ``Set then
    let args := tyWhnf.getAppArgs
    if args.size < 1 then
      return none
    else
      return some (args.get! 0)

  match tyWhnf with
  | .forallE _ dom body _ =>
      if !body.hasLooseBVars && body.isSort then
        if body == mkSort levelZero then
          return some dom
        else
          return none
      else
        return none
  | _ =>
      return none

private def eqSetSides? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let e := e.consumeMData
  if e.getAppFn.constName? != some ``Eq then
    return none
  else
    let args := e.getAppArgs
    if args.size < 3 then
      return none
    else
      let eqTy := args.get! (args.size - 3)
      let some carrier ← setCarrierType? eqTy
        | return none
      return some (carrier, args.get! (args.size - 2), args.get! (args.size - 1))

private def carrierValues (carrier : Expr) : MetaM (Array Expr) := do
  match (← explicitDomainValues? carrier) with
  | some vals => pure vals
  | none =>
      let (inst, card) ← fintypeInstCard carrier
      fintypeValues carrier inst card

private def mkDecideWithClassical (prop : Expr) : MetaM Expr := do
  try
    mkDecide prop
  catch _ =>
    let decInst ← mkAppM ``Classical.dec #[prop]
    pure (mkApp2 (mkConst ``decide) prop decInst)

private def evalPropAsBool (prop : Expr) : MetaM Bool := do
  let propWhnf ← whnf prop
  let propReduced ← reduce propWhnf
  let decideExpr ← mkDecideWithClassical propReduced
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
      throwError "[semantic_fail] set_equality_noncomputable"

private def sideExtEqMismatch? (carrier lhs rhs : Expr) (enumCap : Nat)
    : MetaM (Option (Expr × Bool × Bool)) := do
  let vals ← carrierValues carrier
  if vals.isEmpty then
    throwError "[semantic_fail] set_carrier_empty"
  if vals.size > enumCap then
    throwError s!"[semantic_fail] set_carrier_enum_cap_exceeded:{vals.size}>{enumCap}"
  for x in vals do
    let lhsVal ← evalPropAsBool (mkApp lhs x)
    let rhsVal ← evalPropAsBool (mkApp rhs x)
    if lhsVal != rhsVal then
      return some (x, lhsVal, rhsVal)
  return none

private def boolAsString (b : Bool) : String :=
  if b then "true" else "false"

private def mismatchDetail (label : String) (mismatch : Expr × Bool × Bool) : MetaM String := do
  let (x, lhsVal, rhsVal) := mismatch
  let xFmt ← ppExpr x
  pure
    s!"{label}:x={xFmt.pretty}, lhs={boolAsString lhsVal}, rhs={boolAsString rhsVal}"

/-- Placeholder v0 checker retained for compatibility with frozen configurations. -/
def checkSetEqualityV0 (cand expected : Expr) : MetaM Unit := do
  if (← isDefEq cand expected) then
    pure ()
  else
    throwError "[semantic_fail] set_equality_mismatch"

/--
v1 deterministic checker for set equalities:
- enumerate finite binder assignments (bounded by `enumCap`)
- compare candidate and expected set sides extensionally (`∀ x, x ∈ A ↔ x ∈ B`)
- allow swapping equation sides
-/
def checkSetEqualityV1 (cand expected : Expr) (enumCap : Nat) : MetaM Unit := do
  if (← isDefEq cand expected) then
    pure ()
  else
    forallTelescopeReducing cand fun candXs candBody => do
      forallTelescopeReducing expected fun expXs expBody => do
        if candXs.size != expXs.size then
          throwError "[semantic_fail] set_binder_arity"

        let expectedBodyMapped := expBody.replaceFVars expXs candXs
        let (domains, _) ← collectDomains candXs enumCap
        let assignments := allAssignments domains
        let candFn ← mkLambdaFVars candXs candBody
        let expFn ← mkLambdaFVars candXs expectedBodyMapped

        for vals in assignments do
          let candInst ← whnf (mkAppN candFn vals)
          let expInst ← whnf (mkAppN expFn vals)

          let some (candCarrier, candLhs, candRhs) ← eqSetSides? candInst
            | throwError "[semantic_fail] set_expected_equality"
          let some (expCarrier, expLhs, expRhs) ← eqSetSides? expInst
            | throwError "[semantic_fail] set_expected_equality"

          unless (← isDefEq candCarrier expCarrier) do
            throwError "[semantic_fail] set_carrier_mismatch"

          let directLhsMismatch ← sideExtEqMismatch? candCarrier candLhs expLhs enumCap
          let directRhsMismatch ← sideExtEqMismatch? candCarrier candRhs expRhs enumCap
          let swappedLhsMismatch ← sideExtEqMismatch? candCarrier candLhs expRhs enumCap
          let swappedRhsMismatch ← sideExtEqMismatch? candCarrier candRhs expLhs enumCap

          let directOk := directLhsMismatch.isNone && directRhsMismatch.isNone
          let swappedOk := swappedLhsMismatch.isNone && swappedRhsMismatch.isNone
          unless (directOk || swappedOk) do
            let witness := (← assignmentToString candXs vals)
            let detail ←
              if let some m := directLhsMismatch then
                mismatchDetail "direct_lhs" m
              else if let some m := directRhsMismatch then
                mismatchDetail "direct_rhs" m
              else if let some m := swappedLhsMismatch then
                mismatchDetail "swapped_lhs" m
              else if let some m := swappedRhsMismatch then
                mismatchDetail "swapped_rhs" m
              else
                pure "no_detail"
            throwError s!"[semantic_fail] set_equality_mismatch:{witness};{detail}"

/-- Backward-compatible alias. -/
def checkSetEquality (cand expected : Expr) : MetaM Unit :=
  checkSetEqualityV0 cand expected

end AutoformalizationEval.Families
