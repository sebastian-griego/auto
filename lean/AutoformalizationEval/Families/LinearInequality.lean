import Lean

open Lean Meta

namespace AutoformalizationEval.Families

private inductive ArithType where
  | nat
  | int
  deriving BEq

private inductive RelationKind where
  | lt
  | le
  deriving BEq

private structure AffineForm where
  coeffs : Array Int
  const : Int
  deriving BEq

private structure ParsedAffine where
  form : AffineForm
  literal? : Option Nat

private structure ConstraintNorm where
  arithType : ArithType
  relation : RelationKind
  form : AffineForm
  deriving BEq

private def arithTypeToString : ArithType → String
  | .nat => "Nat"
  | .int => "Int"

private def relationToString : RelationKind → String
  | .lt => "<"
  | .le => "<="

private def mkZeroForm (arity : Nat) : AffineForm :=
  { coeffs := mkArray arity 0, const := 0 }

private def mkConstForm (arity : Nat) (value : Int) : AffineForm :=
  { coeffs := mkArray arity 0, const := value }

private def mkVarForm (arity idx : Nat) : AffineForm :=
  { coeffs := (mkArray arity 0).set! idx 1, const := 0 }

private def mapCoeffs (f : Int → Int) (coeffs : Array Int) : Array Int :=
  coeffs.map f

private def zipCoeffs (f : Int → Int → Int) (xs ys : Array Int) : Array Int :=
  Id.run do
    let mut out : Array Int := #[]
    for i in [0:xs.size] do
      out := out.push (f (xs.get! i) (ys.get! i))
    out

private def addForm (lhs rhs : AffineForm) : AffineForm :=
  { coeffs := zipCoeffs (· + ·) lhs.coeffs rhs.coeffs
    const := lhs.const + rhs.const }

private def subForm (lhs rhs : AffineForm) : AffineForm :=
  { coeffs := zipCoeffs (· - ·) lhs.coeffs rhs.coeffs
    const := lhs.const - rhs.const }

private def smulNatForm (n : Nat) (form : AffineForm) : AffineForm :=
  let scale := Int.ofNat n
  { coeffs := mapCoeffs (fun coeff => scale * coeff) form.coeffs
    const := scale * form.const }

private def coeffsToString (coeffs : Array Int) : String :=
  let parts := coeffs.toList.map (fun coeff => s!"{coeff}")
  "[" ++ String.intercalate "," parts ++ "]"

private def constraintToString (norm : ConstraintNorm) : String :=
  s!"type={arithTypeToString norm.arithType} rel={relationToString norm.relation} coeffs={coeffsToString norm.form.coeffs} const={norm.form.const}"

private def throwUnsupportedTerm (side : String) (reason : String) : MetaM α :=
  throwError s!"[semantic_fail] linear_inequality_unsupported_{side}:{reason}"

private def binderIndexOf? (binders : Array Expr) (e : Expr) : Option Nat :=
  match e with
  | .fvar fid =>
      Id.run do
        let mut i := 0
        while i < binders.size do
          if (binders.get! i).fvarId! == fid then
            return some i
          i := i + 1
        return none
  | _ => none

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

private def binaryOpArgs? (op : Name) (e : Expr) : Option (Expr × Expr) := do
  let e := e.consumeMData
  if e.getAppFn.constName? != some op then
    none
  else
    let args := e.getAppArgs
    if args.size < 2 then
      none
    else
      some (args.get! (args.size - 2), args.get! (args.size - 1))

private def relationArgs? (e : Expr) : Option (RelationKind × Expr × Expr) := do
  let e := e.consumeMData
  let args := e.getAppArgs
  if args.size < 4 then
    none
  else if e.getAppFn.constName? == some ``LT.lt then
    some (.lt, args.get! (args.size - 2), args.get! (args.size - 1))
  else if e.getAppFn.constName? == some ``LE.le then
    some (.le, args.get! (args.size - 2), args.get! (args.size - 1))
  else
    none

private def unsupportedHeadReason (e : Expr) : String :=
  match e.consumeMData with
  | .letE .. => "let"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | expr =>
      match expr.getAppFn.constName? with
      | some ``HSub.hSub => "sub"
      | some ``Sub.sub => "sub"
      | some ``HDiv.hDiv => "div"
      | some ``Div.div => "div"
      | some ``Neg.neg => "neg"
      | some ``ite => "if"
      | some ``dite => "if"
      | some name =>
          let head := name.toString
          if head == "abs" || head.endsWith ".abs" || head.endsWith "Abs.abs" then
            "abs"
          else if head.endsWith ".max" || head == "max" || head.endsWith "Max.max" then
            "max"
          else if head.endsWith ".min" || head == "min" || head.endsWith "Min.min" then
            "min"
          else if head == "HMul.hMul" || head == "Mul.mul" then
            "nonlinear_mul"
          else
            head
      | none => "term"

private def arithTypeOfType? (ty : Expr) : MetaM (Option ArithType) := do
  let ty ← whnf ty
  let ty := ty.consumeMData
  if ty.isConstOf ``Nat then
    return some .nat
  if ty.isConstOf ``Int then
    return some .int
  return none

private def exprArithType? (e : Expr) : MetaM (Option ArithType) := do
  arithTypeOfType? (← inferType e)

private def requireSupportedBinder (binder : Expr) (idx : Nat) : MetaM Unit := do
  let decl ← binder.fvarId!.getDecl
  let some _ ← arithTypeOfType? decl.type
    | throwError s!"[semantic_fail] linear_inequality_unsupported_binder:{idx}"
  pure ()

private partial def parseAffineExpr
    (binders : Array Expr)
    (side : String)
    (e : Expr) : MetaM ParsedAffine := do
  let e := e.consumeMData
  if let some idx := binderIndexOf? binders e then
    pure { form := mkVarForm binders.size idx, literal? := none }
  else if let some n := natLitValue? e then
    pure { form := mkConstForm binders.size (Int.ofNat n), literal? := some n }
  else if let some (lhs, rhs) := binaryOpArgs? ``HAdd.hAdd e then
    let lhsParsed ← parseAffineExpr binders side lhs
    let rhsParsed ← parseAffineExpr binders side rhs
    pure { form := addForm lhsParsed.form rhsParsed.form, literal? := none }
  else if let some (lhs, rhs) := binaryOpArgs? ``HMul.hMul e then
    let lhsParsed ← parseAffineExpr binders side lhs
    let rhsParsed ← parseAffineExpr binders side rhs
    match lhsParsed.literal?, rhsParsed.literal? with
    | some n, _ =>
        pure
          { form := smulNatForm n rhsParsed.form
            literal? := none }
    | _, some n =>
        pure
          { form := smulNatForm n lhsParsed.form
            literal? := none }
    | none, none =>
        throwUnsupportedTerm side "nonlinear_mul"
  else
    throwUnsupportedTerm side (unsupportedHeadReason e)

private def normalizeConstraint
    (binders : Array Expr)
    (side : String)
    (body : Expr) : MetaM ConstraintNorm := do
  for i in [0:binders.size] do
    requireSupportedBinder (binders.get! i) i
  let some (relation, lhs, rhs) := relationArgs? body
    | throwError s!"[semantic_fail] linear_inequality_expected_relation:{side}"
  let some arithType ← exprArithType? lhs
    | throwError s!"[semantic_fail] linear_inequality_unsupported_relation_type:{side}"
  let lhsParsed ← parseAffineExpr binders side lhs
  let rhsParsed ← parseAffineExpr binders side rhs
  pure
    { arithType := arithType
      relation := relation
      form := subForm lhsParsed.form rhsParsed.form }

/--
Deterministic checker for strict affine inequalities over leading `Nat`/`Int` binders.
It accepts only direct affine normalization:
- reassociation/commutation of `+`
- moving affine terms across the relation
- combining repeated variables
- numeral scalar multiplication
- optional distribution that arises from recursive scalar parsing
-/
def checkLinearInequalityV1 (cand expected : Expr) : MetaM Unit := do
  forallTelescopeReducing cand fun candXs candBody => do
    forallTelescopeReducing expected fun expXs expBody => do
      if candXs.size != expXs.size then
        throwError "[semantic_fail] linear_inequality_binder_arity"

      let expectedBodyMapped := expBody.replaceFVars expXs candXs
      let candNorm ← normalizeConstraint candXs "cand" candBody
      let expNorm ← normalizeConstraint candXs "expected" expectedBodyMapped

      unless candNorm.arithType == expNorm.arithType do
        throwError
          s!"[semantic_fail] linear_inequality_type_mismatch:cand={arithTypeToString candNorm.arithType}:expected={arithTypeToString expNorm.arithType}"

      unless candNorm.relation == expNorm.relation do
        throwError
          s!"[semantic_fail] linear_inequality_relation_mismatch:cand={relationToString candNorm.relation}:expected={relationToString expNorm.relation}"

      unless candNorm.form == expNorm.form do
        throwError
          s!"[semantic_fail] linear_inequality_mismatch:cand={constraintToString candNorm} expected={constraintToString expNorm}"

end AutoformalizationEval.Families
