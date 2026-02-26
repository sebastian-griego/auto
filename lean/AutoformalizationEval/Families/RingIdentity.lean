import Lean

open Lean Meta

namespace AutoformalizationEval.Families

abbrev Monomial := List Nat
abbrev Poly := List (Monomial × Nat)

private def monoCompare : Monomial → Monomial → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      match compare a b with
      | .eq => monoCompare as bs
      | .lt => .lt
      | .gt => .gt

private def polyConst (n : Nat) : Poly :=
  if n == 0 then
    []
  else
    [([], n)]

private def polyVar (idx : Nat) : Poly :=
  [([idx], 1)]

private def insertTerm (mono : Monomial) (coeff : Nat) : Poly → Poly
  | [] =>
      if coeff == 0 then [] else [(mono, coeff)]
  | (mono', coeff') :: rest =>
      match monoCompare mono mono' with
      | .lt =>
          if coeff == 0 then
            (mono', coeff') :: rest
          else
            (mono, coeff) :: (mono', coeff') :: rest
      | .eq =>
          let coeff'' := coeff + coeff'
          if coeff'' == 0 then
            rest
          else
            (mono, coeff'') :: rest
      | .gt =>
          (mono', coeff') :: insertTerm mono coeff rest

private def polyAdd (p q : Poly) : Poly :=
  q.foldl (fun acc term => insertTerm term.1 term.2 acc) p

private def polyMul (p q : Poly) : Poly :=
  p.foldl
    (fun acc t1 =>
      q.foldl
        (fun acc' t2 =>
          let mono := t1.1 ++ t2.1
          let coeff := t1.2 * t2.2
          insertTerm mono coeff acc')
        acc)
    []

private def monoToString (mono : Monomial) : String :=
  if mono.isEmpty then
    "1"
  else
    String.intercalate "*" (mono.map (fun idx => s!"x{idx}"))

private def termToString (term : Monomial × Nat) : String :=
  let mono := term.1
  let coeff := term.2
  if mono.isEmpty then
    s!"{coeff}"
  else if coeff == 1 then
    monoToString mono
  else
    s!"{coeff}*{monoToString mono}"

private def polyToString (poly : Poly) : String :=
  match poly with
  | [] => "0"
  | _ => String.intercalate " + " (poly.map termToString)

private def eqNormToString (eqNorm : Poly × Poly) : String :=
  s!"{polyToString eqNorm.1} = {polyToString eqNorm.2}"

private def eqNormMatches (candNorm expNorm : Poly × Poly) : Bool :=
  candNorm == expNorm || (candNorm.1 == expNorm.2 && candNorm.2 == expNorm.1)

private def insertEverywhere {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys =>
      (x :: y :: ys) :: (insertEverywhere x ys).map (fun zs => y :: zs)

private def listPermutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      (listPermutations xs).bind (insertEverywhere x)

private def binderPermutations (arity : Nat) : List (Array Nat) :=
  (listPermutations (List.range arity)).map List.toArray

private def renameIndexByPerm (perm : Array Nat) (idx : Nat) : Nat :=
  if h : idx < perm.size then
    perm.get ⟨idx, h⟩
  else
    idx

private def renameMonomial (mono : Monomial) (renameIdx : Nat → Nat) : Monomial :=
  mono.map renameIdx

private def renamePoly (poly : Poly) (renameIdx : Nat → Nat) : Poly :=
  poly.foldl
    (fun acc term => insertTerm (renameMonomial term.1 renameIdx) term.2 acc)
    []

private def renameEqNorm (eqNorm : Poly × Poly) (renameIdx : Nat → Nat) : Poly × Poly :=
  (renamePoly eqNorm.1 renameIdx, renamePoly eqNorm.2 renameIdx)

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

private def natLitValue? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

private def ofNatValue? (e : Expr) : Option Nat := do
  let e := e.consumeMData
  if e.getAppFn.constName? != some ``OfNat.ofNat then
    none
  else
    let args := e.getAppArgs
    if args.size < 2 then
      none
    else
      natLitValue? (args.get! 1)

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

private def eqSides? (e : Expr) : Option (Expr × Expr) := do
  let e := e.consumeMData
  if e.getAppFn.constName? != some ``Eq then
    none
  else
    let args := e.getAppArgs
    if args.size < 3 then
      none
    else
      some (args.get! (args.size - 2), args.get! (args.size - 1))

partial def normalizeExpr (binders : Array Expr) (e : Expr) : MetaM Poly := do
  let e := e.consumeMData
  if let some idx := binderIndexOf? binders e then
    pure (polyVar idx)
  else if let some n := ofNatValue? e then
    pure (polyConst n)
  else if let some (a, b) := binaryOpArgs? ``HAdd.hAdd e then
    pure (polyAdd (← normalizeExpr binders a) (← normalizeExpr binders b))
  else if let some (a, b) := binaryOpArgs? ``HMul.hMul e then
    pure (polyMul (← normalizeExpr binders a) (← normalizeExpr binders b))
  else
    throwError "[semantic_fail] ring_unsupported_term:{e}"

private def normalizeEquation (binders : Array Expr) (body : Expr) : MetaM (Poly × Poly) := do
  match eqSides? body with
  | none => throwError "[semantic_fail] ring_expected_equality"
  | some (lhs, rhs) =>
      pure (← normalizeExpr binders lhs, ← normalizeExpr binders rhs)

/-- Strict v1 checker: binder positions are compared directly (no binder permutation invariance). -/
def checkRingIdentityNormV1 (cand expected : Expr) : MetaM Unit := do
  forallTelescopeReducing cand fun candXs candBody => do
    forallTelescopeReducing expected fun expXs expBody => do
      if candXs.size != expXs.size then
        throwError "[semantic_fail] ring_binder_arity"

      let candNorm ← normalizeEquation candXs candBody
      let expNorm ← normalizeEquation expXs expBody

      unless eqNormMatches candNorm expNorm do
        throwError
          s!"[semantic_fail] ring_identity_mismatch cand_norm:{eqNormToString candNorm} expected_norm:{eqNormToString expNorm}"

/--
v2 checker for ring identities:
- same normalization as v1
- equation-side symmetry
- invariant to permutations of leading binder indices
-/
def checkRingIdentityNormV2 (cand expected : Expr) : MetaM Unit := do
  forallTelescopeReducing cand fun candXs candBody => do
    forallTelescopeReducing expected fun expXs expBody => do
      if candXs.size != expXs.size then
        throwError "[semantic_fail] ring_binder_arity"

      let candNorm ← normalizeEquation candXs candBody
      let expNorm ← normalizeEquation expXs expBody
      let perms := binderPermutations candXs.size

      let matched :=
        perms.any fun perm =>
          let candRenamed := renameEqNorm candNorm (renameIndexByPerm perm)
          eqNormMatches candRenamed expNorm

      unless matched do
        throwError
          s!"[semantic_fail] ring_identity_mismatch cand_norm:{eqNormToString candNorm} expected_norm:{eqNormToString expNorm}"

/-- Backward-compatible alias used by older callers. -/
def checkRingIdentityNorm (cand expected : Expr) : MetaM Unit :=
  checkRingIdentityNormV1 cand expected

end AutoformalizationEval.Families
