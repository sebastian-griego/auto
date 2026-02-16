import Lean

open Lean Meta

namespace AutoformalizationEval.Families

/-- Tier B placeholder checker. -/
def checkSetEquality (cand expected : Expr) : MetaM Unit := do
  if (← isDefEq cand expected) then
    pure ()
  else
    throwError "[semantic_fail] set_equality_mismatch"

end AutoformalizationEval.Families
