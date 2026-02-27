import Mathlib
import AutoformalizationEval

set_option autoImplicit false
set_option maxHeartbeats 200000

def cand : Prop :=
  ∀ i j : Fin 8,
    (Set.singleton i ∪ Set.singleton j : Set (Fin 8)) =
      (Set.singleton i ∪ Set.singleton j : Set (Fin 8))

def expected : Prop :=
  ∀ i j : Fin 8,
    (Set.singleton i ∪ Set.singleton j : Set (Fin 8)) =
      (Set.singleton i ∪ Set.singleton j : Set (Fin 8))

autoform_check "set_equality" "set_equality_norm" "set_equality_norm_v1" 64

def regression_ok : True := True.intro
