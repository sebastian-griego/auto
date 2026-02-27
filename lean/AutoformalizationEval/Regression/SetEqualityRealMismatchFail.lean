import Mathlib
import AutoformalizationEval

set_option autoImplicit false
set_option maxHeartbeats 200000

def cand : Prop :=
  ((fun x : Fin 8 => x = 0) : Set (Fin 8)) = ((fun x : Fin 8 => x = 0) : Set (Fin 8))

def expected : Prop :=
  ((fun x : Fin 8 => x = 0) : Set (Fin 8)) = ((fun x : Fin 8 => x = 1) : Set (Fin 8))

autoform_check "set_equality" "set_equality_norm" "set_equality_norm_v1" 8

def regression_ok : True := True.intro
