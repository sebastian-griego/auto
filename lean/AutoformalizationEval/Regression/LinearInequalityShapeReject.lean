import Mathlib
import AutoformalizationEval

set_option autoImplicit false
set_option maxHeartbeats 200000

def cand : Prop :=
  ∀ x y : Int, x + y = 7

def expected : Prop :=
  ∀ x y : Int, x + y + y <= 7

autoform_check "linear_inequality" "linear_inequality_norm" "linear_inequality_norm_v1" 0

def regression_ok : True := True.intro
