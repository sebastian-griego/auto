import Mathlib
import AutoformalizationEval

set_option autoImplicit false
set_option maxHeartbeats 200000

variable (R : Type) [Semiring R]

def cand : Prop :=
  ∀ a b c d : R, (b + c + d) * a = b * a + c * a + d * a

def expected : Prop :=
  ∀ a b c d : R, a * (b + c + d) = a * b + a * c + a * d

autoform_check "ring_identity" "ring_identity_norm" "ring_identity_norm_v2" 0

def regression_ok : True := True.intro
