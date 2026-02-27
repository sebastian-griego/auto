import Mathlib
import AutoformalizationEval

set_option autoImplicit false
set_option maxHeartbeats 200000

def cand : Prop :=
  ∀ a b : Bool, ({a} : Set Bool) ∪ ({b} : Set Bool) = ({a} : Set Bool)

def expected : Prop :=
  ∀ a b : Bool, ({a} : Set Bool) ∪ ({b} : Set Bool) = ({b} : Set Bool) ∪ ({a} : Set Bool)

autoform_check "set_equality" "set_equality_norm" "set_equality_norm_v1" 4

def regression_ok : True := True.intro
