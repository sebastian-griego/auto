import Lake
open Lake DSL

package "autoformalization-eval" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

@[default_target]
lean_lib AutoformalizationEval where
