import Lake
open Lake DSL

package «rng3d» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Rng3d» where
