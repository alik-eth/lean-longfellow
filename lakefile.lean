import Lake
open Lake DSL

package «lean-longfellow» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib LeanLongfellow where
  roots := #[`LeanLongfellow]
