import Lake
open Lake DSL

package BalancedVectors where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib BalancedVectors where
  globs := #[.submodules `BalancedVectors]
