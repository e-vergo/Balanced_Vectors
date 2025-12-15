import Lake
open Lake DSL

package PsiIntegrals where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib PsiIntegrals where
  globs := #[.submodules `PsiIntegrals]
