import Lake
open Lake DSL

package «pb100» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

  -- add any additional package configuration options here


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"



@[default_target]
lean_lib «Pb100» where
  -- add any library configuration options here
