import Lake
open Lake DSL

package "xmss" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Xmss» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
