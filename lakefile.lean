import Lake
open Lake DSL

package OddMath where
  -- Preserve the elaborator's pre-4.34 implicit-argument unfolding; kernel checking is unchanged.
  moreLeanArgs := #["-DwarningAsError=true", "-Dbackward.isDefEq.respectTransparency=false",
    "-Dbackward.isDefEq.respectTransparency.types=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.34.1"

require StringDiagrams from git
  "https://github.com/apellis/string-diagrams-lean.git" @
  "fb96f497c0dd0a24ed941d3a2c25b4cbfe63d884"

require DG from git
  "https://github.com/apellis/dg-lean.git" @
  "23a7a0893e31ec1f371bf727a0532394d5b9b397"

@[default_target]
lean_lib OddMath where
  globs := #[.andSubmodules `OddMath]
