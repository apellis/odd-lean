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
  "38e1e848d07386de5053f85099a947d92afced40"

@[default_target]
lean_lib OddMath where
  globs := #[.andSubmodules `OddMath]
