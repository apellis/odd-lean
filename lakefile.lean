import Lake
open Lake DSL

package OddMath where
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"

require StringDiagrams from git
  "https://github.com/apellis/string-diagrams-lean.git" @
  "6627eeca272cab80273b9641174d13976b518578"

@[default_target]
lean_lib OddMath where
  globs := #[.andSubmodules `OddMath]
