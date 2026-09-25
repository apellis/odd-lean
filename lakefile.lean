import Lake
open Lake DSL

package OddMath where
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

require StringDiagrams from git
  "https://github.com/apellis/string-diagrams-lean.git" @
  "99a74632364536d189b56d4c8938eb0c80c19f5d"

@[default_target]
lean_lib OddMath where
  globs := #[.andSubmodules `OddMath]
