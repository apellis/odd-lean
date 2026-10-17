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
  "9976974dfbce9c140f20c41467abbe44a4a0e294"

require DG from git
  "https://github.com/apellis/dg-lean.git" @
  "df94a62562df5d82029d2832f6e9a5d42e078b67"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "9666a66184264251e73d604223db1c934820845a"

@[default_target]
lean_lib OddMath where
  globs := #[.andSubmodules `OddMath]
