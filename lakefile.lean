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
  "f4855a2731720992334b4bb3504e736ad0dcbb23"

require DG from git
  "https://github.com/apellis/dg-lean.git" @
  "fe2d53ab78fc1aa776069ebb8834882e37997c5c"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "32bd12d86ac3e02ae5703812699d36fb7285583e"

@[default_target]
lean_lib OddMath where
  globs := #[.andSubmodules `OddMath]
