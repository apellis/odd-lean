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
  "8ae261b120e748db9f79fa3179028fa5617c996f"

require DG from git
  "https://github.com/apellis/dg-lean.git" @
  "161db4ede65f2dd359263a301c33ec39036988eb"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "29042522f511a969b7f6dbc81d3c8a8bebfef818"

require Categorification from git
  "https://github.com/apellis/categorification-lean.git" @
  "ee5a0b65a60c4d11193be85e412af544a2592867"

@[default_target]
lean_lib OddMath where
  globs := #[.andSubmodules `OddMath]
