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
  "4540cd4a47cf0c4d8ef7597cdc8a5fa95c84a11f"

require DG from git
  "https://github.com/apellis/dg-lean.git" @
  "fe555b543a8a4ab084a6eafef9159dda8339d2fd"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "84222f8a9861e73db9778092c6a9d51ff39315cb"

@[default_target]
lean_lib OddMath where
  globs := #[.andSubmodules `OddMath]
