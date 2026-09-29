# Notes for Claude Code sessions

## Pending: port to Lean v4.34.1 (remove this section once done)

Target pins (`lean-toolchain`, `lakefile.lean`), matching the other `*-lean` repos:

- toolchain `leanprover/lean4:v4.34.1`
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`)
- StringDiagrams `fb96f497c0dd0a24ed941d3a2c25b4cbfe63d884` (string-diagrams-lean `main`, already on
  v4.34.1 with the same mathlib; or any later `main` commit). The library imports only
  `StringDiagrams.{Derivation, Generation, Grading, Interpretation}`.

Then run `lake update` to regenerate `lake-manifest.json`, build, and fix what breaks. Keep
`-DwarningAsError=true` and the README's no-`sorry`/no-added-axioms guarantee. Update the toolchain
line in the README as string-diagrams-lean did.

Order across repos: string-diagrams-lean first (done), then odd-lean and categorification-lean
(both depend on it). dg-lean and lie-lean are independent.

Cloud-session setup notes (as of 2026-09-27): `release.lean-lang.org` is blocked by the egress proxy,
so `elan-init.sh` cannot fetch toolchains. What worked: download
`https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst` with
`curl -sSfL -C -` in a retry loop (transfers drop mid-stream), extract with `tar --zstd`, install elan
from its GitHub release with `--default-toolchain none`, then
`elan toolchain link leanprover/lean4:v4.34.1 <dir>`. `lake update` and `lake exe cache get` were
not yet tried there.
