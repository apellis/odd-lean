# Development notes

## Lean 4.34.1 toolchain and verification

Keep the checked-in pins together:

- toolchain `leanprover/lean4:v4.34.1`;
- Mathlib `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612`;
- StringDiagrams `fb96f497c0dd0a24ed941d3a2c25b4cbfe63d884`.

Use the existing `lake-manifest.json`; do not run `lake update` just to build, and do not edit
shared dependency checkouts. `lakefile.lean` retains warnings as errors and the two
`backward.isDefEq.respectTransparency` compatibility options. These affect elaboration,
not the kernel or axiom policy. Do not disable linters to hide migration failures.

```sh
lake --wfail build
lake env lean -DwarningAsError=true scripts/AxiomAudit.lean
```

For isolated source checks, pass both compatibility settings explicitly because `lake env lean`
does not apply the package build arguments:

```sh
lake env lean -DwarningAsError=true \
  -Dbackward.isDefEq.respectTransparency=false \
  -Dbackward.isDefEq.respectTransparency.types=false OddMath/Frontier/FILE.lean
```

No `sorry`, `admit`, added axioms, or `native_decide`. Keep theorem statements and proof coverage
intact. `scripts/AxiomAudit.lean` checks every imported `OddMath` declaration against the
allowlist `propext`, `Classical.choice`, `Quot.sound`; a failed build is not a successful audit.

## Shared build storage

Sources, lockfiles, and `.verification/*.log` are durable. `.lake/build` is regenerable output;
`.lake/packages` may point to shared dependencies and must not be swept. Reuse the installed
toolchain/cache rather than allocating another Mathlib build (`lake exe cache get`). On a
machine shared with other builds, serialize full builds (e.g. with `flock
.verification/build.lock`), limit parallelism with `LEAN_NUM_THREADS`, and run `lake` with
stdin redirected from `/dev/null`. Machine-specific disk and scheduling tooling belongs in
private configuration, not in this repository.
