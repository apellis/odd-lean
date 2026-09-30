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
toolchain/cache rather than allocating another Mathlib build. On the shared formalization host,
serialize builds and reserve headroom:

```sh
mkdir -p .verification
flock .verification/build.lock \
  python3 /home/hermes/.hermes/scripts/disk_lifecycle.py run \
    --path "$PWD" --project odd-core-upgrade --reserve-gib 2 -- \
    env PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2 lake --wfail build < /dev/null
```

Do not bypass a reservation refusal. Retirement uses the host maintenance command
`python3 /home/hermes/.hermes/scripts/disk_lifecycle_maintenance.py --apply`; only its explicitly
classified inactive rebuild outputs may be removed. Preserve sources, evidence, shared targets,
and active builds.
