# Contributor guide

This repository is developed largely by AI agents under human direction. Everything here is
public: keep it mathematical and technical.

## Lean 4.34.1 toolchain and verification

Keep the checked-in pins together: the toolchain in `lean-toolchain` (`leanprover/lean4:v4.34.1`)
and the package revisions in `lake-manifest.json` (Mathlib `v4.34.1`, commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, plus StringDiagrams, DG and LieLean).

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

Sources and lockfiles are durable. Local logs (for example `.verification/*.log`) are untracked
scratch: do not commit them. `.lake/build` is regenerable output;
`.lake/packages` may point to shared dependencies and must not be swept. Reuse the installed
toolchain/cache rather than allocating another Mathlib build (`lake exe cache get`). On a
machine shared with other builds, serialize full builds (e.g. with `flock
.verification/build.lock`), limit parallelism with `LEAN_NUM_THREADS`, and run `lake` with
stdin redirected from `/dev/null`. Machine-specific disk and scheduling tooling belongs in
private configuration, not in this repository.

## Layout

New modules go in a topical directory (`OddMath/SKM/`, `OddMath/CoveringQuantum/`, ...), with a
module docstring naming the source results they formalize. Do not add new top-level files to
`OddMath/` or new files to `OddMath/Frontier/`.

## Staying on course

These rules apply to every contributor and take precedence over local habits or private
instructions that conflict with them.

**Targets and scope**

- Every PR advances a specific numbered result of a cited source (theorem, proposition,
  corollary, lemma, definition or equation) or a roadmap item that one of them needs. The PR
  title or body names it. Supporting lemmas land with, or shortly before, the result that uses
  them.
- Formalize what the source states. Do not label results "original", and do not develop new
  theory when a source step is missing. When a cited proof relies on a reference that is not
  available, on a step that has a gap, or on a result outside the library, stop and record this
  in the tracking issue as a question for the maintainer. The options are: (a) obtain the
  reference; (b) take the missing input as an explicit, documented hypothesis of the dependent
  results; (c) build a replacement route. Do not start (c) without the maintainer's approval.
- Scope decisions are the maintainer's. These include declaring a numbered result out of scope,
  choosing between several valid conventions, and substituting a different object for the one
  the source uses (for example a crystal basis for a canonical basis). List them as open
  questions; do not decide them silently.
- Prove one form of a result. Restate it in another form (maps → bimodule maps → natural
  isomorphisms → mates, and so on) only when a named downstream result needs that form.

**Statements**

- A headline statement carries exactly the source's hypotheses, after any recorded erratum
  correction.
- An extra hypothesis that the current proof route needs is allowed only on an intermediate
  statement. Its docstring must say so, the README status must say so, and a roadmap item must
  track its removal.
- Names, docstrings and status tables never overstate. Do not use `_unconditional` on a
  conditional theorem, and do not use "full" or "complete" for a statement that assumes part of
  its conclusion.
- An erratum entry gives the printed statement, the corrected statement with the extra
  hypothesis or correction, the declarations, and a short paragraph that can be sent to the
  authors as is.

**Lean engineering**

- Elaboration trouble is not a mathematical obstruction. Examples: `whnf` or `isDefEq` timeouts
  on dependent transports, heartbeat limits, motive errors, slow instance search.
- After two failed attempts at the same proof, redesign the encoding. Possible changes: reindex
  so that the types agree definitionally, prove one generic lemma instead of many instances, or
  avoid nested casts. Do not raise `maxHeartbeats` or retry with a larger budget.
- Names of declarations, modules and PRs describe the mathematics. Avoid process adjectives
  ("actual", "genuine", "original", "native", "fixed", "frontier"), stage labels (`LegA`,
  `AdapterB7`, `PbwL3`) and "WIP". A PR whose title says WIP is not merged.

**Workflow and evidence**

- All proof work happens on topic branches of this repository and lands through PRs with green
  CI. Work that does not build yet may be pushed as a draft PR. Proof developments are not kept
  in private copies, scratch archives or other repositories.
- The evidence that a result is done is CI: full build with warnings as errors, plus the axiom
  audit. Agreement between reviewers, private sign-offs, hash manifests and log archives are not
  evidence. Do not commit logs, manifests, archives or review packets.
- The same PR updates the README/ROADMAP status row and the tracking issue. Close an issue when
  its goal is met.
