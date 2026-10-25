<!-- LIVE-STATUS-START -->
# Live research status

Updated 2026-10-25 19:43 UTC. Branch: `research/odd-nondegeneracy`.
Latest pushed checkpoint: `4a9ef53`; [full CI](https://github.com/apellis/odd-lean/actions/runs/40226825974) passed (build, axiom audit, non-vacuity).
Last fully green checkpoint: `4a9ef53`. The earlier umbrella name collision is fixed.

| Stream | Checked result | Current task | Workers |
|---|---|---|---|
| Upward → oriented | Full-SYM sorted-boundary implication; actual distinct-colour target descent; global induction with explicit local hypotheses | Same-colour paired comparison and source exchange, with actual adapted serializers | sorting, rewriting, Webster |
| Upward independence | Explicit ELV quotient separation; canonical PBW/matching bridge; fixed-weight finite observations imply full upward independence | Construct bounded coefficient recovery with nilpotent coefficient truncation | separation |
| Actions / synthesis | Actual 80×80 fixed-weight coupling; local norm identities; proposed connected action audit | Direct zero/nonzero superdatum coupling: vacuum Frobenius signs and excited-probe Schur/bubble formulas | action, choice |

**Still open:** construction of the fixed-weight observations, and completion of arbitrary-boundary local exchange. No full nondegeneracy theorem is claimed. Scoped-checked results after the pushed checkpoint await integration/full CI. Six workers remain active; completed assignments are immediately replaced.

Persistent restart details: [HANDOFF.md](HANDOFF.md). Earlier checkpoint history follows.
<!-- LIVE-STATUS-END -->

# Odd nondegeneracy research progress

Last checkpoint: 2026-10-25 18:54 UTC. Branch: `research/odd-nondegeneracy`.
Research baseline: `0edcf48`. This board records checkpoints, not live telemetry.

## Objective and operating rules

Prove the Brundan–Ellis §8 odd/mixed Nondegeneracy Conjecture, keeping its
parameter and coefficient scope explicit. Maintain the three principal streams
below. Completed assignments trigger review and the next substantive assignment.
Keep all exploratory work on this research branch. No PRs against master;
selection and cleanup are a later stage. A written argument is not a formally
proved result. Every status must distinguish experiments, written proofs,
scoped Lean checks, and full CI verification.

## Active work

| Stream / worker | State | Current concrete target | Latest established input | Main unresolved obligation |
| --- | --- | --- | --- | --- |
| Oriented reduction / matching choice | Active | Right-cap attachment, final pairing and weak reducedness | Native arbitrary-choice coefficient isomorphism and independence equivalence | Full weak inverse-mate label bijection |
| Oriented reduction / closure | Active | Full coefficient compatibility of source-prefix bending | Literal partial-mate contraction and source-cup matching/dot transport checked | Full-SYM closure comparison and contextual sorting |
| Upward independence / separation | Active | Full bubble polynomial/exterior presentation and grading | Native pure-power quotient and arbitrary-module tensor detection checked | Weighted deformed ideal and actual categorical realization |
| Upward independence / action | Active | Extend N=4 even/odd parameter action beyond vacuum | Actual72×72 inversion; N=4 vacuum detects δ, ε and δε | All-rank connected tower and full inversion |
| Grassmannian–Webster synthesis | Active | Multicolour translated action at odd heights | Native shifted inverse coordinates and conditional bubble shift checked | Full translated presentation; even heights need reservoir deformation |
| Independent challenge / rewriting | Active | Twisted KKO maps and monic projectivity argument | Mixed EF paper extension; even-cutoff normality exact sequence; first connected map test | All-beta same-colour projectivity and inversion |

## Verification

- Full CI [40222091681](https://github.com/apellis/odd-lean/actions/runs/40222091681)
  passed for `c8debb4`. `8b5b2cc` is pushed; CI40222830590 running.
- **18:54 UTC:** Whole-word full-coefficient transport and actual partial-mate
  closure expansion are scoped Lean-checked. The signed coefficient-extended
  QH category is constructed with genuine tensor Homs. All-content even-cutoff
  projectivity has a written source-adaptation proof under review; Section 9
  inversion is still being audited. One worker moved from that audit to the
  cyclic pairing-coverage lemma; six workers remain active across all streams.

- Full CI [40221653309](https://github.com/apellis/odd-lean/actions/runs/40221653309)
  passed for `cd0ba81`. Checkpoint `c8debb4` is pushed; full CI
  [40222091681](https://github.com/apellis/odd-lean/actions/runs/40222091681) running.
- **18:45 UTC:** Full-SYM one-strand transport with prescribed constant
  coefficient and finite positive-dot errors is scoped Lean-checked.
  Coefficient basis, multiplicative weight filtration and bounded injection
  into its actual ring quotient are checked. Workers continue on whole-word
  transport, signed categorical coefficient extension, and connected action.
  Both actual odd bubble composites at the first connected object have a
  nonzero product in the exact finite pilot; this is not a full action.

- Full CI [40221226055](https://github.com/apellis/odd-lean/actions/runs/40221226055)
  passed for `3da1842`. Next pushed checkpoint `cd0ba81` is running full CI
  [40221653309](https://github.com/apellis/odd-lean/actions/runs/40221653309).
- **18:35 UTC:** Source-prefix bending now commutes with all closed coefficients;
  abstract SYM is identified with polynomial tensor exterior algebra. Both are
  scoped Lean-checked. Rank-one deformed action is already supplied by
  Ebert–Lauda–Vera Th4.5; ongoing action work targets its connected extension
  and fixed-weight detection. Exact vacuum test retains both even and odd
  parameters and their product. First connected inversion corner passes.

- Baseline scoped Lean checks and concrete consumers passed, with allowed axioms only.
- [Full branch CI for 0edcf48](https://github.com/apellis/odd-lean/actions/runs/40218574038)
  completed successfully: Build, Axiom audit, and non-vacuity checks passed. New work below has scoped checks until its separate full CI completes.
- Neither upward SKM independence nor its full oriented consequence is proved.

## Checkpoint log

- **18:04 UTC:** Sustained parallel work resumed with six active workers. New
  assignments target the missing constructions directly. Prior proposals and
  partial results are preserved in the linked topic notes and baseline commit.

See [HANDOFF.md](HANDOFF.md) for exact restart state and file ownership.

- **18:30 UTC:** Commit `3da1842` pushed; full CI [40221226055](https://github.com/apellis/odd-lean/actions/runs/40221226055) running. Next scoped-checked checkpoint: pure-power cyclotomic separation, arbitrary-module tensor coordinate detection (including full `SYM`), weak source-cup matching transport, and exact finite-cutoff kernel. These do not yet construct a full SKM action. Next tasks: right-cap matching transport; polynomial/exterior coefficient structure; actual N=4 categorical bubbles with independent even and odd parameters; odd-height dot translation; even-cutoff twisted Mackey maps.

- **2026-10-25 18:08 UTC**: Native elementary closure and endpoint-list constructions advance the oriented stream. Actual nonzero-exterior inversion and normalized bubble detection advance the action stream. Workers continue on the next missing constructions. New results awaiting integration are scoped checks, not a full-CI claim.

- **2026-10-25 18:11 UTC**: Baseline full CI successful. Integrating the next scoped-checked checkpoint while all streams continue. Connected pilot confirms that surviving exterior coefficients alone do not imply joint PBW detection.

- **2026-10-25 18:24 UTC**: Brief executor disconnection resolved; local files and staging survived. Full CI for [120463b](https://github.com/apellis/odd-lean/actions/runs/40220230892) passed. Native choice equivalence and complete score-controlled PBW straightening are the next integration checkpoint. All streams resumed.


## Latest execution checkpoint

The workspace executor disconnected after the 19:01 UTC update. Local builds
and edits are paused; all six streams retain their assignments and source review
continues. Last pushed code is `901938c`. New weighted signed quotient separation,
weak-to-strict transfer, cyclic pairing coverage, and positive-dot detector results
passed scoped checks and are staged locally, not yet part of that commit.
The proposed connected-action manuscript remains a written argument under review.
See the recovery section of [HANDOFF.md](HANDOFF.md) for exact checked/unchecked
files and restart commands. This board update was saved directly through GitHub.

The connection subsequently returned. Recovery commit `4b16af0` was fetched and
fast-forwarded without losing staged work. All workers resumed their exact
pending checks. CI40222830590 passed for `8b5b2cc`; CI40223506675 for `901938c`
is still running. New weighted signed ideal separation and weak-family transfer
checkpoints are now being integrated; the connected-action theorem remains
labelled proposed, not a native theorem or a solution of nondegeneracy.


## Integrated continuation checkpoint

CI for `901938c` passed; `15ad5c1` is running separately. The executor is
available and all six workers continue. No full nondegeneracy theorem is claimed.

- Oriented: full-SYM parity placement equivalence, canonical positive-dot
  coefficient lift, weak mate coverage and literal layers are scoped checked.
  Choice assembles sorted independence; sorting audits its hypotheses and then
  owns contextual assembly; rewriting supplies list-boundary wrappers; Webster
  proves actual local paired-sector pivots and recurrences.
- Upward: weighted signed quotient detection is integrated. Explicit ELV
  coefficient specialization and its generated quotient bounds are next.
  These results concern affine coefficient-extended quotients, not yet an SKM action.
- Synthesis: the actual 80 by 80 fixed-weight reservoir/probe mate passes,
  retaining odd and even coefficient products. General weighted spectral folding
  and the proposed connected action still require categorical justification.

Next review checkpoint: sorted theorem hypotheses, all-weight paired sorting,
ELV quotient consumers, and reproducible fixed-weight coupling computation.
All work remains on `research/odd-nondegeneracy`; no master PR.

Explicit all-colour ELV coefficient relations and colour-correct first-dot
polynomials now have scoped-checked bounded quotient separation. Even uniform
cutoffs jointly detect every affine SYM-coefficient morphism. Next: an explicit
conditional categorical evaluation interface, keeping the missing SKM action
and bubble identification visible.


## Sorted-boundary milestone

`WeakMate.sorted_independence` now builds: full upward matching-expansion
independence implies every sorted oriented matching family is independent, at
every prescribed external weight, over full SYM. The top serializer, ordinary
layers, weak mate coverage, closure correction and coefficient parity premises
are all discharged. Independent assumption audit found no additional action,
field, finite-colour or bubble-faithfulness hypothesis. This is not yet the
full arbitrary-boundary implication.

The remaining oriented work is actual local exchange descent. Global boundary
induction is checked conditionally; paired crossing expansions are checked;
workers are constructing contextual adapted families and their coefficient maps.

`UpwardCoefficientDetection` isolates finite observations at fixed weight as a
sufficient condition for the actual affine coefficient evaluation to be injective.
Neither these observations nor its PBW-to-matching comparison is yet constructed.
The latter is now the separation worker's task.

The 80 by 80 fixed-weight coupling script was independently reproduced. The
general synthesis still needs actual categorical coupling and bubble recovery.
We are also testing a simpler route using two original-superdatum cyclotomic
actions with disjoint zero/nonzero spectra, before committing to a weighted
Clifford-to-even cover construction.

CI for `15ad5c1` passed; `67c4365` is running. Research branch only.


### Integration and continued assignments

CI `40225381594` for `67c4365` caught an umbrella-only name collision:
new `QuiverHecke.cl_nil` duplicated the declaration in `Centre`. Renamed the
new helper `coefficient_cl_nil`; the full local build is running. Scoped
checks, including the sorted theorem's populated consumer and standard axiom
audit, pass. The next commit is a checked local checkpoint awaiting full CI.

Worker allocation now: choice + separation construct the canonical affine
PBW/matching evaluation bridge; sorting + rewriting + Webster assemble actual
contextual source/target exchange; action develops the direct disjoint-spectrum
coupling. All six continue. The original all-content action remains a proposed
manuscript. The direct coupling has a symbolic Frobenius-pairing argument at
the highest probe vacuum; general coupled inversion remains under investigation.
