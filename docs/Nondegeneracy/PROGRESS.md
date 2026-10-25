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
