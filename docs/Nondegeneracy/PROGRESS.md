# Odd nondegeneracy research progress

Last checkpoint: 2026-10-25 18:11 UTC. Branch: `research/odd-nondegeneracy`.
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
| Oriented reduction / matching choice | Active | Extend signed columns coefficient-linearly and prove transition injectivity | Actual arbitrary-choice signed unit-column comparison passes scoped Lean checks | Evaluate the complete signed transition and prove injectivity |
| Oriented reduction / closure | Active | Generalize cap–cup closure to arbitrary nested strand blocks | Mixed-crossing, decorated cap–cup and signed downward-dot closure lemmas pass scoped Lean checks | Native finite sweep, full-SYM transport, and contextual sorting |
| Upward independence / separation | Active | Refine dot-down and normal-form induction with joint score/crossing filtration | Native weighted braid equivalence and contextual correction bounds pass scoped checks | Native straightening bound, supertensor coefficient extension, actual action |
| Upward independence / action | Active | Construct distinct-colour bubble-product tests; extend actual inversion | 72×72 mate inverse checked; feedback nonzero and square-zero; normalized bubble acts as nonzero −δ | Full inversion and genuinely multicolour coherence |
| Grassmannian–Webster synthesis | Active | Anchor normalized bubble to native inverse mate, then derive coupled generating series | BK convolution derived on paper; native zero-weight bubble identity compiles | Compatibility of reservoir and probe actions with normalized cups/caps |
| Independent challenge / rewriting | Active | Connected iji braid; distinguish low-cutoff annihilators from general obstruction | Connected two-colour transport/quadratic pilot passes; tiny cutoff kills reverse-crossing·δiδj | Multicolour confluence or a useful alternative reduction |

## Verification

- Baseline scoped Lean checks and concrete consumers passed, with allowed axioms only.
- [Full branch CI for 0edcf48](https://github.com/apellis/odd-lean/actions/runs/40218574038)
  completed successfully: Build, Axiom audit, and non-vacuity checks passed. New work below has scoped checks until its separate full CI completes.
- Neither upward SKM independence nor its full oriented consequence is proved.

## Checkpoint log

- **18:04 UTC:** Sustained parallel work resumed with six active workers. New
  assignments target the missing constructions directly. Prior proposals and
  partial results are preserved in the linked topic notes and baseline commit.

See [HANDOFF.md](HANDOFF.md) for exact restart state and file ownership.

- **2026-10-25 18:08 UTC**: Native elementary closure and endpoint-list constructions advance the oriented stream. Actual nonzero-exterior inversion and normalized bubble detection advance the action stream. Workers continue on the next missing constructions. New results awaiting integration are scoped checks, not a full-CI claim.

- **2026-10-25 18:11 UTC**: Baseline full CI successful. Integrating the next scoped-checked checkpoint while all streams continue. Connected pilot confirms that surviving exterior coefficients alone do not imply joint PBW detection.
