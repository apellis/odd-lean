# Odd nondegeneracy research progress

Last checkpoint: 2026-10-25 18:04 UTC. Branch: `research/odd-nondegeneracy`.
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
| Oriented reduction / matching choice | Active | Construct endpoint dot lists, signed unit columns, and the native choice transition | Arbitrary reduced-skeleton lower-dot normalization passes scoped Lean and axiom checks | Evaluate the complete signed transition and prove injectivity |
| Oriented reduction / closure | Active | Prove literal right closure of the mixed crossing equals its upward crossing using pitchforks and zigzags | Finite greatest-crossing/least-dot detector passes scoped Lean checks | Native finite sweep, full-SYM transport, and contextual sorting |
| Upward independence / separation | Active | Formalize dot-minus-crossing score filtration and refined straightening | Written bounded cyclotomic separation argument, independently reviewed | Native straightening bound, supertensor coefficient extension, actual action |
| Upward independence / action | Active | Finish nonzero-exterior EF/FE inversion using sparse/block mate calculations | Local relations and adjunction triangles checked; cyclotomic obstruction kernel-checked | Full inversion and genuinely multicolour coherence |
| Grassmannian–Webster synthesis | Active | Derive coupled bubble generating series and a triangular coefficient map | Squared-dot/Clifford proposal and exact restrictions documented | Compatibility of reservoir and probe actions with normalized cups/caps |
| Independent challenge / rewriting | Active | Adversarial two-colour quotient tests and a concrete multicolour critical overlap | Exact Clifford/exterior spectral tests pass | Multicolour confluence or a useful alternative reduction |

## Verification

- Baseline scoped Lean checks and concrete consumers passed, with allowed axioms only.
- [Full branch CI for 0edcf48](https://github.com/apellis/odd-lean/actions/runs/40218574038)
  was still running at this checkpoint. No successful full-CI claim yet.
- Neither upward SKM independence nor its full oriented consequence is proved.

## Checkpoint log

- **18:04 UTC:** Sustained parallel work resumed with six active workers. New
  assignments target the missing constructions directly. Prior proposals and
  partial results are preserved in the linked topic notes and baseline commit.

See [HANDOFF.md](HANDOFF.md) for exact restart state and file ownership.
