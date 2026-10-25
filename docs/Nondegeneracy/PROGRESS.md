# Odd nondegeneracy research progress

Last checkpoint: 2026-10-25 18:30 UTC. Branch: `research/odd-nondegeneracy`.
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
| Oriented reduction / matching choice | Active | Apply choice isomorphisms to weakly reduced inverse-mate families | Native choiceTransition is a coefficient-space isomorphism; expansion_injective_choice_iff checked | Weak inverse-mate combinatorics and full-SYM closure comparison |
| Oriented reduction / closure | Active | Construct weak-reduced partial-mate matching bridge | Arbitrary-block partial-mate contraction and nested cap–cup closure checked | Native finite sweep, full-SYM transport, and contextual sorting |
| Upward independence / separation | Active | Check cyclotomic quotient consumer; extend to weighted super-coefficients | Full score-controlled PBW straightening checked; native bounded pure-power cyclotomic theorem built | Weighted supertensor extension, actual action and bubble comparison |
| Upward independence / action | Active | Construct distinct-colour bubble-product tests; extend actual inversion | 72×72 mate inverse checked; feedback nonzero and square-zero; normalized bubble acts as nonzero −δ | Full inversion and genuinely multicolour coherence |
| Grassmannian–Webster synthesis | Active | Anchor normalized bubble to native inverse mate, then derive coupled generating series | BK convolution derived on paper; native zero-weight bubble identity compiles | Compatibility of reservoir and probe actions with normalized cups/caps |
| Independent challenge / rewriting | Active | Extend KKO mixed Mackey ideal argument to ELV coefficients | Connected n3/n4 upward relations checked; paper mixed EF extension identified | Multicolour confluence or a useful alternative reduction |

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

- **18:30 UTC:** Commit `3da1842` pushed; full CI [40221226055](https://github.com/apellis/odd-lean/actions/runs/40221226055) running. Next scoped-checked checkpoint: pure-power cyclotomic separation, arbitrary-module tensor coordinate detection (including full `SYM`), weak source-cup matching transport, and exact finite-cutoff kernel. These do not yet construct a full SKM action. Next tasks: right-cap matching transport; polynomial/exterior coefficient structure; actual N=4 categorical bubbles with independent even and odd parameters; odd-height dot translation; even-cutoff twisted Mackey maps.

- **2026-10-25 18:08 UTC**: Native elementary closure and endpoint-list constructions advance the oriented stream. Actual nonzero-exterior inversion and normalized bubble detection advance the action stream. Workers continue on the next missing constructions. New results awaiting integration are scoped checks, not a full-CI claim.

- **2026-10-25 18:11 UTC**: Baseline full CI successful. Integrating the next scoped-checked checkpoint while all streams continue. Connected pilot confirms that surviving exterior coefficients alone do not imply joint PBW detection.

- **2026-10-25 18:24 UTC**: Brief executor disconnection resolved; local files and staging survived. Full CI for [120463b](https://github.com/apellis/odd-lean/actions/runs/40220230892) passed. Native choice equivalence and complete score-controlled PBW straightening are the next integration checkpoint. All streams resumed.
