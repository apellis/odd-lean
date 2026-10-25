# Odd nondegeneracy: status board

Branch `research/odd-nondegeneracy`. Restart state, open obligations and next targets:
[HANDOFF.md](HANDOFF.md). Every push to this branch runs the full CI build (build, axiom
audit, non-vacuity); the branch tip is expected to be green.

| Line of work | Lean on this branch | Open |
| --- | --- | --- |
| Upward → oriented reduction | assembly `SKM.nondegeneracy_of_contextual_descent`; sorted boundaries `WeakMate.sorted_independence`; choice independence `expansion_injective_choice_iff`; distinct-colour target descent `SKM.distinct_target_exchange_descent`; distinct-colour source adapted families; complete same-colour target choices `exists_same_colour_adapted_equiv` | source exchange descent; same-colour target and source descent |
| Upward independence | conditional consumers `upward_independence_of_finite_observations`, `upward_independence_of_spectators`; spectator evaluation interface; multicolour ELV and weighted signed quotient detection | action-derived product law and joint detection; fixed-weight separation with moving spectator strands |
| Deformed actions | local norm, translation and Frobenius resolvent identities; cyclotomic exterior obstruction | multicolour action (proposed for even cutoffs), odd heights, fixed-weight bubble images; coupling for weights not reached by dominant vacua |

Full nondegeneracy for odd or mixed data is not proved. Python scripts in
`scripts/Nondegeneracy/` are finite models of particular instances.

Earlier checkpoint history is in the git history of this file.
