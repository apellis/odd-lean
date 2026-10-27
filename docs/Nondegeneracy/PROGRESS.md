# Odd nondegeneracy: status board

Branch `research/odd-nondegeneracy`. Restart state, open obligations and next targets:
[HANDOFF.md](HANDOFF.md). Every push to this branch runs the full CI build (build, axiom
audit, non-vacuity); the branch tip is expected to be green.

| Line of work | Lean on this branch | Open |
| --- | --- | --- |
| Finite contextual colour witness, SwappedNondegeneracy §5 | `SKM.mem_finiteColourIdeal`, `SKM.eq_finiteColourIdeal`; an empty-boundary inverse cup/cap relation consumer | finite-subtype restriction preserving X, roots, coroots and scalars; finite-colour detection and nondegeneracy |
| Reservoir principal word, `HomPrincipalMate.md` §3 | `RouquierFamily.leftCrossingWord_eq`: unnormalized word at every height, coefficient one at zero; `principalWord_scalar`: gamma(0)=(-1)^p | specified shifted Hom mate substitution and shift removal (10); full principal comparison, augmented inversion, fusion |
| Upward → oriented reduction | assembly `SKM.nondegeneracy_of_contextual_descent`; sorted boundaries `WeakMate.sorted_independence`; choice independence `expansion_injective_choice_iff`; distinct-colour target descent `SKM.distinct_target_exchange_descent`; distinct-colour source adapted families; complete same-colour target choices `exists_same_colour_adapted_equiv` | source exchange descent; same-colour target and source descent |
| Upward independence | conditional consumers `upward_independence_of_finite_observations`, `upward_independence_of_spectators`; spectator evaluation interface; fixed-spectator cofinal ELV separation and weighted signed quotient detection | action-derived product law and joint detection; fixed-weight separation with moving spectator strands |
| Deformed actions | local norm, translation and Frobenius resolvent identities; cyclotomic exterior obstruction | multicolour action (proposed for even cutoffs), odd heights, fixed-weight bubble images; coupling for weights not reached by dominant vacua |

Full nondegeneracy for odd or mixed data is not proved. Python scripts in
`scripts/Nondegeneracy/` are finite models of particular instances.

Earlier checkpoint history is in the git history of this file.
