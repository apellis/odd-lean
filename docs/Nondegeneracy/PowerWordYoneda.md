# Enriched Hom chart for the actual regular-power word modules

Status: strict producer and occupied paired-consumer checks passed; all owned
declarations use only standard axioms. Full-library CI is a separate gate.

`ELVPowerWordYoneda.lean` constructs the enriched Yoneda equivalence for
`powerWordModule D Sc cutoff L ν` against every actual
`CoefficientPowerModules` object. Its inverse is the full-parity formula

    h ↦ M(twist_p h)(proj_p m).

The formula descends through the proved `powerWordGenerator_ker`: every
coefficient in the literal two-sided power ideal acts by zero on the target.
No flatness premise or replacement coefficient quotient is introduced. The
result includes the enriched transformation, both evaluation round trips,
the linear Hom equivalence, and compatibility with both parity projections.

On an arbitrary coend vector `h ⊗ [a]`, the formula is

    M(twist_p(eν(a) ≫ h))(proj_p m).

Both the old arrow and the exterior coefficient are inside the twist. The
paired consumer uses the actual empty regular A/T vacuum, with two distinct
odd exterior colours. For odd m and odd a, even when h is the identity, the
chart has the extra minus sign. The product survives the coefficient power
quotient and the old-category extension, so this test is occupied.

This is the Hom chart for the actual word modules. Identifying the native
signed word maps with the selected iterated induction dots and crossings,
and then assembling the swapped action and normalized bubble comparisons,
remain separate work. The Hom chart alone does not assert action faithfulness
or odd nondegeneracy.
