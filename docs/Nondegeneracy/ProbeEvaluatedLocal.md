# The local Rouquier record on evaluated probes

Brundan–Ellis (1.7)–(1.8) and (1.13)–(1.14) require the local relations for
the chosen induction, restriction, dot and crossing maps. The declaration
`probeEvaluatedLoc` in `ELVProbeEvaluatedLocal` restricts `oldContentLoc` to
the full subcategories of old modules whose coefficients evaluate to the
chosen probe polynomials.

The adjunction is `probeEvaluatedRightAdjunction`, the dots are
`probeEvaluatedInductionDot`, and the crossing is `probeEvaluatedEqualCross`.
The crossing retains the old negative convention. The local height is
`-contentCrossingHeight D (probeCutoff D m) i (i :: ν)`; all dot powers remain
ordered powers of the selected dots. No inverse or local-relation premise
is supplied to the constructor.

The proof restricts homogeneous natural transformations along full
subcategory inclusions. Restriction preserves composition, addition,
integer scalar multiplication and finite sums. Consequently the old slide
relations and finite inverse identities restrict without changing any map.
The mate, unit rows and counit rows coincide componentwise with the
restrictions of their old counterparts. This comparison uses the selected
ordinary adjunctions, including their units and counits.

The four declarations `probeEvaluatedLoc_invPos_f'_app`,
`probeEvaluatedLoc_invPos_g'_app`, `probeEvaluatedLoc_invNeg_f'_app` and
`probeEvaluatedLoc_invNeg_g'_app` identify each homogeneous component of the
selected inverse entries with its old component. These equalities hold for
all row indices, including indices outside the finite inverse sum. The
inverse data are restricted directly rather than replaced by a new choice
or a zero extension.

The paired consumer uses the two-colour rational fixture, including both
parities, positive and negative heights, the zero-height overlap, and an
off-diagonal finite matrix identity. It evaluates the inverse-component
comparisons on scalar-evaluated regular-module probes. This is the local
record on evaluated content categories; transport to arbitrary canonical
representatives of weights requires the induction–reindex generator
comparisons.

The exact producer and paired consumer pass strict checks with warnings
as errors and both compatibility settings; all 182 owned declarations
pass the standard axiom allowlist. Full integration remains separate.
