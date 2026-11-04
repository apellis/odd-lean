# Padded reservoir contractions in the output coefficient ideal

SwappedHomInversion §4, equations (7)–(9), requires the chosen reservoir
principal closures and finite-window contractions in condition (J).
`Sigma/ReservoirWindowCoefficientIdeal.lean` attaches the source coefficient
ideal theorems to the named entries of `ReservoirWindowInverseData`.

`SupportedSectors.reservoirOutputEval` is the literal
`RegularReservoir.evalHomFunctor`: it fixes only the output content and
retains the complete functor from the probe weight category. Its morphism
map is output whiskering by `elvBlockEval`. Its zero object is the
constant actual zero module from `ELVContentHomZero`; no extra zero-object
hypothesis is required. The coefficient ideal uses
`contentModuleCoefficientIdeal` on this functor category, with the
parameter-twisted homogeneous scalars. Its zeroth level contains every
morphism; there is no grading premise on arbitrary Hom morphisms.

The two `_closure_eq` equations cancel the occupied padded charts and
identify the named principal closure with the native postcomposition
closure. The `_closure_mem` theorems apply the corresponding positive or
negative `ReservoirClosures` source ideal API. At an absent source, each
principal maps into the padded zero corner and its closure is zero.
`_negPrincipal_closure_mem` retains membership for the negative central
principal convention.

The two occupied `_boundary_eq` equations perform the same cancellation
for finite inverse entries. The absent cap column is zero. The absent
unit row instead uses `_boundary_eq_of_absent`, with native predecessor
`P.muM t - D.α i`; it is not replaced by zero. For every finite slot `j`
and row `r > j`, `_boundary_mem` applies the appropriate
`ReservoirBoundaries` source ideal API. The `_contraction_mem` theorems
use each named record's `isInverse` for rows inside its window and the
boundary theorem outside it. Thus every row differs from its Kronecker
pairing by a level-one coefficient. The finite entries of `negPrincipal`
are definitionally the same, so these contraction statements apply to
that convention as well.

The paired consumer is
`scripts/NonVacuity/ReservoirWindowCoefficientIdeal.lean`. It retains the
two-odd-colour rational datum with Cartan matrix `[[2,-2],[-2,2]]`, the
nonzero tensor Hom, and the colliding original-weight block. It exercises
both height signs, occupied and absent source branches, both principal
signs, arbitrary off-window rows, and all-row contractions. Its absent
unit window entry is proved nonzero: its finite diagonal contraction is
identity on the proved nonzero output functor. No inverse equation or
coefficient membership is supplied as a consumer premise.

These statements supply the reservoir coefficient inputs to residual
comparison. They do not supply the mixed-bend expansion, probe window
inverse, or final central augmented inverse.

The producer and paired consumer pass strict scoped checks with the pinned
toolchain, warnings as errors and both compatibility settings. The consumer
audits all 32 declarations owned by this attachment, all seven canonical
zero-object declarations, all fifteen closure-ideal declarations and all
nineteen boundary-ideal declarations against the standard axiom allowlist.
Full CI remains the integration gate.
