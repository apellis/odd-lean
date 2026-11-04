# The padded Dx entry on the regular vacuum probe

`paddedVacuumDx_odd` addresses SwappedHomInversion §3 (4)–(5) and
SwappedVacuumCoordinates §4. It identifies the prescribed padded Dx entry
with the evaluated odd vacuum bend through its displayed source and target
isomorphisms.

The input is an arbitrary superfunctor from the empty-content probe
module category to the full reservoir original-weight product. The two formal vacuum weights are changed
only by their equality charts. The same charts pull the given input back
to the literal zero sector, and normalize regular-probe evaluation.

Each actual negative pre-cap followed by a dotted post-unit is transported
through these equality charts and then through the separately constructed
vacuum cap and reservoir unit coordinates. The raw probe dot, normalized
pre-cap, reservoir unit and reservoir dot are retained. For an odd colour,
the chronological coefficient satisfies
`-(-1)^(r+1) = (-1)^r`, exactly the coefficient in the native bend expansion.

The outer dot in the chosen mixed bend has its existing output-content
nilpotence bound. The native induced reservoir dot has its homogeneous
symmetrizable bound. Taking the maximum of the two exponents yields two
series of the same length `2*n`; no stabilization or moment compatibility
is assumed. The two prescribed padded corner charts are retained in the
resulting source and target isomorphisms.

The concrete consumer uses both odd colours of the asymmetric
fixture, a reservoir with unequal cutoffs, and the full tensor-Hom input.
It retains a nonzero odd reservoir coefficient and its nonzero tensor with
the regular probe's scalar vector.

The proof transports each cap/unit word by the formal weight equality
square, applies the checked vacuum word-series comparison, and uses an
abstract additive chart lemma to compose the finite sum with the padded
corner charts. The public `vacuumSectorInput`, `vacuumSectorEvaluation`,
`sectorRegular`, `sectorEmpty`, and `vacuumSectorEvaluation_eq` retain the
input and evaluation charts needed by a subsequent principal-inverse
comparison.

The producer and paired consumer pass the pinned strict isolated checks.
All 41 owned declarations pass the standard-axiom audit; the consumer also
reaudits the 30 declarations of `RouquierHomWeightCoordinates`. No cap,
dot, unit, bend, or moment compatibility premise is added.
