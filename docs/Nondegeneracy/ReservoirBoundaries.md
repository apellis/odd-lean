# Source coefficients of literal reservoir boundaries

`ELVReservoirBoundaries` attaches the literal chosen
`W.loc.boundaryPos` and `W.loc.boundaryNeg` of
`SwappedHomInversion.md` §4 (7) to exact-content source coefficients.
It uses the fields chosen by `elvRouquierFamily`, without an independent
inverse comparison or grading of module Homs.

In namespace `ReservoirBoundaries`, `positive` is `boundaryPos(j,r)` and
`negative` is `boundaryNeg(r,j)`. Their `positiveContent` and
`negativeContent` restrictions act on every whole-weight input by the
corresponding original boundary component, by the two `_total` equations.
`positiveCoefficient` and `negativeCoefficient` reconstruct the source
coefficients of those restricted module-centre maps. The two coefficient
`_total` equations identify their realization with the same literal
whole-weight boundary on every input family.

The producer and paired `scripts/NonVacuity/ELVReservoirBoundaries.lean`
consumer passed Lean 4.34.1 with warnings as errors, both repository
compatibility options and default limits. All 15 owned declarations were
audited against the three allowed axioms. The consumer exercises both
boundary orientations, arbitrary natural indices, every module vector,
and a separately detected nonzero odd exterior vector in an occupied
content module.

This module identifies the coefficients, not their integer degrees.
Finite chosen inverse-coordinate comparisons and the source grading are
needed to prove degree `2 dᵢ(r-j)` for a finite window slot `j`. A block
without a predecessor kills the positive-weight cap boundary through its
lower induction object, but does not generally kill the negative-weight
unit boundary. The latter retains its finite unit inverse rows and must
be attached separately. No nilpotence of an entire weight category is
assumed.
