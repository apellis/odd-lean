# Inverse coefficient rows as module maps

The left-cap normalization in `SwappedVacuumNonpositiveBubbles.md`, §2,
uses a coefficient row of the prescribed inverse unit matrix. Fix output
content ν with nonnegative crossing height, an old supermodule M, and an
index r in the prescribed unit count.

`contentUnitCoefficientMap` is an actual supernatural module morphism
from the restriction of FE(M) to the restriction of M on this content
category. It is the selected inverse `contentUnitMatrixIso.inv`, followed
by projection to coordinate `some r` and by the original source unshift
`homParityShiftDatum.iso.hom`. The projection is an even module map;
`contentUnitCoefficientMap_mem` proves that the composite has degree r*p.
Thus the inverse coefficient is natural as a module map, rather than
only a linear functional at one object.

`contentUnitCoefficientMap_total` gives this exact formula on every
component. `contentUnitCoefficientMap_total_surjective` proves that every
component is surjective: insert the inverse-unshifted target vector in
one product coordinate and apply the original forward unit matrix.

At the literal empty object, `contentUnitCoefficientMap_vacuum_total`
identifies the component with the previously specified
`moduleUnitCoefficient`. The two matrix inverses are equal because their
forward morphisms are the same prescribed matrix; no equality of inverse
formulas or additional cap scalar is assumed.

The paired consumer uses the canonical full-old regular-probe extension
for the asymmetric two-odd-colour datum over the rationals, at levels one
and two. Surjectivity gives a vector whose cap image is the nonzero image
of the original empty probe vector under its fully faithful inclusion
unit. It also applies the exact empty-component identification and the
homogeneous module-map theorem to these data.

Composing this map with the probe's fully faithful inclusion inverse,
comparing with the selected ordinary probe inverse row, and attaching the
result to the final mixed slide remain separate steps. No final swapped
vacuum datum or complete left-adjunction normalization is asserted here.
