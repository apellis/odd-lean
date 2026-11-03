# Weighted polynomial module caps

For SwappedVacuumNonpositiveBubbles §§3–4, `weightedPolynomialCap` applies
`(D²+1)^M` in the given restricted weighted module dot before the prescribed
canonical-content inverse-coefficient cap. `weightedPolynomialCap_mem`
retains its homogeneous degree. The original literal A/T vacuum and its
typed empty coordinate are retained.

`weightedPolynomialCapMoment_moduleCap` identifies every closure, on every
coefficient vector, with this module map and the given unit/dot column.
`weightedPolynomialCapMoment_sum` gives the binomial sum of the already
identified weighted moment maps; `weightedPolynomialCapMoment_eq_polynomialCapMoment`
attaches the existing χ/δ formula. The nonpositive first closure, its odd
sign and the zero-height specialization are proved by
`weightedPolynomialCapMoment_nonpositive_first`,
`weightedPolynomialCapMoment_nonpositive_first_odd` and
`weightedPolynomialCapMoment_zero_height_odd`.

At cutoff four and exponent two, the second closure is multiplication by
χ₁+2. On the same cap, dot and columns, replacing the polynomial by
`(D²−1)²` gives χ₁−2. These are
`weightedPolynomialCapMoment_second_four` and
`weightedCapMomentLinear_minus_second_four`. The paired asymmetric two-odd-colour
consumer proves the two closures differ on a nonzero surviving odd input,
and proves the polynomial module caps nonzero at both zero and strictly
negative external heights. This detects the polynomial sign beyond the
common monic first odd closure.

The producer and paired consumer pass strict scoped Lean checks. The audit
covers all 82 owned declarations, including private and generated ones,
using only the standard three axioms. Full-package CI remains the integration
gate. Identification with the prescribed mixed inverse cap remains open
until the actual slide and chosen content/weight fields are attached; no
independent extractor, module basis or Frobenius pairing is assumed.
