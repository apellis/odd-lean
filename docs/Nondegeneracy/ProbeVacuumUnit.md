# An occupied regular probe append unit

This supplies the nonzero vacuum probe vector needed by `SwappedVacuumBubbles.md`, §1. The producer pair and its consumer pass scoped checks. The argument uses the existing unit-matrix inverse and the specified scalar comparison, with no new polynomial quotient presentation.

`probeOldVacuumVector` is the actual empty word-idempotent vector of `probeOldVacuumRegular`, the regular height-zero probe with its old action. Its original matrix entry is the empty affine identity. That identity is a nonzero PBW basis vector, so `probeOldVacuumVector_ne_zero` holds over any nontrivial ground ring covered by the construction.

`oldVacuumInductionUnit_injective` uses slot zero of the prescribed inverse unit matrix to split append from the empty old component whenever the cutoff is positive. `oldContentVacuumInductionUnit_injective` transfers this along the selected full-content extension/unit comparison and the fully faithful inclusion unit. No inverse of the comparison is needed for this implication.

`probeOldVacuumAppendVector` is the native content append unit applied to the preceding regular vector. `probeOldVacuumAppendVector_ne_zero` proves that the original old append coend is occupied for every positive probe level, in either moving parity.

`probeOrdinaryVacuumAppendVector` transports this vector by the specified `probeAppendLinearEquiv`. Its injectivity gives `probeOrdinaryVacuumAppendVector_ne_zero` in the actual ordinary append coend. `probeOrdinaryVacuumAppendVector_eq_unit` uses the exact computed forward map and its unit formula to identify this image with the literal ordinary append unit. The source regular module's scalar-evaluation property is proved.

The consumer uses the original connected all-odd datum, with probe exponents one and two. It checks the nonzero empty, old append and ordinary append vectors. At exponent one, the signed annihilator from `ProbeVacuumPolynomial.md` gives

    D²v = −v,   v ≠ 0,

on this actual probe coend. The consumer also proves `(D²−1)v ≠ 0` over ℚ. This tests the numerator sign on the actual occupied probe object. Every declaration owned by the two producers is audited.

This closes the actual probe-occupancy caveat of the preceding polynomial consumers. It does not construct the final swapped mate slide or identify the mixed cup/cap normalization.
