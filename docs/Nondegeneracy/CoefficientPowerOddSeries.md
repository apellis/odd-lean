# Closed odd reservoir series on the literal power vacuum

This attaches the two series in
[SwappedVacuumNonpositiveBubbles, §2 (7)](SwappedVacuumNonpositiveBubbles.md)
to the actual inverse-row moments of the old regular A/T vacuum.
`ELVCoefficientPowerOddSeries` and its connected occupied consumer pass
scoped Lean checks with warnings as errors and both pinned compatibility
settings. All 64 owned declarations pass the standard axiom allowlist
audit. Full CI remains the integration gate.

Let N>0 be the cutoff of an odd moving colour. Write C(z)=sum χ_r z^r,
with χ_0=1, and let R(w) be the constructed ordinary remainder series of
[CoefficientPowerRemainders](CoefficientPowerRemainders.md). The map from
the universal polynomial coefficient algebra to literal A/T is
`polynomialToPower`. All expansions, rescalings and polynomial-series
inversions take place in that commutative polynomial algebra before
applying this map. A/T retains its original ring and exterior multiplication.

`odd_remainderPolynomial_coeff` identifies every coefficient of the
actual reversed monic relation F(w), including degrees beyond N. The
proved odd coefficient tail, with the even-cutoff δχ_(N/2) relation,
gives the exact factorization

    F(w) = C(w²)(1 + (−1)^N δ w).

`remainderPolynomial_factor` proves this identity after literal coefficient
evaluation. `oddLinearTerm_mul_self` retains δ²=0. The mapped elementary
series and its mapped inverse multiply to one in both orders.
`remainderSeries_factor` therefore identifies the actual ordinary
remainder series as

    R(w) = (1 − (−1)^N δ w) / C(w²).

The exterior factor remains on its original left side; no coefficient
is commuted past another odd coefficient.

For h_l=(lambda D^(N−1+l)u)(1), the already proved signed normalization
and the new `signedMoment_even` and `signedMoment_odd` give every coefficient:

    sum h_(2r) z^r   = 1 / C(−z),
    sum h_(2r+1) z^r = (−1)^(N+1) δ / C(−z).

Concretely `completeCoefficient(i,r)` is the literal coefficient of the
mapped inverse of C(−z). Both formulas concern actual signed-dot moments
of the ordinary unit and the prescribed inverse row. No independent
moment formula is supplied as a premise.

`signedMoment_first_odd` consequently proves, for every positive
cutoff of an odd colour,

    (lambda D^N u)(1) = (−1)^(N+1) [δ].

The connected asymmetric two-odd-colour consumer takes cutoffs four and
five and fourth powers of every even elementary generator. It instantiates
both complete series at every r. Each independent odd coefficient survives;
the first higher moment is negative at cutoff four and positive at cutoff
five. The first nonconstant complete coefficient is the surviving χ_1.
Its product with the same-colour δ is also proved nonzero by the actual
bounded coefficient injection and a polynomial/exterior basis coordinate.
Thus the next odd coefficient tests both its polynomial and exterior factors.

These are scalar values on the actual ordinary unit vector 1. The full
higher-moment map on arbitrary A/T vectors, the probe-polynomial numerator,
and identification with the mixed inverse caps and final swapped bubbles
remain to be attached. No vacuum evaluation-kernel identity or all-height
bubble theorem is asserted.
