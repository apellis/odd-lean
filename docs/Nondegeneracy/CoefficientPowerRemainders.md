# Ordered remainders on the literal coefficient-power vacuum

This attaches the ordinary-remainder calculation of
[SwappedVacuumNonpositiveBubbles, §2](SwappedVacuumNonpositiveBubbles.md)
to the actual inverse-row moments of
[CoefficientPowerMoments](CoefficientPowerMoments.md).
`ELVCoefficientPowerRemainders` and its paired occupied consumer pass
scoped Lean checks with warnings as errors and both pinned compatibility
settings. All 52 owned declarations pass the standard axiom allowlist
audit. Full CI remains the integration gate.

## The ordinary coefficient convention

Fix an odd moving colour, N>0, and the actual A/T-valued raw moment
μ_n=λ([t^n]⊗E(1)). Put r=N−1 and σ_r=(−1)^binom(r,2).
`ordinaryMoment` is the derived sequence

    ell_n = σ_r (−1)^(r(n+r)) μ_n.

`ordinaryMoment_window` gives ell_n=[n=N−1] for n<N. The coefficient
sign of the actual inverse row converts its raw recurrence to
`ordinaryMoment_recurrence`, the literal ordered monic recurrence with
the original coefficients c_j on the left. No monic-remainder functional
is supplied as a premise.

Define R_l=ell_(N−1+l). `remainder_zero` gives R_0=1, and
`remainder_recurrence` is the complete shifted recurrence. Terms whose
shift would be negative vanish by the proved low window. The proof uses
only nonnegative dot powers.

The same top-row sign combines with the normalized monic odd coefficient
to give `odd_effective_coefficient` and `odd_rawMoment_recurrence`: the
effective raw coefficient indexed by a=N−j is (−1)^a[c_a], independent
of the parity of N. Its ordinary counterpart retains (−1)^(Na)[c_a].

## The complete inverse series

`remainderPolynomial` is the reversed literal monic relation

    F(w) = sum_(j=0)^N [c_j] w^(N−j),

and `remainderSeries` has coefficients R_l. The actual ordered recurrence
proves

    F(w) R(w) = 1,    R(w) = invOfUnit(F(w),1).

These are `remainderPolynomial_mul_remainderSeries` and
`remainderSeries_eq_invOfUnit`. The constant coefficient of F is one.
The coefficient ring remains literal A/T, including its odd coefficients;
the PowerSeries inverse works over its ring structure. No commutative
replacement or inversion of a coefficient is made.

At every exponent, `signedMoment_remainder` proves the written
normalization

    (lambda D^(N−1+l) u)(1) = (−1)^binom(l,2) R_l.

This includes the sign contributed by the extracted coefficient parity.
Thus the complete ordinary inverse series is attached to the actual
signed-dot/ordinary-unit moments, without a cap rescaling.

`odd_coefficient_tail` also proves that every coefficient beyond the odd
cutoff vanishes in A/T. At even N this uses the defining δχ_(N/2)=0
relation for the first odd tail, as required by the finite polynomial
identity in the written proof.

The connected asymmetric two-odd-colour consumer at N=2 and elementary
squares checks the complete formal inverse in both multiplication
orders, the normalization at every l, and R_1=−[δ_i]≠0 for each independent
odd colour. It recovers the actual signed second-dot moment as −[δ_i].
It also checks the literal even-cutoff relation [δ_i e_(i,0)]=0.

The closed odd-colour even/odd decomposition in terms of 1/C(−z) is
proved in [CoefficientPowerOddSeries](CoefficientPowerOddSeries.md). The
probe-polynomial numerator and final swapped bubble maps remain to be
attached. No
vacuum evaluation-kernel identity or all-height bubble theorem is asserted.
