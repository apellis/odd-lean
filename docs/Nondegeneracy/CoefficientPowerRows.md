# Inverse coefficient rows on the regular power vacuum

This attaches the normalized extraction window of
[SwappedVacuumNonpositiveBubbles, §2](SwappedVacuumNonpositiveBubbles.md)
to the literal old power vacuum constructed in
[CoefficientPowerVacuum](CoefficientPowerVacuum.md).
`ELVCoefficientPowerRows` and its occupied consumer pass scoped Lean checks
with warnings as errors and both pinned compatibility settings. All 17
owned declarations pass the standard axiom allowlist audit. Full CI
remains the integration gate.

Let A be the full ELV coefficient algebra, T its ideal of even elementary
powers, N the moving colour's positive cutoff, and M the actual balanced
induction of the regular A/T coefficient module to the old category.
The chosen even empty-component unit identifies M(empty) with literal
A/T. `PowerVacuumCoefficient.unit` is the ordinary append unit composed
with this identification. `functional` is the prescribed last
`moduleUnitCoefficient` row followed by its inverse. Neither a
coefficient extractor nor a bubble identity is a premise.

`functional_dot_window` proves, for every z in A/T and 0 ≤ a < N,

    λ(D^a u(z)) = if a + 1 = N then z else 0.

Here D is the existing signed induction dot. There is no additional cap
rescaling. `functional_mem` retains the top-row parity (N−1)p_i.
`indRes_eq_zero` kills the entire first mate-source summand on M, using
its proved nonempty-word support and balanced-tensor generation.

`empty_coefficient_action` identifies the old empty-endomorphism action
with the original left multiplication by the class of a in A/T, for
every coefficient, including odd ones. For a homogeneous coefficient a
of parity q, `functional_coefficient` consequently proves

    λ(output(a) z) = (−1)^((N−1)p_i q) [a] λ(z).

This follows from the actual inverse-row endomorphism naturality and the
chosen even empty-component unit; coefficient order is retained.

The connected asymmetric two-odd-colour consumer takes cutoff four and
fourth powers of the even elementary generators. Both independent odd
coefficient classes survive in A/T. Their top dotted units are proved
nonzero by extraction. Moving either odd colour, an odd coefficient on
the top dotted ordinary unit extracts to the negative of its nonzero
class. A mixed-datum instance also checks the same all-vector window
for both an even and an odd moving colour.

The functional belongs to the old literal power vacuum. Its higher raw
and signed moments are attached in
[CoefficientPowerMoments](CoefficientPowerMoments.md). The mixed inverse
caps and final swapped bubble action still require attachment. No vacuum
evaluation-kernel identity, integer support bound or all-height bubble
theorem is asserted.
