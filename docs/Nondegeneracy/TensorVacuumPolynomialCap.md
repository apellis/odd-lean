# The polynomial cap and the evaluated mixed bend

`ELVTensorVacuumPolynomialCap` proves (9) of
`SwappedVacuumNonpositiveBubbles.md` for the actual evaluated A6 bend and
the prescribed inverse coefficient row on its exact tensor-vacuum carrier.
At `P = 2*m < N`, it proves

`evaluatedMixedBend ≫ (evaluatedPostDot² + 1)^m ≫ tensorPowerVacuumCap = 0`.

The proof supplies every input of `NegativeCapMoments` from the existing
chosen maps. The signed slide is the proved A6 bend slide. The normalized
window is `tensorPowerVacuumCap_window`, already identified with the native
inverse row on `H(N0)`. The probe relation is the polynomial annihilator of
the raw shifted pre-dot; its source parity comparison is retained, rather
than replacing that dot by the unsigned coordinate dot. The coefficients
of `(X²+1)^m` are supported in even degrees, so their multiplication by
`(-1)^n` is unchanged. Evaluating this polynomial is exactly `(x²+1)^m`.
No mixed isomorphism, cap window, or slide is supplied as a new premise.

The intermediate action calculation retains the existing positive
symmetrizer and homogeneous-parameter hypotheses, used for the actual
reservoir dot nilpotence. It does not strengthen the scope to arbitrary
Cartan data.

The exact producer and occupied paired consumer pass strict scoped Lean
checks. All 23 owned declarations, including private and generated ones,
pass the standard axiom audit. The consumer uses the asymmetric
all-odd literal power vacuum, probe degrees 2 and 4, and reservoir cutoffs
4 and 5, so both negative heights are present. The same normalized cap is
nonzero. The consumer also proves that the annihilated mixed bend itself
is nonzero, using the prescribed splitting probe cap and reservoir unit.
Full repository CI remains the integration gate.

This closes the polynomial annihilation test for the prescribed candidate
extreme row. Identifying that row with the complete swapped augmented
inverse, and hence identifying the bubble series, remains separate.
