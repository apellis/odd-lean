# Equal-level normalization of the evaluated mixed bend

`ELVTensorVacuumPrincipalCap` proves (8) of
`SwappedVacuumNonpositiveBubbles.md` on the same chosen operators as the
negative-height calculation. At equal levels `P = 2*m = N`, it proves

`evaluatedMixedBend ≫ (evaluatedPostDot² + 1)^m ≫ tensorPowerVacuumCap = shiftedPreCap`.

Every input to `InverseCapMoments.principal_cap_polynomial` is supplied by
the actual maps: the evaluated A6 signed slide, the native inverse-row
window on `H(N0)`, and the polynomial annihilator of the raw shifted probe
dot. The polynomial `(X²+1)^m` is monic of degree `2*m`, and its even-degree
support retains the signed slide coefficients. No principal mixed inverse,
extractor, or cap compatibility is assumed. In particular, no global sign
is added to the polynomial cap.

The intermediate action calculation retains the existing positive
symmetrizer and homogeneous-parameter hypotheses used for reservoir dot
nilpotence. It does not assert the broader conjecture for arbitrary data.

The exact producer and occupied paired consumer pass strict scoped Lean
checks. All 27 owned declarations, including private and generated ones,
pass the standard axiom audit. The consumer uses the asymmetric
all-odd datum with matched probe and reservoir levels 2 and 4 and the
literal coefficient power quotient with powers 4. A surviving odd
coefficient occupies `H(N0)`; the normalized cap and mixed bend are nonzero.
Full repository CI remains the integration gate.

Identification of the complete swapped principal matrix inverse remains
open. This identity supplies its required equal-level normalization on the
specified vacuum component, rather than constructing that inverse.
