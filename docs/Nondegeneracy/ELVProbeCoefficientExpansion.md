# Component expansions of the constructed probe–reservoir coefficient

`SwappedHomInversion.md` §3 (2)–(3) identifies the literal mixed crossing entry
with a finite ordinary series at even colours and an ordered signed series at
odd colours. The coefficient is `elvProbeCrossCoeff`; its inverse identities
and whole probe-dot unit are supplied by `ELVProbeDenominatorUnits`. The
reservoir bound is constructed after evaluation at one input and output block.
No uniform nilpotence exponent is assumed.

The two `elvProbeMixedCoefficient_*_expansion` statements express the formula
for a coefficient with its inverse identity. The two
`elvProbeCrossCoeff_*_expansion` statements specialize to the constructed
coefficient. Their result predicates, `elvProbeEvenCoefficientExpansion` and
`elvProbeOddCoefficientExpansion`, retain the same nilpotence witness and series
equality. The even series is the negative sum of `x⁻¹^(r+1) y^r` for `r<n`;
the odd series includes the sign `(-1)^r` for `r<2n`.

The current encoding states the arithmetic over an abstract ring and evaluates
the coefficient while the factor pair is abstract, before specializing to the
chosen probe–reservoir pair. The carrier, validity proof and Hom input are bound explicitly in each specialized statement, so the evaluation map and crossing entry use the same literal RP object.

The producer and paired consumer pass scoped checks with the pinned toolchain, warnings as errors and both compatibility settings. The consumer audits all 17 owned declarations against the repository axiom allowlist and applies the constructed even and odd expansions on mixed-parity and asymmetric two-odd factor pairs. It also supplies nonzero append vectors for the acting twisted probe parameters.
