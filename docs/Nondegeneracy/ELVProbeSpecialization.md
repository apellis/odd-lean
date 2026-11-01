# Binomial coefficient specialization for cofinal probes

`ELVProbeCoefficients.lean` supplies the prescribed scalar coefficient values for arbitrary colourwise powers m. The cutoff is e_i*m_i, with e_i=2 at an odd colour and e_i=1 at an even colour. Even elementary generators e(i,r) map to choose(m_i,r+1); odd elementary generators map to (-1)^(r+1) choose(m_i,r+1). Exterior generators map to zero under the existing scalar evaluation.

The exact ELV elementary rank is m_i in both parities, and all values at or above that rank vanish. The resulting ordinary source polynomial is (X²−1)^m_i at an odd colour and (X−1)^m_i at an even colour. The calculation includes zero powers and arbitrary commutative coefficient rings.

`scalarCoefficientPolynomial_probe` identifies the source polynomial with the prescribed probe, and `elvProbeAffineSpecialization_dotPolynomial` proves its literal signed scalar Hom image on every strand. Producer and closed two-colour rational consumers passed strict direct Lean checks; all 33 owned declarations passed the consumer axiom audit. Full build with warnings as errors, global axiom audit and concrete consumers passed before research integration in #813 and #814.

The successor module `ELVProbeSpecialization.lean` proves the generator-span descent through the original `ELVOld.ideal` into the existing ordinary `cycHom` ideal. The descended Hom maps are surjective and commute with arbitrary right contexts. At finite colour type, `elvProbeWordEntry` maps the old quotient into the literal probe `CyclotomicAlgebra`, preserving identities and composition in matrix order. `elvProbeWordEntry_append` identifies the append map with the existing `cyclotomicAppend`.

The successor producer and closed mixed-parity rational consumers passed strict direct Lean checks, including the owner axiom audit of all 39 declarations. Full build with warnings as errors, global axiom audit and concrete consumers passed before research integration in #813 and #814. No positive-weight coefficient truncation, flatness, or preservation of integer grading is asserted. Comparison of the entire module action, including its prescribed inverse matrices, remains separate.
