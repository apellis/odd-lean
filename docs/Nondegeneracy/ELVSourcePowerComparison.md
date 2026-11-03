# Literal coefficient powers in the actual old presentation

`ELVSourcePowerComparison.lean` extends the exact kernel comparison in
`ELVSourceQuotientComparison.md` by specified coefficient generators. Its
`coefficientGeneratorHomSpan` is independently defined inside existing
`ELVOld.hom` modules: arbitrary full-coefficient multipliers surround the
actual scalar generator at a word of the appropriate length.

`map_coefficientGeneratorSpan` proves that the source coefficient-generator
span maps onto this actual Hom span. It uses the existing coefficient
quotient on generators and lifts both context multipliers by surjectivity.
This holds for arbitrary coefficient sets, including odd and nonhomogeneous
coefficients; no parity specialization is required for this presentation
comparison.

`comap_oldIdeal_sup_coefficientGenerators` identifies the preimage of the
literal old first-boundary ideal plus this scalar span with the source ELV
relation span plus the same source coefficient generators.

For the paper's elementary powers, `elementaryPowerHomSpan` uses exactly
`elementaryCoefficients a ^ L a` in the actual ELV coefficient algebra.
`comap_oldIdeal_sup_elementaryPowers` proves the corresponding preimage
identity with the literal source powers `SYM.e a ^ L a`. The generator
comparison is the original coefficient quotient's `map_pow` identity.
No weighted ideal is substituted for the power ideal, and no alternate
quotient category is introduced.

The paired consumer uses the asymmetric two-odd-colour datum with Cartan
entries −2 and −4, tests a source set containing an even elementary and
an odd exterior generator, and instantiates the actual elementary-power
preimage with exponent three. It proves that all these elementary powers
have coefficient weight at least six.

Verification: strict pinned producer and paired consumer checks passed.
The consumer audits all six producer-owned declarations, including private
and generated declarations, against `propext`, `Classical.choice`, and
`Quot.sound`.

This is a source-presentation comparison inside actual old coefficient
Homs. Identifying vacuum evaluation with the resulting signed coordinates
remains separate work.
