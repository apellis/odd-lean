# Regular coefficient-power vacuum on the old category

**Proposed source; this batch and its consumer are not yet verified.** The
empty-coefficient embedding producer has a strict scoped check, but this
does not establish the regular-old-vacuum construction or its paired
consumer. These sources are not exported as checked library results.

The intended vacuum in [SwappedNondegeneracy, §2](SwappedNondegeneracy.md)
is the old-category extension of the literal regular A/T coefficient
module from [CoefficientPowerGrading](CoefficientPowerGrading.md).
The coefficient category embeds at the empty old word by literal
coefficient identities. The affine-empty PBW coordinate decodes every
empty-word coefficient, and `ideal_nil` says there is no old cyclotomic
relation at that word. The intended `emptyCoefficientEquiv` gives the full
Hom comparison and makes this embedding fully faithful, with its complete
coefficient parity and multiplication order.

Define `coefficientPowerVacuum` by the existing balanced induction along
this embedding, applied to the actual regular quotient module. The
existing fully faithful unit isomorphism should identify its empty
component with literal A/T. Word-content support should kill every
nonempty component. Sliding each even power generator through a balanced
tensor should prove annihilation by the entire literal power ideal, using
its verified generator characterization.

The current source defines the embedding, its coefficient decoder and
fully faithful comparison, the induced old module and proposed chosen
unit isomorphism. Support, power-ideal annihilation, occupied regular-old
vacuum consumers and all-owned-declaration audits remain to be completed.
No final swapped vacuum, evaluation kernel, integer grading or positive-dot
nilpotence is asserted.
