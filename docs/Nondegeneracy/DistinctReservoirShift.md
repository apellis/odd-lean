# The shifted reservoir crossing

The pure reservoir entry of Brundan–Ellis Definition 1.5, (1.11)
uses the prescribed even beta/xi comparison `ProbeReservoir.postPairIso`.
The shifted factor mate uses the successive homogeneous parity removals
in `homShiftedPostCrossing`. Their equality is a needed coordinate
comparison before applying the reservoir inversion relation to that entry.

`Sigma/DistinctReservoirShift.postPairCrossing_eq` identifies the given
even comparison with

    sign((q+p)r) · homShiftedPostCrossing(p,q,t,Z)

for a factor crossing `t` of parity `r`. It reuses the existing
`postPairIso_cross_remove` theorem and expands `homPostPairRemoval`;
there is no additional naturality or comparison hypothesis. For content
shifts `p = parity(i) contentParity(beta)` and
`q = parity(j) contentParity(beta)`, the factor crossing has
`r = parity(i) parity(j)` and the exponent `(q+p)r` vanishes.

The paired consumer uses a nonzero odd crossing in the two-envelope of
the rational unit bicategory, with independently shifted letters. Both
orders of the two shifts retain the negative normalization coefficient.
The consumer audits all declarations owned by the comparison module
against the standard axiom allowlist.
