# Distinct-colour crossing decoder

This develops Brundan–Ellis (1.12) through
[DeformedActionAssembly](DeformedActionAssembly.md) §§2–4. It uses the literal
ordinary right action throughout. The two-colour balanced source has induction
endpoint `i`, coefficient endpoint `j`, and coefficient shift `p(i)p(j)`.

`ELVDistinctCrossingTensor.toCyclotomic` is the prescribed affine crossing
column after both outer cyclotomic quotients and lower balance. Its tensor
formula retains arbitrary full exterior coefficients. The canonical map `q`
changes only the first factor. `shortCross_quotient_square` identifies the two
orders of imposing the enlarged ideal.

For `i ≠ j`, every append PBW tail ending in `j` has a first crossing. The
identity tail is absent by last-colour support. Peeling that crossing leaves
an append tail for induction by `i`, while its old coefficient ends in `j`.
The moving dot slides across the crossing with sign `(-1)^(p(i)p(j))` and no
divided-difference correction. `decode` retains the whole old quotient
coefficient, moves the dot power to the first tensor factor, and multiplies
by that sign to the dot exponent. `crossingEquiv` identifies the independently
balanced short source with the entire old-only append target; its inverse
is this explicit decoder.

The remaining quotient argument uses the checked full-ELV equality (9.3),
`ideal_eq_appendRelations_sup_outputOldRelations`. Postcomposition by an old
output relation acts on the first tensor factor, so its preimage under the
crossing equivalence belongs to the literal `firstIdeal`. Conversely that
first ideal is killed by the target cyclotomic quotient. Its exact kernel
is proved without any flatness hypothesis. These identifications are intended
to establish `cyclotomicEquiv`; the full quotient module and paired consumer
are currently proposed and await strict checking. The tensor source, tail
support, dot slides, and old-only decoder equivalence are scoped-checked.

The prescribed cup-crossing-cap mate comparison, its parity-shift source
isomorphism, naturality, and attachment to the full factor family remain open.
The even crossing column on the shifted source is not identified silently
with a supernatural representing map on the unshifted source.
