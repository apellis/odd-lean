# Evaluated matrix inverses and naturality

For the central augmented matrices in Brundan–Ellis (1.13)–(1.14),
`Supernatural.MatrixEvaluation` evaluates every entry at its actual total
supernatural component. Its `map_comp`, `map_id` and `map_ext` retain
composition, identity and detection of the whole natural matrix.

`isIso_of_components_target` and `isIso_of_components_source` lift
invertibility at every input object to invertibility of the whole matrix.
The forward entries have a prescribed parity depending on the target or
source index. The existing finite matrix inverse equations force both
parity and supernatural naturality of the chosen inverse entries; these
are conclusions, not additional premises. The even specialization is
`isIso_of_components`.

The producer and paired consumer pass strict checks and all eight owned
axiom audits. The consumer uses an invertible triangular two-by-two matrix
of identity and parity-shift superfunctors on rational superspaces, with
a nonzero odd off-diagonal entry also nonzero after evaluation at the unit.
It exercises both parity profiles and the even specialization.

This is the naturality step needed after central matrix inversion at
module/output/word coordinates. `MatrixProductEvaluation.isIso_of_components` now supplies the product
step: the coordinate inverse entries assemble on the entire product,
without finite output support. Its paired consumer uses an infinite
family of invertible triangular rational-module matrices, with a nonzero
off-diagonal entry at every natural-number coordinate. All three owned
declarations pass strict paired checks and the axiom audit. `MatrixNestedEvaluation` now composes these exact lifts at an input
module, output block and represented word. Its target/source parity
versions derive the whole natural inverse from those nested component
inverses; inverse naturality is retained at both module layers.

The nested consumer uses actual affine-collision ELV weight products,
identity outer functors and a triangular matrix with explicit component
inverses at every input, block and word. Both even parity profiles are
instantiated, with no whole-matrix inverse premise. Its literal nested
off-diagonal fixes an independently nonzero product of two odd
coefficients. All three owned declarations pass strict paired checks
and the axiom audit. The actual central evaluated inverse remains open.
