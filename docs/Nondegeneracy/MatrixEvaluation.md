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
module/output/word coordinates. Product-coordinate inverse lifting and
the actual central evaluated inverse remain separate attachments.
