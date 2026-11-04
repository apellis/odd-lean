# Weighted inverses in coefficient kernel coordinates

For DeformedMatrixComparison §4 and the inverse degree step G8, `weightedUnitInverse_coordinates` and `weightedCapInverse_coordinates` compare the independently constructed weighted and OLD matrix inverses using their checked forward squares. Every finite parity coordinate is retained; `weightedUnitInverse_none` singles out the literal principal row.

`weightedContentUnitInverse_atWord` and `weightedContentCapInverse_atWord` identify the exact-content inverse total at the original word with the corresponding weighted component inverse. Their arbitrary-content-object variants use only the object's content identity.

`weightedUnitPrincipalInverseValue` and `weightedCapPrincipalInverseValue` remove precisely the named weighted and parity charts from that component inverse. The `_eq` theorems identify the selected OLD inverse; the `_tensor` theorems identify its raw positive or negative kernel principal inverse on each coefficient tensor. No inverse compatibility assumption is supplied.

The producer and paired consumer pass strict scoped checking, and all 28 owned declarations pass the standard axiom allowlist audit. The consumer covers both moving parities, positive and negative heights, empty windows, and a nonzero weighted inverse value detected independently from an odd coefficient in a truncated one-strand quotient. Full package CI remains the integration gate.
