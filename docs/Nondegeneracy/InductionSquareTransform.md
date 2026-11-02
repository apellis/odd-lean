# Homogeneous transformations through an induction square

This supplies a coend comparison needed for the chosen generator transport
in [DeformedActionAssembly](DeformedActionAssembly.md), sections 5–6.
It uses the literal ordinary balanced tensors and retains full coefficient
parity in homogeneous transformations.

For a commuting square `J ⋙ U = Q ⋙ T`,
`ELVInductionSquareTransform.coendSquareMap` sends the coend for `J` with
input `Q ⋙ M` at `w` to the coend for `T` with input `M` at `U(w)`.
It sends `[g ⊗ b]` to `[U(g) ⊗ b]`, with the explicit endpoint equality
from the commuting square. `coendSquareCoefficient_balance` proves
balancing against every source arrow. The definition requires no fullness,
flatness or homogeneity of the tensor factors.

`coendSquareMap_transform` compares two such squares and homogeneous
families `α` and `β` of the same parity. When the coefficient arrows map
through the square, their induced transformations intertwine the canonical
coend maps. The proof keeps the full `twist k p g`; it does not assume that
an arbitrary coefficient arrow is homogeneous or even. In the weighted
application, the coefficient condition is the quotient image of the same
appended affine diagram, rather than an additional action hypothesis.

The producer and its paired consumer pass strict scoped checks. The
consumer uses a mixed even/odd connected datum and the actual old-to-weighted
quotient. It checks the literal tensor formula on an induced mixed
representable, both moving-dot parities, arbitrary output arrows and vectors,
and the odd coefficient's negative twist. All 15 owned declarations pass
the axiom allowlist audit. Full CI remains a separate gate.

This is the canonical map of raw coends. Identification with the selected
weighted append comparison and the two-letter flattening coherence needed
for crossing transport remain separate steps. This result alone supplies
neither the chosen crossing comparison nor a full factor action.
