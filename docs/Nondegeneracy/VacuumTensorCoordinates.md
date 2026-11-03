# Recovering the reservoir vacuum from the tensor functor

The tensor vacuum functor of `VacuumTensor.md` sends the actual regular
empty probe to the reservoir vacuum tensored with its empty probe value.
`ELVVacuumTensorCoordinates.probeVacuumIso` identifies this whole module
with the given reservoir vacuum. This is the carrier comparison needed to
put the evaluated mixed bend and the normalized reservoir cap of
`SwappedVacuumCoordinates.md` on the same objects.

The component map is the raw linear equivalence
`TensorProduct.congr id e` followed by `TensorProduct.rid`, where `e` is the
inverse of the prescribed probe scalar coordinate. Its pure-tensor formula
is `v ⊗ w ↦ e(w) • v`. Naturality follows directly from tensor linearity and
linearity of every output module arrow. Evenness follows from the even
scalar coordinate and the even tensor right unitor. The generic
`scalarTensorIso` bundles these components into a genuine even module
isomorphism, including its inverse and both module inverse identities.

The actual height-zero probe is purely even. Using its existing
`probeVacuumScalarEquiv` gives `probeVacuumIso`; its forward map sends
`v ⊗ probeVacuumScalarEquiv(1)` to exactly `v`, with no sign or rescaling.
Both directions are even. The input-map Koszul factors of the tensor
vacuum functor are retained; this coordinate does not redefine that functor.

The exact producer and paired consumer pass strict scoped Lean checks.
All 20 owned declarations, including private and generated ones, pass the
standard axiom audit. The consumer uses the actual asymmetric all-odd
power vacuum, with cutoffs 4 and 6 and powers 4. A surviving odd exterior
coefficient occupies the tensor vacuum, its image is the unchanged
reservoir coefficient, and the isomorphism is nonzero. Both homogeneous
degrees and whole module inverse identities are checked. Full repository
CI remains the integration gate.

Transporting the prescribed inverse coefficient row through this even
isomorphism remains a subsequent square. The complete swapped mixed
inverse and bubble-series attachment are not asserted here.
