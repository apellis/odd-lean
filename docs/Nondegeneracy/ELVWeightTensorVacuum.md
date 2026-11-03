# Tensor vacuum on the original weight products

This supplies the initial-family attachment in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §2, required by
the selected reversed reservoir word comparison. The probe target is the
scalar-evaluated OLD probe, with all formal contents of its original
weight. The reservoir target is the full-coefficient ELV weight product.

`WeightTensorVacuum.emptyProbe` evaluates the formal empty probe block and
forgets only the scalar-evaluation property, retaining all module maps.
`regularProbe` places the evaluated regular height-zero module at that
block and the zero module at every other formal content. This includes
nonempty contents with the same original weight; no injectivity of the
root map is assumed. `emptyProbe_regular` proves that the resulting module
is exactly the prescribed regular probe.

`WeightTensorVacuum.hom` tensors every component of a reservoir family
with the value of this probe evaluation. It is a superfunctor between the
full original-weight products, and hence a swapped Hom input. Its input
maps are the existing tensor-vacuum maps, including their Koszul signs.
`regularIso` identifies its value at `regularProbe` with the entire
reservoir family. Its components are the proved regular-probe evaluation
followed by `VacuumTensor.scalarTensorIso`; both directions are even, and
the comparison is natural on all reservoir module arrows, including odd
ones.

`regularIso_hom_apply` describes the map on every vector using the original
probe scalar coordinate and the tensor right unitor. In particular,
`regularIso_hom_tensorVector` sends the tensor of any reservoir vector
with the prescribed regular probe vector to that same reservoir vector.
There is no supplied equality identifying a hypothetical Hom input with
the desired vacuum.

`selectedHom` and `selectedIso` use the exact regular-power empty-word
family `ReservoirWordValue.initialValue`. Together with the reversed-word
value comparison, they provide the specified initial input for the
reservoir path. Transport of dot and crossing maps along this comparison,
literal swapped layer observations, and the final nondegeneracy argument
are separate obligations.

The paired consumer uses the connected asymmetric two-odd datum over
`ℚ`, the actual OLD probe, and the selected full reservoir family. A product
of the two independent odd coefficients survives in the empty reservoir
module by the existing bounded coefficient injection, occupies the
tensor-vacuum Hom value, and maps to its unchanged coefficient. The
consumer also applies the whole-family comparison and both inverse
identities, and checks every owned declaration against the standard axiom
allowlist.
