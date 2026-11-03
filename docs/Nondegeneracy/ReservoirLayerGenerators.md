# Factor dots in surviving reservoir matrix entries

This supplies the dot matrix-to-factor comparison in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`ProbeReservoir.reservoirLayerDotIso` keeps the actual left and right path
functors. It combines the path-append equality with the canonical
zero-probe-content chart on the middle dot strand. Its target is the left
path functor applied to the right path value postcomposed by the prescribed
reservoir raising functor.

`layerMap_reservoir_dot` starts with the literal matrix `layerMap` of
`P.upwardGens a`. At the selected reservoir path its output, followed by
this chart, equals the arbitrary input entry followed by the same chart
and the left path functor applied to `Z ◁ P.W.dot`, where `Z` is the actual
right path value. The proof collapses the existing matrix sum and uses
`dotImage_reservoirVacuum`. Neither outer context nor the input matrix is
replaced. This is an equality of whole Hom maps, hence includes arbitrary
parity components and every input vector. No generator comparison is
assumed.

The theorem requires a supplied complete `ProbeReservoir`. Its mixed
crossing coefficient is only an argument of the prescribed generator
record; no inverse or relation assertion for it is used by this dot
calculation. The right path is upward and ends at probe content zero.

The paired consumer constructs a complete positive-level two-odd ELV
factor pair with actual shifted adjunctions and multicolour relations. Both
contexts are nonempty; the matrix has an identity transport at its selected
three-letter reservoir path and zero elsewhere. The theorem is also
applied to every input family in this fixture. This consumer does not
assert that the identical factors give a separating model, that the tested
matrix entry is nonzero, or that its unused zero mixed coefficient is an
inverse. The nonzero mixed and two-odd vector calculations for the
contextual factor maps and their quotient classes are supplied separately
by `ELVTensorHomContexts` and `PowerWordLayerClasses`.

Strict producer and consumer checks pass. All four owned declarations
pass the standard axiom allowlist.

To attach this comparison to the intended OLD observation, specialize the
supplied reservoir to the unchanged chosen ELV data, transport the two
path contexts through `reservoirWordFunctorIso`, and use the corresponding
`TensorHomContexts.dot_apply` chart. `PowerWordLayerClasses.affine_class_square`
then gives the literal layer quotient class. The crossing matrix comparison,
supported-family evaluation, complete OLD probe relations and the vacuum
coefficient field remain separate requirements; no `VacuumCornerEvaluation`
is constructed here.
