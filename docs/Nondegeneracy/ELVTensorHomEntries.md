# Surviving reservoir Hom-entry evaluation

This supplies the Hom-entry square needed to attach
[ELVTensorVacuumWords](ELVTensorVacuumWords.md) to the layer matrices in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`TensorHomEntries.dot_apply` takes an arbitrary source Hom object `G` and
an arbitrary whole supernatural map

    f : G → wordHom ν ≫ E_i.

It evaluates the literal layer-row composition
`f ≫ (wordHom ν ◁ reservoir.dot)` at the actual regular probe and then at
an arbitrary vector in an arbitrary formal-content block. Applying the
selected append chart gives exactly the old-Hom dot applied to the chart
of the evaluated input entry. `cross_apply` proves the corresponding
statement for `f : G → wordHom ν ≫ E_j ≫ E_i` and the two selected pair
charts. The original intermediate weights, equal and distinct colours,
and every coefficient vector are included. There is no homogeneity
restriction on `f` and no independently supplied generator-comparison
hypothesis.

`coordinates` applies the established whole Hom coordinate equivalence
after evaluation of an actual Hom entry and a specified target chart.
`coordinates_apply` proves that this is literal total evaluation at the
selected source cyclic vector. The consumer supplies the already proved
`TensorVacuumWords.chart`, rather than assuming a vacuum identification.
No injectivity or faithfulness of evaluating all supernatural
transformations at the regular probe is asserted.

The paired consumer supplies both the connected asymmetric two-odd datum
and a connected mixed even/odd datum over `ℚ`. Its source Hom objects are
the chosen tensor-Hom words in the nonempty context `[false,true]`.
The actual input Hom maps are `2 • identity`; their values on the surviving
exterior-coefficient vectors are proved nonzero. The literal dot, equal
odd crossing and distinct crossing squares are applied to these entries.
The consumer also instantiates the formulas for arbitrary whole input
maps and arbitrary source vectors.

The producer and consumer pass the strict scoped checks; all 16 owned
declarations pass the standard axiom allowlist.

## Remaining attachment to the literal layer action

For an observation with source strand word `s`, put `ν = s.reverse` and
let `c` be its formal content. Once the chosen OLD probe and reservoir are
assembled into the actual `ProbeReservoir P`, use the following families
in `P.Mod`, transporting only proved equal presentations of original
weights:

* `Ys (0,0)` is `WeightTensorVacuum.selectedHom`; every other `Ys` sector
  is the zero Hom functor.
* `Gs (0,c)` is `TensorVacuumWords.wordHom ν`; every other `Gs` sector is
  the zero Hom functor. The equality of its target weight with
  `-ΛR + contentWeight c` follows from the formal content of `ν`.

For an upward target word `t`, only the row `(0,c)` and right endpoint
`(0,0)` can contribute. `VacuumPaths` gives uniqueness of paths into probe
content zero, and `ReservoirPaths` constructs the surviving all-reservoir
path when the formal contents agree. `ReservoirWordFunctor` removes its
vanishing parity shifts and identifies its postcomposition order.
The existing reversed-word and tensor-Hom charts then identify evaluation
of this entry with the actual chosen reservoir word value. Evaluating the
input supernatural map at the regular probe and using the whole Hom
coordinates gives the corresponding full old-Hom coefficient vector.

The squares proved here are the surviving reservoir entries for a dot or
crossing with an arbitrary inner word context. A general affine layer
`u ⊗ g ⊗ v` also has an outer E-word whisker. The existing
`PowerWordWeightContexts.context_family_arrow`, `dot_in_context` and
`cross_in_context` supply its native chosen-word comparisons; their
attachment to the same tensor-Hom entry evaluation is still required.
Then `ProbeReservoir.layerEntry` is exactly the input entry followed by
that contextualized generator, with its prescribed path-append equality
transports. The unique-path sum reduces `layerMap` to this composition.
Finally `SwappedRelationData.upwardModuleAction_act_layer` identifies the
relation-derived action with this literal layer map. The old quotient and
signed half-turn comparisons must identify its coordinate with the
specified quotient class before constructing
`VacuumCornerEvaluation.ev_layer`.

The completed chosen probe record, these matrix and contextualization
transports, the quotient-class attachment, and `ev_vacuum` remain separate
obligations. The present result is a concrete surviving-entry square; it
is not a `VacuumCornerEvaluation` or a nondegeneracy theorem.
