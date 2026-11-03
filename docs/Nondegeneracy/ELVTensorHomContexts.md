# Outer E contexts on surviving Hom entries

This supplies the outer E-word whisker left open by
[ELVTensorHomEntries](ELVTensorHomEntries.md), for
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`TensorHomContexts.context` bundles the existing
`PowerWordWeightContexts.contextFunctor` with its additive, linear and
superfunctor structures. Its objects and maps are unchanged: it is the
literal successive chosen reservoir E functor at each original weight.

`dot` and `cross` start with the actual Hom two-morphisms

    (wordHom ν ◁ reservoir generator) ▷ context η.

They evaluate at the specified regular probe and use the existing context
chart applied to the already checked tensor append or pair chart. The
result is precisely `wordFamilyArrow` of the corresponding
`PowerWordContexts.extendedArrow`. The crossing retains the given original
intermediate weights and includes equal and distinct colours.

`dot_apply` and `cross_apply` then postcompose an arbitrary whole Hom
entry `f` from an arbitrary source Hom object `G` with that same literal
contextualized generator. They prove the coordinate identity at every
source vector in every content object of every formal-content block.
There is no homogeneity restriction on `f`, independent generator
comparison assumption, or faithfulness premise. The proof combines total
evaluation of Hom composition with the chosen word-arrow context square.

The consumer supplies both the connected asymmetric two-odd datum and a
connected mixed even/odd datum over `ℚ`. Its inner tuple is
`[false,true]` and its nonempty outer tuple is `[false]`. Bounded power
injections prove that exterior coefficients survive in the literal
four-E dot and five-E equal/distinct crossing inputs under these same
context charts. The concrete Hom entries are identity maps on those
actual chosen postcomposition functors. The consumer also instantiates
both formulas for arbitrary whole input entries and arbitrary vectors.
The producer and consumer pass strict scoped checks, and all 25 owned
declarations pass the standard axiom allowlist.

For a literal affine layer `u ⊗ g ⊗ v`, the reservoir append tuples are
the reversed source-order tuples. Thus `ν` is the inner tuple contributed
by `v`, while `η` is the outer tuple contributed by `u`. These statements
now supply the chosen generator square on the actual tensor Hom entry
with both whiskers present. They do not assemble the sector families into
a completed chosen `ProbeReservoir`.

The remaining attachment is to transport this entry through the actual
`pathFunctor` comparisons in `ProbeReservoir.layerEntry`, collapse the
middle-path sum at probe content zero, and use
`SwappedRelationData.upwardModuleAction_act_layer` for the relation-derived
action. The supported `Gs`/`Ys` recipe is in
[ELVTensorHomEntries](ELVTensorHomEntries.md#remaining-attachment-to-the-literal-layer-action).
The signed old quotient comparison must then identify the coordinate
with the specified quotient class. Neither a literal `ev_layer` field nor
a nondegeneracy conclusion is asserted here.
