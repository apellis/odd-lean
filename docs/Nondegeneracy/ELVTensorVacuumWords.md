# Arbitrary word contexts on the tensor-vacuum Hom

This extends [ELVTensorVacuumGenerators](ELVTensorVacuumGenerators.md)
through arbitrary reservoir word contexts, for
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`TensorVacuumWords.wordHom ν` successively postcomposes the specified
`WeightTensorVacuum.selectedHom` by the same chosen reservoir E functors.
At the empty word, only the proved equality between the two presentations
of the original lowest weight is transported. No module, functor, scalar
chart, parameter or coefficient quotient is replaced. `wordHom_append`
records the literal next postcomposition. Here `ν` is the reservoir append
tuple, so the source strand word has colours `ν.reverse`, in accordance
with [ELVReservoirWordValue](ELVReservoirWordValue.md).

`valueIso` identifies evaluation of this Hom word at the specified
`regularProbe` with `PowerWordEvaluation.value ν`. Its base comparison is
the existing `selectedIso`; its induction step applies the given E functor
to the preceding comparison. `valueIso_even` proves that this comparison
is even for every word. The full selected chart is then `chart`, obtained
by following `valueIso` with the existing native word chart; it too is
even.

`dot` identifies the literal reservoir dot whiskered by `wordHom ν` and
evaluated at `regularProbe`, using the selected append chart. `cross`
does the same for the literal reservoir crossing in the two selected pair
charts. Both are equations of whole weight-product module maps. The
crossing retains the given intermediate original weights and includes
equal and distinct colours. `dot_apply` and `cross_apply` give the equations
for every vector, every output content object, and every formal content
block of those products. Neither a basis-vector restriction nor a
scalar-extraction assumption is present.

`homEquiv` uses `valueIso` and the already established
`PowerWordHomCoordinates.homEquiv` to give whole Hom coordinates on the
evaluated tensor-Hom word. Its target is the explicit same-weight word
family. `homEquiv_from_old` proves that every full-coefficient old-word
generator has its unchanged original coordinate under this equivalence.
The equivalence is defined on all module maps, including odd and
inhomogeneous maps, and retains all off-support components.

The paired consumer supplies two connected asymmetric fixtures over `ℚ`:
one with two odd vertices, and one with an even and an odd vertex. In the
nonempty context `[false,true]`, bounded regular-power injections prove
that the relevant exterior coefficients survive in the chosen word
modules. The same append and pair charts pull these to nonzero inputs in
the literal three-E and four-E tensor-Hom values. The dot, equal odd
crossing and distinct crossing vector equations are applied to these
inputs. The consumer also instantiates the even comparisons and whole Hom
coordinates with the old identity map and arbitrary target vectors.

The producer and consumer pass the strict scoped checks; all 46 owned
declarations pass the standard axiom allowlist. This identifies the
underlying chosen reservoir generators on the specified OLD tensor Hom
through every word context. A completed chosen `ProbeReservoir`, the
attachment of these comparisons to its literal layer matrices and
`ev_layer`, and the resulting nondegeneracy conclusion are separate
obligations.
