# Coefficients on the tensor-vacuum Hom

The source action required by SwappedVacuumCoordinates §§2–6 is an
algebra action on the whole tensor-vacuum input, before evaluation at the
regular probe. `VacuumTensorCoefficientMaps.sourceCoefficientAction` has
source `SYM D k` and target the endomorphism algebra of
`WeightTensorVacuum.selectedHom`. It uses the specified ELV coefficient
quotient, the regular-power module action, weighted descent, restriction
to every original-weight block, and tensoring on the reservoir factor.
The input remains the entire original probe weight product.

The generic `reservoirEndAction` tensors a reservoir endomorphism with the
identity on the probe factor at every input module. Its supernatural
naturality follows from the signed tensor interchange law.
`coefficientAction_mem` retains the degree of every homogeneous ELV
coefficient, and `coefficientAction_total` gives the literal first-factor
operator for every probe module, reservoir block, output object and
vector. Inhomogeneous coefficients are included in the algebra map.

`coefficientAction_regular` is an equality of whole reservoir-family
morphisms under the prescribed regular-probe isomorphism.
`coefficientAction_regular_apply` gives its value on every vector, and
`sourceCoefficientAction_tensorVector` places an arbitrary source SYM
coefficient on an arbitrary reservoir tensor vector in the same chart.
The coefficient multiplication is the original one: an algebra product
acts by chronological composition in the corresponding endomorphism
algebra. No precomposition action or commutative replacement is used.

`pathCoefficientAction` is direct right whiskering of that whole-input
source action by the specified reservoir path functor.
`pathCoefficientAction_total` identifies its evaluation on every probe
module. `postcompositionAlgHom` and `pathHomCoefficientAction` then act on
the entire Hom from an arbitrary source functor to the chosen path Hom,
by literal postcomposition. These maps retain the same source SYM ring
and multiplication order.

The paired consumer `scripts/NonVacuity/ELVVacuumTensorCoefficientMaps.lean`
uses two distinct odd colours in the asymmetric two-colour datum. One odd
source coefficient acts on a tensor vector carrying the other odd
coefficient. Its regular chart is their ordered product in the literal
coefficient-power quotient, and bounded coefficient injectivity proves
that the resulting tensor vector is nonzero. The consumer also checks
the whole-input odd parity, the raw coefficient algebra law and the sign
under reversing the two odd coefficients. Its owned-declaration audit
allows only `propext`, `Classical.choice` and `Quot.sound`.

The remaining comparison is the coefficient square under the global
word chart: the direct path-whiskered action must agree with the
specified signed word-family coefficient arrow under
`TensorVacuumWords.chart` and its original-weight path transport. The
regular vacuum square above supplies its empty-word input, but does not
assert that global word square or the resulting matrix-observation
coefficient compatibility.
