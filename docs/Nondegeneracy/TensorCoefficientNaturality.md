# Tensor coefficient arrows and even charts

The proposed base step for the coefficient observation square can avoid
an equality between two chosen empty-word charts. Identify the full
source action with the actual output module action on the coefficient
arrow. Every even module chart then intertwines that arrow, including
an odd or inhomogeneous coefficient, by ordinary naturality of its even
component. This uses no commutativity of the source coefficient ring.

`TensorCoefficientNaturality.contentCoefficientArrow` is the same
coefficient scalar in the truncated content category.
`vacuumBlockAction_total` identifies its action on each reservoir block.
`coefficientAction_output` extends this identification to every probe
module and every tensor vector. `coefficientAction_evenChart` is the
resulting arbitrary-even-chart square for raw `SYM D k` coefficients.
The paired consumer tests the square on arbitrary vectors and proves
that the output arrow of one odd colour acts nontrivially on a tensor
containing the other odd colour, using the asymmetric two-odd datum.

These declarations do not yet identify the direct path action with the
recursive normalized word action. To use the result at the actual
matrix observation, transport its base square through the original
weight equality, identify the target word-family coefficient by
`PowerWordCoefficients.coefficient_fromArrow`, and extend through
`chart_append_hom` and `append_family_arrow`. The evaluation on the
source chart inverse of the unit is then an application of the
whole-vector square. The observation square remains a separate proof.
