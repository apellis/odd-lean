# Integer degree of the chosen reservoir closures

The closure dependency G8 uses the principal inverse selected by the
reservoir Rouquier family, between an ordinary unit with `r` dots and an
ordinary cap with `s` dots. The source coefficients carry integer degree;
arbitrary module morphisms do not need an integer grading.

The comparison proceeds through the following specified coordinates.

1. `positive_content_coordinates` and `negative_content_coordinates`
   identify the chosen weight closure with its content unit, principal
   inverse and cap on each supported output block. The principal square
   follows from inverse uniqueness. The unit and cap use the same weight
   source and target equations, so the intermediate coordinates cancel.
2. `contentTargetsCapClosure_coordinates` and
   `contentTargetsUnitClosure_coordinates` pass the content closure
   through the selected full-inclusion charts. The value chart is the
   content extension unit. The source and target charts cancel between
   the prescribed forward fields and the forced principal inverse.
   `positive_weighted_coordinates` and `negative_weighted_coordinates`
   compose these comparisons for the actual chosen closures.
3. The weighted matrix inverse, after removing its named parity and
   value charts, is the represented OLD kernel inverse. The raw principal
   inverse raises integer degree by `2 dᵢ`. The dotted unit and cap
   contribute `2 dᵢ r` and `2 dᵢ s`.

`positiveRepresentedValue` and `negativeRepresentedValue` are the
coefficient-truncated raw closures evaluated at the OLD identity of the
given word. The weight and content height signs are opposite. Both
represented values lie in degree `2 dᵢ (r+s+1)`, which is strictly
positive because the symmetrizer entries are positive.

The extension-unit chart is even. Its naturality therefore returns a raw
coefficient action to the original content module without a Koszul factor.
Evaluation on content representables recovers the two parity components
of the source coefficient. Parity projections preserve the independent
integer degree. Output blocks without a predecessor have zero closure,
since the chosen principal factors through the zero lower induction
component.

`positiveCoefficient_mem_degree` and `negativeCoefficient_mem_degree`
state the degree of the reconstructed coefficients of the literal chosen
closures on every output block. Together with the existing
`positiveCoefficient_total` and `negativeCoefficient_total`, these give
the required coefficient witness acting on every whole-weight input.
Their hypotheses are the cutoff/highest-weight match, a symmetrizer,
homogeneous parameters, and the corresponding height sign.
