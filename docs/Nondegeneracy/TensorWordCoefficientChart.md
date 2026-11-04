# Tensor word charts and source coefficients

`TensorWordCoefficientChart.chart_square` is the global prescribed-chart
square for the full original `SYM D k` source action on each normalized
whole tensor word. Under `TensorVacuumWords.chart`, it is the existing
signed `wordFamilyArrow` of `coefficientEndomorphism` on that word.
`chart_square_apply` specializes the same equality to every vector and
every actual output content block.

The empty-word step uses no comparison between chosen initial charts.
`wordAction_nil_output` transports the full output coefficient identity
through the empty path and its endpoint normalization. Every even module
chart intertwines the output coefficient arrow, even when the source
coefficient is odd or inhomogeneous. `wordFamilyArrow_total` identifies
the target coefficient arrow with this output action, using the original
`coefficient_fromArrow` theorem and literal weighted descent.

The append step maps the preceding square through the prescribed
`elvE`, follows it by `weightAppendIso`, and applies
`append_family_arrow` and `append_coefficientEndomorphism`. The local
append chart is the mapped global preceding chart followed by this
append comparison. `chart_append_heq` and `wordAction_append_heq`
transport the resulting square to the normalized whole word.

The paired consumer applies the square to the asymmetric two-odd datum,
including a nonzero odd empty-word action detected on a tensor
containing the other odd colour. It applies the full-vector theorem to
arbitrary words and a mixed-parity source coefficient. Relating the
result to the canonical original-row observation additionally uses the
direct path-action comparison and the actual path/global-chart
comparison. No generator-detection or injectivity statement follows
from this square alone.
