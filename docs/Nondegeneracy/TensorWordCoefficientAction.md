# Source coefficients on the normalized whole tensor word

`TensorWordCoefficientAction.wordAction` carries the original `SYM D k`
action on each full `TensorVacuumWords.wordHom`. Its empty-word action is
the direct empty reservoir-path action, transported through the proved
original-weight normalization and `pathHomAt_eq_wordHom`. Each append
step right-whiskers the whole supernatural map by the prescribed `elvE`
and transports it through the given whole-Hom append equality.

`wordAction_append` exposes that literal formula. All coefficient,
input-module and parity components remain part of the maps; no regular
probe is chosen in the construction. Because every step is an algebra
map, source multiplication order is retained without assuming ordinary
commutativity. `wordHomAction` acts on the entire Hom from an arbitrary
source functor by postcomposition with this same word action.

`wordAction_nil_ne_zero` proves that a nonzero coefficient endomorphism of
the initial whole tensor Hom remains nonzero under the empty-word
normalization. The paired consumer uses two independent odd colours in
the asymmetric datum. A source coefficient acting on a tensor containing
the other odd coefficient has nonzero ordered product in the literal
power quotient, so its whole-input action and its normalized empty-word
action are nonzero. The same consumer applies the algebra law and the
odd reversal sign at arbitrary words.

This supplies the full-input normalized word action needed by the
coefficient observation square. The equality under
`TensorVacuumWords.chart` with the signed original word-family
coefficient arrow remains to be proved, including its empty-word chart
normalization and compatibility with the direct arbitrary-path action.
No matrix-observation coefficient compatibility is asserted here.

The proposed chart argument uses the existing append square. At the
vacuum, combine `coefficientAction_regular` with
`PowerWordCoefficients.coefficient_fromArrow`, weighted descent and
restriction to identify the right side as the original coefficient
arrow on the empty word. Transport this square through the empty-weight
equality and the empty-path whole-Hom equality. At an append, expand
`chart_append_hom`: its local chart is the mapped old global chart
followed by `PowerWordWeight.weightAppendIso`. Map the preceding square
by `elvE`, then use `PowerWordWeightWhiskering.append_family_arrow` and
`append_coefficientEndomorphism`. The source coefficient remains inside
the same original ordered composition throughout. Relating this
recursive action to the direct arbitrary-path action then requires the
same whole-path induction as `pathHomAt_eq_wordHom`, now on maps.
