# Even input comparison and dotted counit rows

This supplies the even-colour actual-map attachment in
[DeformedMatrixComparison §4](DeformedMatrixComparison.md).
It uses the canonical coefficient(0) source from
[EvenCoefficientModule](EvenCoefficientModule.md) and the unchanged raw
operators of [EvenInputOperators](EvenInputOperators.md).

`evenSourceInputDot` is the actual induction dot on the existing even-moving
coefficient module. Its tensor formula retains every coefficient. The
theorems `evenSourceInputContraction_eq` and `evenSourceInputDot_eq` identify
the canonical negative ordinary counit and this induction dot with the
prescribed raw even input operators, on every balanced class.

`evenSourceInputDot_sourceEquiv` proves that the canonical even source
comparison intertwines the ordinary actual induction dot, with no parity
conjugation. Iteration gives `evenSourceInputDot_iterate_sourceEquiv`.
Finally `evenCapRow_normalization` proves for every row n:

\[
E_0 X_0^n J_0=-\varepsilon T^n.
\]

Thus the minus is constant in every even row; neither an odd cap scalar nor
a whole-output twist occurs. The separate even self-colour leading unit
is unchanged.

The source and concrete consumer pass strict scoped checks and all nine
owned-declaration axiom checks. The consumer retains the nonzero mixed
crossing with an odd coefficient of the other colour, tests both operator
equalities on arbitrary balanced classes, and applies the normalization at
all row indices, including zero. Full CI is required before integration.
The actual ordered crossing mate and shifted module-family assembly remain
separate obligations; see [STATUS](STATUS.md).
