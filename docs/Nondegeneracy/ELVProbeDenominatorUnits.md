# Mixed denominators on the OLD-probe and ELV-reservoir pair

SwappedActionAssembly F2–F3 and (A6) require the mixed crossing entry on the
specified factor pair. `elvProbe_rpObj`, `elvProbe_rpPreDot`, and
`elvProbe_rpPostDot` identify its literal RP carrier and chosen dots with the
shifted ELV induction, inner probe dot, and outer reservoir dot. These are
identities of the chosen operators, including the prescribed shift.

`elvProbeCrossDenominatorUnits` constructs both denominator units on that pair:
the even difference and odd difference of squares. It uses the whole OLD-probe
dot unit and the existing reservoir bounds at individual content components.
No uniform nilpotence exponent over a weight fibre is assumed.

`elvProbeCrossCoeff` is the crossing coefficient selected from these denominator
units. `elvProbeCrossCoeff_isInverse` proves its even inverse and odd
square-denominator identities. `elvProbeCrossCoeff_even_expansion` and
`elvProbeCrossCoeff_odd_expansion` evaluate its literal `c.a` entry at one input
object and reservoir block. They construct a nilpotence bound at that component
and identify the result with the finite ordinary or signed ordered series.
Neither theorem asks for a coefficient, inverse identity, or reservoir bound.

The paired consumer uses a two-colour mixed-parity datum and an asymmetric
all-odd datum, applies both denominator and coefficient identities, and checks
nonzero scalar-probe vacuum vectors. It also applies the two finite expansion
theorems to the mixed-parity pair, applies the odd expansion with asymmetric
parameters, and audits all declarations in the module.

These statements construct the mixed crossing coefficients. Finite bends and
the complete swapped action remain separate assembly obligations.

The declarations and paired consumer await their scoped checks against the
complete probe-factor constructor.
