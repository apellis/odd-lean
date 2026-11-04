# Separated mixed-bend series

The scoped checked result is `Sigma/BendSeriesAlgebra.lean`, together
with `scripts/NonVacuity/BendSeriesAlgebra.lean`: inverse evaluation,
the sign of consecutive negated monomials, and both residual-series
scalar conventions. The producer and consumer pass strict checks;
all nine owned declarations use only the standard allowed axioms.
The categorical monomial evaluation in `Sigma/BendWindowMonomials` and
its nonzero module consumer also pass strict scoped checks, auditing all
three owned declarations. `Sigma/SeparatedBendSeries.lean` now assembles
the four separated series, and `Sigma/BendWindowEquations.lean` states
them as the literal signed equations. Both producers and the concrete
`ELVProbeSeparatedSeries` consumer pass strict scoped checks. The consumer
audits all 93 declarations owned by the former module and all 41 owned by
the latter, with only `propext`, `Classical.choice` and `Quot.sound` allowed.

The target of `Sigma/SeparatedBendSeries.lean` is the pair of literal
series in `CentralInverse/ResidualComparison.lean`:

\[
D=-\sum_r q^{r+1}x^{-r-1}vu_R(r),\qquad
C=\sum_r q^{r+2}v_R(r)uy^{-r-1}.
\]

Composition in Lean is chronological. The maps `v` and `u` are the
normalized probe counit and unit. The reservoir windows are
`homContentPostCup` and `homContentPostCap`. The automorphisms use the
raw invertible probe dot and its image under the prescribed right
adjoint, followed by the chosen output evaluation. No transposed dot
or alternative probe family is substituted.

The proof has three distinct inputs. `Sigma/BendDotCoordinates.lean`
identifies the two dots in each actual coefficient chart. The RP chart
preserves the dots; the PR chart multiplies both by `q`.
`RouquierHomBendMonomials.lean` separates the ordered raw monomial into
the dotted cap and cup. `Sigma/BendSeriesAlgebra.lean` converts the
resulting signs into the exact integer powers above.

For the odd PR chart, negating both dots negates the monomial because
its exponents are consecutive. The alternating coefficient series
then meets the prescribed minus in the PR bend. The resulting scalar
is `(-1)^(r+2)`. For the RP bend the scalar is `-(-1)^(r+1)`.
The arithmetic is valid in noncommutative endomorphism rings, including
zero corners. Its concrete consumer uses noncommuting rational matrices.

`Sigma/BendWindowMonomials.lean` verifies that evaluating the ring
inverse gives the image of the specified probe automorphism's inverse.
It also evaluates the ordered monomial without changing its order.
The finite bound is imposed only on the evaluated reservoir dot.
For each output component, the ELV construction supplies that bound
from the source content read by the appropriate lowering functor.
There is no finite bound on a whole weight fibre and no restriction to
regular input modules.

The generic four `*_even_windows` and `*_odd_windows` declarations
retain a chosen coefficient and its inverse equations, a probe-dot
isomorphism, and the evaluated reservoir-dot bound as construction
inputs. Canonical specialization supplies these from the specified
ELV probe/reservoir pair and its constructed coefficient. When a common
truncation index for both bends is needed, take a common upper bound of
the two component nilpotence exponents before applying these formulas.
