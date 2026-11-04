# Mixed-window equations at an additive output

`Sigma/BendWindowEquations.lean` names the two equations required by
`CentralInverse/ResidualComparison.lean`. For an arbitrary additive
output functor, `ProbeToReservoirSeparatedAt` is the literal
`-∑ q^(r+1) • (x^(-r-1) ≫ v ≫ uR r)` equation, and
`ReservoirToProbeSeparatedAt` is the literal
`∑ q^(r+2) • (vR r ≫ u ≫ y^(-r-1))` equation.

Here `q` is the parity sign of the selected colour. The probe
automorphisms are the evaluated raw dot and its image under the
prescribed right adjoint; the cap and cup are the normalized
adjunction maps. The coefficient and both mixed bends are the ones
already specified by the probe/reservoir pair.

The four `*_even_separated` and `*_odd_separated` theorems supply
these equations from the checked separated series. Their inputs are
the chosen coefficient's inverse equations, invertibility of the
probe dot, and a nilpotence exponent for the evaluated reservoir
dot. The even equation uses that exponent as its range; the odd
equation uses twice the exponent. The named predicates introduce no
additional assumption and unfold to the displayed equations.

Both evaluation at a probe module and projection to a whole
output-content category are allowed. For the latter, one exponent
at each fixed reservoir content must work for every probe input.
This still requires no uniform exponent over an entire weight fibre.

Both generic producers and the concrete `ELVProbeSeparatedSeries`
consumer pass strict scoped checks. Its four applications use the
constructed coefficient, its inverse equations, the whole probe unit,
and derived output nilpotence bounds at both parities. The consumer
audits all 93 declarations owned by `SeparatedBendSeries` and all 41
owned by `BendWindowEquations` against the standard axiom allowlist.
