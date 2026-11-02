# The power quotient sandwich after the actual ELV coefficient quotient

This specializes [CoefficientPowers](CoefficientPowers.md) to the actual
full ELV coefficient algebra and instantiates the category functors in
[CoefficientPowerComparison](CoefficientPowerComparison.md). It supplies
the power/weight bridge of [SwappedNondegeneracy, §2](SwappedNondegeneracy.md).
The producer and paired concrete consumer pass scoped Lean checks with
warnings as errors and both pinned compatibility settings. All nine owned
declarations pass the standard axiom allowlist audit. Full CI remains the
integration gate.

Let q:SYM->A be the actual ELV coefficient quotient, with kernel ideal J.
`elementaryCoefficients(a)` is q(e_a), proved even. For powers L_a put

    T=span_two_sided {q(e_a)^L_a} in A.

If every L_a*weight(e_a) is at least N, then
`elementaryPowerIdeal_le_weighted` proves T contained in the actual
`coefficientWeightedIdeal(N)`. The proof sends each universal homogeneous
high-weight span through q, retaining odd monomials and scalar coefficients.

For finite colour support, put

    R=sum_(surviving elementary keys a) (L_a-1)*weight(e_a)
      + number of independent odd colours.

`weighted_le_elementaryPowerIdeal` proves W_(R+1) contained in T in A.
It uses the verified universal high-monomial bound in J plus the universal
power ideal. The first ideal maps to zero under q; each generator of the
second maps to the literal generator q(e_a)^L_a. No quotient normalization
or equality of the power and weighted ideals is assumed.

## The actual module functors

`elementaryWeightedToPower` and `elementaryPowerToWeighted` instantiate
the previously constructed literal category functors, giving

    weighted(N)-modules -> T-annihilated old modules
                        -> weighted(R+1)-modules.

Their ideal-containment hypotheses have been discharged. The first functor
retains the explicit numerical lower-weight inequalities; the second uses
the proved finite bound without an additional ideal premise. All vector
spaces, homogeneous map components and the prescribed maps of transported
isomorphisms are unchanged. These module directions are contravariant to
the quotient-algebra arrows.

The consumer uses the connected all-odd two-colour datum at cutoff four,
with fourth powers of the actual even elementary generators. It verifies
W_39 contained in T contained in W_4 inside A, constructs the resulting
module functors on the actual weighted-empty representable, and checks
both the odd parity comparison and its inverse on literal components.
This consumer uses the paper's even-power family, rather than the auxiliary
weighted-generator fixture of the generic comparison note.

## Boundary

The sandwich does not identify its three quotient algebras. In particular
it gives no new injectivity statement after imposing a further quotient.
Identification with literal quotient-algebra module categories, complete
generator/crossing coherence and the actual vacuum evaluation-kernel
identification remain separate. The all-height swapped bubble theorem
still requires its concrete factor and prescribed mixed inverse maps.
