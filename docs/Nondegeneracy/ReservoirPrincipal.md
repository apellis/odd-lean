# The actual reservoir principal matrix entry

The source `Sigma/ReservoirPrincipal` continues the reservoir cap/unit
comparison in [ReservoirDottedFactorCoordinates](ReservoirDottedFactorCoordinates.md).
It treats the actual same-colour `sigmaEntry` on the pure reservoir
paths, with arbitrary full Hom object and arbitrary probe content. The
raising reservoir path requires positive reservoir content, exactly its
existing `StepValid` condition.

Producer and occupied consumer pass strict scoped checks with warnings
as errors and both backward transparency flags disabled. The consumer
audits all 27 producer-owned declarations against the standard axiom set.

The proof uses the existing general `sigmaEntry_eq_sigmaTerm` to collapse
the actual sum and `sigmaTerm_eq_of_paths` to expose its three generator
entries. The cup and cap are the specified shifted postcomposition unit
and counit. The pure crossing is `postCrossSame`, hence the prescribed
`homContentPostCrossingApp`; the mixed coefficient is unused.

`reservoirCapFactorIso` and `reservoirCupFactorIso` provide the fixed
endpoint, inner-object, and return transports. The comparison
`sigmaEntry_reservoir_mate` identifies the actual entry with the native
mate for those two shifted adjunctions in these charts. A normalized
transport argument eliminates computed weight/object equalities before
instantiating them in the path functors. It assumes no equality of the
operators being compared.

The coordinate square then removes both parity shifts using the existing
`homContentPostCrossing_principal`. Its value is the literal factor map

    associator ; (Z ◁ (W.loc i lowerEdge upperEdge).sig) ; inverse associator.

Both selected adjunctions and the original factor crossing are retained.
The positive principal block uses this sign; the negative augmented map
still has its separately prescribed minus sign.

The paired consumer constructs complete positive-level asymmetric
two-odd ELV factors and tests both comparisons at both colours. Its
identity Hom has an input containing an independently surviving product
of the two odd coefficient classes. The zero mixed coefficient is data
only; no inverse property is asserted. These occupied factors test the
literal comparison and are not the intended unit-dot probe.

This supplies the reservoir principal block, in addition to the already
checked all-exponent reservoir cap/unit rows. The probe principal block,
both mixed diagonal bends, complete matrix chart square, boundary zero
corners, and residual coefficient-ideal memberships remain separate
obligations. No full-weight uniform nilpotence bound is inferred.
