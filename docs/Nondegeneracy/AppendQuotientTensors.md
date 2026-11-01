# Quotient/descent inverse unit tensors

The generator comparison in
[SwappedVacuumCoordinates §6](SwappedVacuumCoordinates.md) needs tensor
formulas for the canonical old/truncated comparison, in addition to
[its input-module naturality](WeightedInductionNaturality.md).

`quotientInducedWeightedModuleIso_inv_tensor` identifies the inverse
quotient-induction/descent comparison on every annihilated old module as
the literal quotient-induction unit tensor on the same vector.
`quotientInductionCounitIso_inv_total` similarly identifies the inverse
actual counit component with the existing unit.

Supporting total-component formulas for even natural isomorphisms and
`inducedIsoOfFunctorEq_tensor` expose the existing append/quotient
comparison without unfolding a concrete coend during functor-equality
transport. The latter keeps the required object equality morphism explicit.

The strict source and concrete consumer pass, with all twelve
owned-declaration axiom checks. The consumer applies the inverse formulas
to an actual truncated representable and retains a mixed-crossing vector
with an odd coefficient, proved nonzero at all sufficiently large cutoffs.
No replacement of the weighted ideal is used.

The entire append comparison's generator formula, chosen dot/crossing and
adjunction intertwining remain separate obligations. Full CI is required
before integration; see [STATUS](STATUS.md).
