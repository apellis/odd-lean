# Coefficient maps on the power vacuum

This supplies the coefficient module maps and their signed source-word whiskering needed by `SwappedVacuumCoordinates.md`, §6. Write A for the old coefficient algebra and T for the literal elementary-power ideal.

`ELVOld.coefficientModuleAction` is an algebra map A → End(M) for every old supermodule M. It uses both homogeneous projections of a coefficient to construct a supernatural transformation. `coefficientModuleAction_app` retains these projections, `coefficientModuleAction_total` recovers the original old coefficient endomorphism at every word, and `coefficientModuleAction_mem` preserves homogeneous parity. In particular, odd coefficients are odd module maps.

The multiplication order is explicit. The old category has e(b) ≫ e(a) = e(ab); endomorphism multiplication also reverses categorical composition. These reversals yield the original product ab in the algebra map. Ordinary commutativity of A is never assumed.

`powerModuleCoefficientAction` descends this map to A/T for every object of the literal T-annihilated module category. `vacuumCoefficientAction` specializes to the regular power vacuum. Its chosen empty-component coordinates satisfy

    vacuumCoefficientAction(a)(E(z)) = E(a*z)

for arbitrary quotient coefficients a and arbitrary vectors z, including inhomogeneous elements. The descent uses the proved annihilation ideal, with no assumed evaluation kernel.

For any old endofunctor J used in balanced induction, `coefficientModuleAction_induction_tensor` gives the signed source-word formula for homogeneous a of parity p:

    Ind(J)(coefficientModuleAction(a))(h ⊗ m)
      = twist_p(h) ⊗ M(e(a))(m).

The entire kernel h is twisted. An odd coefficient does not act by unsigned tensoring on the input vector.

The paired consumer uses independent occupied odd generators at cutoffs four and five. Their product is nonzero in A/T by the coefficient-window injection and exterior basis. It checks the coefficient algebra map, odd module-map parity, exact all-vector and inhomogeneous empty actions, and the source-whisker formula on an independently odd append kernel. Its audit covers every declaration owned by the producer.

This does not yet identify a swapped bubble with this coefficient module map, or construct the probe numerator. Those attachments still require the chosen swapped cup/cap and source-word charts.
