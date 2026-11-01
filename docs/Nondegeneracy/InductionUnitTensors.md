# Unit tensors for append comparisons

The scalar probe and weighted reservoir comparisons use the same two canonical composition-of-induction maps. `ELVInductionUnitTensors` extracts the unit formulas as public reusable declarations: `BalancedInduction.inductionComp_hom_total_unit`, `inductionComp_inv_total_unit`, and `moduleMap_total_tensor_even`.

The producer passes strict source compilation and the complete paired consumer, including its recursive axiom audit of all five owned declarations. The flattening argument applies the established double-tensor formula to two identity arrows and the functor identity law, then applies the explicitly typed identity-composition equality under the tensor map; unflattening is the established inverse tensor formula at an identity. The even module-map formula removes its zero odd component. No new comparison is assumed. Full repository gates remain pending.

The next applications compute the chosen scalar and weighted five-map append comparisons on units, then extend to all tensor generators through proved even naturality and the existing action roundtrip. Full generator, crossing and adjunction comparisons remain open until checked.

`BalancedInduction.composition_total_apply` gives total evaluation of five composable supernatural module maps with common intermediate module endpoints. This vertical-composition identity requires no evenness or action hypothesis. The subsequent `composition_total_apply_of_steps` computes such a chain from the five prescribed vector images using congruence, without dependent rewriting in the concrete modules. Both generic identities pass strict compilation within the complete source and its paired consumer. The scalar and weighted unit specializations remain unverified.
