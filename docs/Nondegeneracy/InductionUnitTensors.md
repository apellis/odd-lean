# Unit tensors for append comparisons

The scalar probe and weighted reservoir comparisons use the same two canonical composition-of-induction maps. `ELVInductionUnitTensors` extracts the unit formulas as public reusable declarations: `BalancedInduction.inductionComp_hom_total_unit`, `inductionComp_inv_total_unit`, and `moduleMap_total_tensor_even`.

This producer and paired representable-module consumers are unverified drafts. The flattening argument applies the established double-tensor formula to two identity arrows and the functor identity law; unflattening is the established inverse tensor formula at an identity. The even module-map formula removes its zero odd component. No new comparison is assumed.

The next applications compute the chosen scalar and weighted five-map append comparisons on units, then extend to all tensor generators through proved even naturality and the existing action roundtrip. Full generator, crossing and adjunction comparisons remain open until checked.
