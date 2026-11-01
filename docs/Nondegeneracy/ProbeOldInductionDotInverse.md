# Old coend probe dot inverse

The probe-unit roadmap needs the prescribed signed dot on the untruncated old append coend. `ELVProbeOldInductionDotInverse` constructs its inverse from the inverse ordinary appended dot, the scalar Hom action on unchanged old induced module values, and the original balanced quotient. The inverse uses the parity-square factor `sign k (D.parity i * D.parity i)`.

`probeOldContentInductionDotInverse_tensor` gives the signed inverse on old coend generators. `probeOldContentInductionDotInverse_comp_dot` and `probeOldContentInductionDot_comp_inverse` prove both inverse products. Their intermediate unit, `probeOldContentInductionDotUnit`, assumes scalar coefficient evaluation of the old module. `probeModuleOldInductionDotUnit` and `probeModuleOldInductionDot_isUnit` discharge that condition for the prescribed `probeOldModule` coming from any ordinary probe height super-bimodule.

The producer and paired consumers pass the scoped strict check, including the recursive audit of all 80 owned declarations. The consumers use the canonical regular ordinary probe modules, mixed lower content, empty lower content, and both moving parities. Full repository CI remains the integration gate.

The proof uses scalar-evaluation closure of old induction, not scalar evaluation of a weighted coefficient truncation. It needs no finite-dimensionality, flatness, or selected coend-comparison premise. The chosen ordinary content probe model is unchanged. Its selected whole append-comparison generator formula and crossing/adjunction comparisons remain separate obligations; this result establishes only the old signed-dot unit input.
