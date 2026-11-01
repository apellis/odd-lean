# Actual module units for the old append dot

`ELVProbeOldDotUnit.lean` maps a relative word corner to actual
endomorphisms of the word-idempotent subspace of a probe module. This is a
unital ring homomorphism: the corner unit acts as the identity on that
subspace.

`probeOldAppendDot_action_isUnit` applies it to the exact checked scalar
image of the actual `oldAppendDotComponent`. The resulting old-category
module component is therefore an actual End unit, in both parities and at
every height, including append from the vacuum. No unit hypothesis on that
module map is supplied.

Strict local producer and all four closed concrete consumers pass. The
consumers use the actual regular probe modules, odd/even appended dots and
both vacuum and mixed positive content. All 22 owned declarations pass
the axiom audit. Full CI remains the integration gate.

Transport of the prescribed induction-dot transform and the inverse-matrix
comparison remain separate. This does not identify an ordinary probe coefficient
evaluation with a weighted coefficient truncation.
