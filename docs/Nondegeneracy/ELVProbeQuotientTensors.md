# Tensor formulas for the chosen scalar quotient comparison

`ELVProbeQuotientTensors.lean` computes the already constructed scalar quotient induction comparison, retaining its exact chosen equality isomorphism. That equality contributes the identity in parity zero and zero in parity one. The inverse quotient counit is the canonical unit tensor at the identical old word.

`probeQuotientInducedModuleIso_inv_tensor` proves that the chosen inverse comparison sends the same actual old module vector to `[id ⊗ vector]` in quotient induction. The proof uses the existing module-map tensor formula and the actual counit; it does not assume a comparison action on tensors. A small opaque identity-plus-zero tensor lemma keeps endpoint metadata out of the concrete normalization.

Strict local producer and every closed consumer pass; all 16 owned declarations pass the axiom audit. Consumers use the actual canonical mixed-colour probe module, its proved scalar evaluation, both equality-isomorphism components and the canonical inverse tensor. Full CI remains the integration gate.

The whole append-comparison generator formula and its prescribed dot/crossing intertwining remain separate. No ordinary-to-height tensor identification or weighted coefficient-truncation specialization is asserted.
