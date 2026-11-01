# Scalar quotient and ordinary append induction

`ELVProbeQuotientInduction.lean` constructs the actual old-to-ordinary append induction comparison needed for the invertible-dot probe action. The ordinary category is the existing literal cycHom quotient. Its scalar functor is full, and the previously proved scalar-kernel closure is applied to the actual old balanced append induction before descending that module.

`probeQuotientCounitIso` gives the quotient-induction counit as an even module isomorphism. Its inverse is the existing unit at the identical source word; fullness supplies the reverse inverse identity. `probeQuotientInducedModuleIso` uses the exact restriction identity of the descended scalar module. Finally `probeAppendOrdinaryModuleIso` composes these counits with the existing induction-composition isomorphisms and the literal append/scalar quotient square.

This compares the actual old append coend with the actual ordinary quotient append coend; it does not identify either with a height-algebra tensor product. No finite-colour, finite-dimensionality, flatness, integer-grading or weighted coefficient-truncation specialization is asserted.

Strict local producer and every closed consumer pass; all 46 owned declarations pass the axiom audit. Concrete mixed-parity consumers use the actual canonical probe module, its proved scalar evaluation and both append parities. Full CI remains the integration gate. Prescribed dot/crossing transport and the ordinary-to-height comparison remain separate.
