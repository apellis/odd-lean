# Actual ordinary counit/dot rows as ordinary-right coefficient-kernel maps

`ELVCapKernelNaturality.actualDotKernel`, `actualCounitKernel` and `actualCapKernel` are natural maps on the concrete ordinary-right IndRes coefficient presheaf. Their covariance holds for every old source arrow a, including inhomogeneous arrows, acting on the coefficient by b ↦ a composed with b.

The dot component is the fixed actual induction dot transported through the literal source-kernel carrier equivalence. `actualDotKernelComponent_pow_apply` proves compatibility for every dot power. The counit is the chosen actual ordinary adjunction counit; `actualCapKernelComponent_moduleCapRow` identifies every row literally with the existing moduleCapRow.total, using exact checked MatrixEntryTotals e827ad65. No replacement operator or matrix equality is assumed.

The complete producer and three closed mixed-endpoint consumers passed strict local checks, covering both moving colours, every power n, arbitrary inhomogeneous source arrows and the actual module-row bridge. All 27 owned declarations, including private/generated, were audited. Full branch CI is pending.

Scope: these are ordinary-right underlying kernel maps. The finite normalized matrix, its fixed-content height multiplicity and grading, and the arbitrary-supermodule tensor realization remain subsequent attachments. No flatness, projectivity, field or all-module matrix isomorphism is asserted here.
