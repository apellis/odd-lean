# The zero lower cell at the empty module boundary

The empty boundary of BE (1.14) retains the native module parity target.
`ELVModuleZeroBoundary` constructs its lower zero cell within
`inductionModulePiCategory C`, using the Empty-indexed finite module product
as the zero module and the constant additive, linear superfunctor on it.
No lower zero category is introduced.

`zeroModuleCell_id` proves the identity of this cell is zero.
`zeroModuleCell_comp_id` proves the same after postcomposition by any
superfunctor into a parity category: additivity sends the zero module's zero
identity to the zero identity of its image. Consequently
`zeroModuleCell_whiskerLeft` kills every transformation whiskered after that
lower cell, including the chosen upper dot needed for boundary slides.
`zeroModuleCellAdjunction` supplies the even zero unit and counit; its two
triangles use the proved zero cell identity.

The exact producer and occupied paired consumer pass strict scoped Lean
checks. All 19 owned declarations, including private and generated ones,
pass the standard axiom audit. The consumer uses the asymmetric
all-odd probe at positive cutoff, proves the same ambient category contains
the nonzero regular empty probe, and postcomposes the lower cell with the
given append induction. It also checks the actual odd append-dot slide and
both adjunction triangles. Full repository CI remains the integration gate.

This supplies the zero lower fields of the empty local Rouquier datum.
The upper fields and their inverse identities must still be attached to the
constructed native module inverse; they are not assumed in this module.
