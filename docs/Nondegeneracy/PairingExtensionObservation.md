# Observation equations under pairing extension

For the original-datum action obtained by pulling back along
`μ ↦ (μ, 0)`, the declarations
`UpwardModuleAction.restrictPairingExtension_upAct` and
`UpwardModuleAction.restrictPairingExtension_bubbles` identify the upward
and source-placed coefficient actions with those of the extended model.
They use the exact affine presentation map and the coefficient algebra
isomorphism from `PairingExtensionComparisons.md`.

`PairingExtension.coefficientEquiv_basis` retains every polynomial/exterior
basis index. Its `coefficientEquiv_mem_atMost` and
`coefficientEquiv_mem_atLeast` consequences preserve the two coefficient
filtrations in `SwappedVacuumCoordinates.md` §7. These are coefficient
filtrations only: joint affine degree and power-quotient kernel transport
are separate obligations. No vacuum/corner observation or nondegeneracy
constructor is asserted here.

The paired consumer constructs the extended supported action from the
explicit parameter schedule with mixed parity and a nonzero coroot-kernel
weight coordinate, then applies both action equations. Its coefficient
has nonzero polynomial and exterior components and weight two; both
filtration bounds and nonzero probe append vectors are proved. The source
and consumer pass scoped strict checks and an audit of all owned
declarations against the standard axioms.
