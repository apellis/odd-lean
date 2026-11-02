# Scalar append comparison on generators

**Proposed specialization, not a verified result.** The shared commuting-square
tensor calculation is scoped-checked separately. The scalar specialization and
its mixed/vacuum consumer below remain unverified; endpoint normalization is
still needed where the square's output vector enters the scalar module.

The comparison in `probeAppendOrdinaryModuleIso` is the prescribed composite:
inverse quotient counit, flattening of balanced induction, the literal
append/specialization square, unflattening, and induction of the scalar
quotient counit. `ELVProbeAppendTensors` computes this composite on every
old coend generator, advancing the ordinary-probe transport obligation in
STATUS's remaining critical chain item 3 and the prescribed action maps in
DeformedActionAssembly §§5–6.

The intermediate four maps are evaluated by
`BalancedInduction.squareComparison_total_tensor`, before specializing the
category endpoints. The inverse quotient comparison inserts the outer unit
tensor. The middle comparison sends the inner old arrow to its literal scalar
image. The final quotient counit cancels its inner unit tensor. Thus
`probeAppendOrdinaryModuleIso_hom_tensor` sends
`[g ⊗ b]` to `[U.map g ⊗ b]` in the selected ordinary append coend, for arbitrary
old arrows and arbitrary module vectors. In particular,
`probeAppendOrdinaryModuleIso_hom_unit` intertwines the chosen append units.

`probeAppendOrdinaryModuleIso_hom_dot` applies this generator formula to the
prescribed signed dot transforms. The source-arrow identity uses the scalar
image of the literal old appended dot and preservation of the full parity
twist. The statement includes odd moving colours and inhomogeneous coend
arrows; no finite-dimensionality assumption is introduced.

The paired consumer uses actual scalar-evaluated regular probe modules on
mixed two-colour content and on the vacuum, with both append parities. The
mixed case additionally checks the full tensor formula and dot intertwining.
The scalar coefficient is nonnilpotent (`e(false,0)` specializes to `−3`),
while the odd coefficient specializes to zero. These results do not assert
faithfulness of scalar specialization on the full coefficient algebra.

The selected comparison's crossing, normalized cap and matrix-inverse
transport remain separate. Unit and dot compatibility alone do not construct
the probe factor action or the full exterior-coefficient reservoir.
