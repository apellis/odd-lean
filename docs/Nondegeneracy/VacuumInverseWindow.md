# The chosen inverse on the vacuum unit window

This supplies the inverse-normalization step in
`SwappedVacuumNonpositiveBubbles` §1 (2) and §4 (13).
Let `P` be the prescribed OLD probe / truncated ELV reservoir pair, and
let `Z` be any supported input at the formal sector `(0,0)`. At every
output content, the reservoir source corner and probe target corner are
zero. The negative augmented factor matrix therefore reduces to the
mixed bend and reservoir unit columns. This uses the actual chosen
central coefficient and its proved augmented inverse.

In `CentralInverse/VacuumWindow`, the matrix equation gives all five
unit-inverse identities after deleting those two zero corners. For the
signed negative matrix, write `J` for its inverse. The inverse of the
positive mixed bend `Dx` has principal

```
j = -J none (some none)
B n = J none (some (some n)).
```

Thus the finite cap rows carry no additional sign. The theorem
`negMap_isCupInverse_of_zero_corners` derives this from both matrix
inverse equations; `negMapCupInverseData` packages the five identities.
The generic consumer has a nonzero unit-window row over `ℚ`.

`Sigma/VacuumInverseWindow` applies this to the prescribed supported
pair without assuming an inverse or any bubble moment:

- `vacuum_height_eq` computes the height as `probeCutoff i - cutoff i`.
- `vacuum_negative_window_length` computes the window length as
  `cutoff i - probeCutoff i`.
- `vacuumCupInverseData` supplies the positive mixed-bend unit inverse
  at every output content when that height is nonpositive.
- `vacuumCupInverseData_window` identifies every finite row with the
  corresponding entry of the chosen negative factor inverse.
- `vacuum_negative_inverse_square` identifies the whole inverse factor
  matrix with the source/target chart transport of the evaluation of
  `inv (augNegMat ...)`, retaining the original path indices.
- `vacuumPrincipalIso` gives the positive mixed-bend isomorphism at
  height zero, with that same chosen principal inverse.

The concrete consumer uses the tensor vacuum for a symmetrizable datum
with two odd colours and colliding root weights. It checks height zero
and height minus two, both slots of the latter finite window, the exact
row normalization and the inverse comparison square. The fixture also
retains a proved nonzero supported two-odd coefficient vector.

## Remaining scalar comparison

These declarations do not yet identify the evaluated padded mixed bend
with `ELVOld.ProbeVacuumCap.evaluatedMixedBend`. The latter uses the
finite-local `localPreSuperAdjunction`; the former uses the normalized
left adjunction of the whole-weight `probeOldRouquierFamily`.
`ELVProbeRouquierCap.localLeftCounit_preCap_eq` computes the local
signed counit as `shiftedPreCap`, and
`evaluatedMixedBend_constructed_counit` inserts precisely that counit.
The remaining comparison must transport the whole-weight inverse-defined
cap to this local cap, then match the reservoir append unit and both raw
dots under the endpoint charts. Equality of inverse rows follows from
inverse uniqueness only after their forward maps have been identified.

After that comparison, the checked tensor polynomial-cap vanishing
(`ELVTensorVacuumPolynomialCap`) and height-zero principal equation
(`ELVTensorVacuumPrincipalCap`) can be applied to the chosen inverse.
`SwappedVacuum/NegativeCapInverse.negative_inverse_cap_eq_polynomial`
then identifies the negative-height extreme row, while the height-zero
principal identity supplies the inverse-mate normalization in
`SKM/CoupledBubbleEvaluation`. No scalar comparison or resulting actual
bubble value is asserted by this module. The distinction between the
algebra generator and the signed raw dot is retained exactly as in
`SwappedVacuumBubbles` §3, equation (5).
