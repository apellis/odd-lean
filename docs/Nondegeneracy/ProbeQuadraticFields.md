# Exact quadratic fields for the bundled OLD probe generators

Brundan–Ellis (1.7) is proved in the exact `RouquierMulticolour.quadZero`
and `quadNe` formats by `ELVProbeQuadraticFields`.
`probeOldRouquierData_quadZero` and `probeOldRouquierData_quadNe` use the
actual bundled `probeOldRouquierData D (parameterTwist D Sc) m Λ`, including
its `.cross`, `.E` and `.dot` fields. `probeOldActionCross_distinct` retains
the bundled crossing while selecting its proved positive distinct branch.
The connected field has the literal ordered whiskered `rouquierPower`
terms and interior sum, with the original parameters `Sc`.

These are corollaries of the whole-weight original-parameter quadratic.
They assume neither an action relation nor a multicolour record. No record
with missing presentation fields is constructed.

The exact producer and concrete consumer pass strict checks with warnings
as errors and both compatibility settings. All ten owned declarations pass
the axiom allowlist. The connected examples cover both orders of a mixed
pair with a nonzero interior coefficient, nonempty and occupied vacuum
weights, and the asymmetric two-odd datum. The disconnected examples use
two odd colours with the original off-diagonal unit parameter equal to 2,
check both orders, and retain an independently nonzero regular probe vacuum
vector. Thus the disconnected branch is tested alongside the connected
interior polynomial rather than as the sole example.

These equations are available for the eventual complete multicolour
presentation. The remaining presentation and local inverse obligations
are separate and are not inferred from the quadratic fields alone.
