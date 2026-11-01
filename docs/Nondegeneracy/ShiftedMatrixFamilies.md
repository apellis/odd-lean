# Shifted finite matrix families

The parity profiles of SKM.SuperSumInvFrom and SuperSumInvTo
(RouquierData.lean, implementing Brundan--Ellis Definition 1.5) specify
actual even rows and columns after canonical parity transport.
ELVShiftedMatrixFamilies constructs these entries on the existing old
module category, for every moving colour and every old supermodule M.

For the unit-column profile, unitMatrixFamily has finite index Option(Fin m):
the first source is Pi^p(Ind Res M), the other sources are Pi^(r p)M,
and the target is Res Ind M. unitMatrixEntry uses the degree-p component
of the constructed ordered mate in its first position and the ordinary
unit/induction-dot power in the other positions, preceded by the canonical
source parity isomorphism. These are unscaled ordinary unit columns;
the scalar d_r used by the polynomial-coordinate comparison is not
silently absorbed into these maps.

For the cap-row profile, capMatrixFamily has first target Pi^p(Res Ind M)
and remaining targets Pi^(r p)M, with source Ind Res M. This is the
equivalent profile obtained after removing the common source shift
from DeformedMatrixComparison section 4. capMatrixEntry uses the actual
mate component and ordinary induction-dot/counit powers, followed by
canonical target parity transport.

unitMatrixEntry_mem and capMatrixEntry_mem prove that every entry is
even. All maps are supernatural module maps by their constructed types.
inductionDotModule_total and inductionDotModule_power_total identify the
module dot and its powers with the same raw component operators used in
the checked ordinary unit/cap comparisons.

The producer and concrete consumer pass scoped builds with warnings as
errors. The mixed-parity asymmetric datum instantiates both moving
parities, every entry of the three-coordinate family, the zero-length coefficient family,
actual module-dot powers, and the literal odd/even source/target shift
profiles. All twenty-nine owned declarations pass the consumer audit.
Full CI and the global audit remain integration gates.

No finite-biproduct inverse or mate-versus-balanced-crossing identity is
asserted here. Those follow-up comparisons must use the existing
component inverses and the explicit diagonal scalar changes. Integer
grading is outside this SVec-valued module construction; parity is retained.
