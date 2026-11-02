# Two-letter comparison across changing contents

DeformedActionAssembly §§5–6 and the comparison step in
DeformedMatrixComparison (2), (4) require the two-letter old-to-ordinary
comparison to respect the selected induction flattenings. Unlike the
height-truncated comparison, scalar probe specialization changes the content
category after each append. The same issue occurs for the old/content matrix
charts.

`ELVInductionGridComposition` keeps six categories separate. Its arrows are
`J : C₀ ⥤ C₁`, `K : C₁ ⥤ C₂`, `Qᵣ : Cᵣ ⥤ Dᵣ`, `T : D₀ ⥤ D₁`, and
`S : D₁ ⥤ D₂`, with the two literal commuting-square equalities. The existing
endofunctor square-composition module is unchanged.

`coendGrid_comp_eq` composes the squares. `coendGrid_comp_endpoint` identifies
the resulting object transport with the ordered single-step transports.
`coendGrid_comp_coefficient` proves that the image of `K.map a ≫ g` is the
composition of the two coefficient images, in that order.
`coendGridMap_comp_tensor` applies this identity to nested coend generators:
the composite square map after old induction flattening equals ordinary
induction flattening after the two coefficient maps. Coefficient arrows and
module vectors are arbitrary; no homogeneity, flatness, or comparison
hypothesis is added.

The consumer specializes the entire grid to literal old and ordinary scalar
probe content categories at `ν`, `i :: ν`, and `j :: i :: ν`. It uses the
connected mixed datum, the canonical scalar probe regular module, both moving
colours, arbitrary old coefficient arrows, and vacuum unit tensors.

This supplies the generic flattening identity needed by the selected scalar
and fixed-content double-crossing comparisons. Identifying their chosen
isomorphisms and their equal-colour crossing components remains separate.
In particular this does not identify normalized cap rows with unshifted
ordinary counits.
