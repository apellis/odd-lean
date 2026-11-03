# Weighted finite matrix field comparison

DeformedMatrixComparison (2), (4) uses the selected genuine source/target
append charts and the canonical module parity coordinates. The first slot
is the original crossing-derived mate, with its original minus sign.
Every other slot uses the given unscaled unit/dot or dot/counit map. No
field compatibility or inverse hypothesis is supplied.

`ELVWeightedMatrixEntryComparison` proves `weightedMatrixCharts_mate`,
`weightedMatrixCharts_unit` and `weightedMatrixCharts_cap`, followed by the
four `weightedMatrixCharts_*Entry_none` / `*_some` equations. The two
`weightedMatrixCharts_unitEntry` / `*_capEntry` statements combine them for
every Option–Fin slot. The supporting four generic actual-field total
formulas in `ELVWeightedMatrixComponents` retain the same given maps.

The producer and paired consumer pass the pinned strict checks, including
the owner audits. The examples use both moving parities, the connected
asymmetric datum, the vacuum, the actual positive unit counts 8 and 10,
and the negative-height cap count 1. The supporting component producer and
consumer also pass, auditing all 87 owned declarations.

The whole finite sum/product comparison and identification of the given
weighted forward matrix with the transported old isomorphism remain open.
This file does not yet claim a component inverse result.
