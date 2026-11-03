# Formal sectors of the supported action

`SwappedAssembly/SupportedSectors.lean` indexes the replete exact-content
Hom categories by the existing pairs of formal nonnegative contents in
F4/(A1). `probeBlock` and `reservoirBlock` use `Finsupp.toMultiset` with
proved original-weight certificates at `-(ΛP-contentWeight b)` and
`-ΛR+contentWeight c`. `H` is the supported full subcategory of that
literal ambient OLD-probe/ELV-reservoir Hom. `target` bundles it as a
parity-supercategory in a sufficiently large universe.

The canonical `inclusion` is full, faithful, additive, linear and parity
preserving by construction. Faithfulness is derived from the full
subcategory inclusion; it is not a supplied premise about an action or
about arbitrary module base change.

`probe_valid_iff` and `reservoir_valid_iff` identify the existing
`StepValid` predecessor conditions with membership of the moving colour
in the selected exact block. The four `*_edge` equalities and
`probeBlock_up`, `probeBlock_down`, `reservoirBlock_up`,
`reservoirBlock_down` identify its selected successor/predecessor with
the actual original-weight `blockSucc`. Every certificate is computed
from formal content, with no injectivity of the root map.

The producer and occupied consumer pass strict Lean 4.34.1 checks with
warnings as errors and both compatibility transparency settings false.
All 35 owned declarations pass the standard axiom audit. The consumer
constructs an actual supported tensor Hom with a surviving product of
two odd coefficients. It exercises all four block equations and the
included object/arrow. At the symmetric affine two-odd datum it also
checks that sectors with the same ambient original weight retain
different chosen formal blocks.

The next attachment restricts native step functors and generator
transformations through these inclusions, using the checked supported
closure. The full presentation and central residual inversion are not
asserted by this indexing result.
