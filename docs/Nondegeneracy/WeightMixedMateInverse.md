# The distinct mixed mate on the weight products

For Brundan–Ellis (1.12), `elvWeightMixedMate_isIso` proves that the given
selected weight cup–crossing–cap family is an isomorphism for distinct
colours. The forward map is `elvWeightMixedMate`: it uses the existing
lower and upper j-adjunctions and `elvActionCross j i`, whose induced
direction reverses the positive affine crossing `j,i → i,j`.
No inverse, flatness or evenness assumption is added.

`elvWeightMixedMate_comparison` proves the whole supported coordinate
square with the positive rectangular content mate. Its source and target
comparisons are the literal object equalities previously checked for the
existing weight functors. The square pastes the independently selected
weight crossing, upper cup and lower cap comparisons.
`elvWeightMixedMate_supported_isIso` transfers the checked content
inverse through that square.

`elvWeightMixedMate_coordinate_isIso` combines the supported result with
the proved vanishing of both actual absent-sector coordinates.
`elvWeightMixedMate_component_isIso` assembles each whole weight-product
module map. The homogeneous inverse criterion then gives the inverse
of the prescribed input-natural family.
`elvWeightMixedMate_inverse_mem` retains degree `parity i * parity j`,
including distinct odd colours. Both inverse identities and naturality
against odd input-module maps hold in the existing superfunctor category.

The producer and paired concrete consumer pass scoped strict checks and
an audit of all 52 owned declarations. The consumer covers both mixed
orders, shifted representable inputs, distinct odd colours, both whole
inverse identities, odd-input naturality and empty truncation. Full CI
remains the integration gate. This establishes the distinct mixed-mate
factor on the existing weight products; the complete factor action and
nondegeneracy theorem still require the remaining assembly results.
