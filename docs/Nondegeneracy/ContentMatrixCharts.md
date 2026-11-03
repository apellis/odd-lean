# Genuine charts for the prescribed content matrices

DeformedMatrixComparison (2), (4) requires the selected preceding E/F,
following F/E and value comparisons to be invertible on entire module
values. `ELVContentMatrixCharts.lean` constructs these linear equivalences
from the already chosen module isomorphisms, with no invertibility or
chart-evenness premise.

- `oldContentEFLinearEquiv` uses the chosen preceding-composite comparison;
  `oldContentEFLinearEquiv_hom` identifies its forward map with the exact
  `oldContentEFRestrictionLinear` from the checked mate square.
- `oldContentFELinearEquiv` uses the chosen following-composite comparison;
  `oldContentFELinearEquiv_apply` identifies its forward map, on every
  vector, with the selected upper append-restriction comparison.
- `oldContentValueLinearEquiv` uses the fully faithful inclusion unit;
  `oldContentValueLinearEquiv_apply` identifies it with the literal
  identity tensor.
- `oldContentMatrixCharts_mate_tensor` carries the independently given
  content cup-crossing-cap through these genuine charts to the literal
  first old matrix entry, on every balanced generator.

The concrete consumer proves bijectivity of the given charts for both
moving parities, mixed representable inputs, and repeated-colour contents
of heights two, zero and minus two. It applies the mate square to an
inhomogeneous identity-plus-dot coefficient. Every producer-owned
declaration, including generated declarations, is audited.

The categories are the full-coefficient, untruncated old content
categories. The preceding composite is at explicit content `i :: ν`.
Transport of all dotted unit/cap entries, assembly of the given finite
matrix inverses, absent-predecessor contents and coefficient-truncated
weight transport remain separate.
