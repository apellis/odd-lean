# Presentation equations on supported matrix modules

`SupportedMatrixModules.lean` supplies the matrix modules of F4/(A1)
using literal arrows into the supported path functors. Original formal
sectors, rightmost-weight conditions and summand paths remain the
indices. `matrixEquiv` identifies this module with the existing chosen
factor `P.Mod`, evaluated on the included supported object families.
It is built from the full-subcategory Hom equivalence and the computed
factor path charts. There is no additional closure or faithfulness
input.

`pathHomEquiv_restrictGenImage` shows that the supported generator
restriction includes to exactly its prescribed factor entry.
`pathHomEquiv_upwardImage` applies this to the chosen `P.upwardGens`,
including the constructed mixed coefficient when that coefficient is
used.

`SupportedPresentation.lean` keeps the native ambient product module
and its layer operators, while composing the inclusion and projection
maps with `matrixEquiv` and its inverse. Consequently the whole ambient
operator of any layer list is unchanged. For every whiskered linear
combination, evaluation on supported matrices is

`matrixEquiv(target)⁻¹ ∘ native evaluation ∘ matrixEquiv(source)`.

`interpretation_evalW_eq_zero_iff` therefore both preserves and reflects
all presentation equations. `relationHolds_iff` gives the same statement
for a defining relation in every valid left and right context. It
applies to already-proved relation groups separately; it does not
require an unavailable group in order to restrict an available one.

`respectsOfObligations` and `functorOfObligations` are intermediate
assembly results taking the original `SwappedObligations` as input.
`upwardModuleActionOfObligations` gives the corresponding form required
by the bounded vacuum-observation interface.
In particular, the central inverse obligation is still part of that
explicit native input. These declarations add no supported-category
hypothesis and do not construct that inverse, normalized bubbles, or an
unconditional complete supported action.

The paired consumer uses the occupied symmetric affine two-odd tensor
Hom. Its identity matrix is nonzero in the literal supported matrix
module and remains nonzero under `matrixEquiv`. It recovers the actual
mixed equal-colour upward crossing entry and restricts both contextual
zigzag relations and super interchange using their existing chosen-factor
proofs, without supplying an inversion relation.
