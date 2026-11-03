# Distinct mates on weight products

For Brundan–Ellis (1.12), `ELVWeightMixedMate.elvWeightMixedMate` is the
cup–crossing–cap map on the existing weight products. It uses the lower
and upper j-adjunctions at their different weights and the selected
`elvActionCross j i`: categorical induction reverses the physical
crossing `j,i → i,j`.

`ELVPiSCatRectangularMate.rectangularMate_piscat_app` expands this mate
at four independent PiSCat corners, and `rectangularMate_piscat_mem`
preserves its homogeneous degree. Consequently `elvWeightMixedMate_mem`
has degree `parity i * parity j`; `elvWeightMixedMate_app` gives its
literal selected unit, crossing and counit components.

For an output block δ of weight x_i, the supported case is δ equal to
the i-successor of a block β of weight x_0. Its source coordinate is
`E_i F_j` on β and its target coordinate is `F_j E_i` through the same
upper content. At an absent i-predecessor, `elvMixedPredecessor_iff`
proves that adding a distinct j does not create an i-predecessor.
`elvWeightMixedSource_isZero` and `elvWeightMixedTarget_isZero` therefore
show that both genuine coordinates vanish.
`elvWeightMixedMate_absent_isIso` inverts the given selected mate there;
no vanishing premise is imposed on the input module.

`ELVContentDistinctTargets.contentDistinctTargetsMate_isIso` and
`contentDistinctTargetsFunctor_isIso` transport the proved canonical
content inverse to arbitrary certificates for all four successor
contents. They retain the literal append functors and positive crossing,
and require only distinctness of the colours.

These three producers and their concrete consumers pass scoped strict
checks and an audit of all 53 owned declarations. Consumers use mixed
colours in both orders, distinct odd colours, shifted representable
modules, nonempty source contents and the absent boundary. Full CI
remains the integration gate.

The remaining obligation is the whole selected weight-mate comparison
with this content mate on supported blocks, followed by assembling its
inverse on the weight products. No inverse on supported weight sectors
or full factor action is claimed here.
