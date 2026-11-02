# Distinct-colour categorical mate comparison

This develops the prescribed mate comparison in
[DeformedActionAssembly](DeformedActionAssembly.md) §4, for Brundan–Ellis
(1.12). It follows the independently balanced quotient inverse in
[DistinctCrossingDecoder](DistinctCrossingDecoder.md).

For two append functors `A` and `B`, the existing canonical induction
composition comparisons transport a homogeneous crossing
`α : B ⋙ A ⇒ A ⋙ B`. `mixedCrossComponent` maps induction by `A` followed by
induction by `B` to the other order. Its tensor formula twists the whole
composite arrow, and its supernaturality retains odd module morphisms.
`orderedMixedMateComponent` applies the existing unit of `B`, this crossing,
and induction by `A` of the existing counit of `B`. Its generator formula
has no same-colour minus sign.

In the old full-ELV category, take `A = append i`, `B = append j` and the raw
last crossing from `j,i` to `i,j`. `moduleMate` is defined using the existing
`SKM.rectangularMate` and the fixed old append adjunction. The checked
`rectangularMate_scat_app` and `moduleMate_eq_ordered` identify it with that
literal ordered cup-crossing-cap. `moduleMate_total_tensor` evaluates it on
arbitrary balanced generators and arbitrary old modules.

The source comparison changes the coefficient shift from zero to
`e = p(i)p(j)`. `sourceParityEquiv` is the canonical J: apply total parity
to power `e` to the entire first tensor factor, including exterior
coefficients, and retain the second factor. Its inverse applies the same
twist. The coefficient keeps its ordinary right action. The construction is
an equivalence of the prescribed balanced tensors, independently of the
crossing image or its inverse.

The actual induced restriction source is compared using the existing
coefficient-zero module isomorphism. `evaluatedMate` fixes co-Yoneda
evaluation at `t ++ [j]`. `moduleMate_crossing` proves equality of whole
linear maps: the evaluated literal mate equals `toCyclotomic` after
canonical J. `moduleMateEquiv_apply` identifies `moduleMateEquiv` with that
actual map on every balanced class. Thus the full quotient PBW decoder,
followed by inverse J, gives its inverse on every old representable corner.
All six producers and the paired concrete consumer pass strict scoped Lean
checks. The consumer covers mixed parities, distinct odd colours, exterior
coefficients in the first tensor factor, empty corners and zero cutoff, and
audits all 73 owned declarations. Full CI remains the integration gate.

This does not yet establish the inverse on every old module, or transport
it through the truncated exact-content and weight comparisons. Those steps,
and attachment to the full factor family, remain open. Ordinary right
precomposition on a kernel is not silently substituted for the signed
representable module map.
