# Nondegeneracy: mathematical checkpoint

## Conclusion

[SwappedNondegeneracy](SwappedNondegeneracy.md) gives the complete written
argument through deformed factors, the swapped action, cofinal bounded
observations, coefficient recovery and upward-to-oriented reduction.
It remains **proposed until checked in Lean**. There is no complete Lean
proof of super nondegeneracy in this checkpoint.

The written theorem assumes a purely even field with 2 invertible, compatible
symmetrizable Cartan superdata with positive integral symmetrizers,
admissible homogeneous parameters with separate odd-variable exponent support
and invertible leading coefficients, and supplied `cs : CScalars Sc`.
Arbitrary colour sets are handled by finite contextual witnesses, retaining
the original weight group. This does not assert existence of compatible
`CScalars` for arbitrary parameters on a collapsed weight realization.

## Comparison with the starting checkpoint

The comparison point is
[`7e4fbdce5b745357ed761d1d49436f46d0ad02a1`](https://github.com/apellis/odd-lean/tree/7e4fbdce5b745357ed761d1d49436f46d0ad02a1),
not an empty development. At that point the upward-to-oriented reduction,
substantial coefficient-separation infrastructure, cyclotomic induction and
restriction, and parts of the local Rouquier calculus were already present.
The separated Hom route still had unproved factor, signed-adjunction,
local-inversion, fusion and fixed-weight detection obligations.

| Part | Starting checkpoint | Present mathematical boundary |
|---|---|---|
| End-to-end argument | Proposed route with essential construction and detection gaps | Complete written proof in the stated scope; Lean realization incomplete |
| Shifted left adjunction and Hom mates | Zigzag/sign normalization and categorical comparisons unresolved | Normalized adjunction, principal pre/post mate comparisons and natural-power dotted coordinates checked in Lean |
| Postcomposition local inverse | No complete prescribed shifted inverse | Whole pointwise inverse and signed natural transformation packaging checked, including odd morphisms and literal parity shifts |
| Reversed left windows | Written construction not formalized | Both raw augmented inverses, finite triangular changes, parities and zero-height products checked |
| Affine and balanced coordinates | Required input-side freeness and balanced descent not established in this form | Explicit whole-corner equivalence, balanced additive equivalence and shifted right coefficient compatibility checked |
| Moving-dot cancellation | Not available on the prescribed balanced/content targets | Square raises degree by two; signed linear difference is injective on full and content targets, including odd sum-of-squares case |
| Cyclotomic relation killing | All-prefix balanced-target statement not established | All-prefix relation killing checked on the prescribed balanced target for ordinary polynomial coefficients, retaining the full parity involution |
| Detecting family | Fixed-weight simultaneous coefficient/strand detection unresolved | Complete written cofinal construction and signed recovery; conditional bounded-recovery consumer checked in Lean, concrete instance still missing |

## Checked Lean components

The linked revisions identify the precise code independently of later branch
integration. Local importing consumers and headline axiom checks accompany
these modules. The only admitted axioms in those checks are `propext`,
`Classical.choice` and `Quot.sound`. A successful scoped check is not a claim
that the full package gate has completed for every linked revision.

| Component | Declaration or module | Exact code |
|---|---|---|
| Bounded recovery implies upward coefficient injectivity | `upwardCoefficientMap_injective_of_bounded_cyclic_recovery` | [BoundedCyclicRecovery](https://github.com/apellis/odd-lean/blob/051bd98876c2538ead88cd77dfc7d1d57f7e2d3a/OddMath/QuiverHecke/BoundedCyclicRecovery.lean) |
| Whole affine prepend coordinates | `prependCoordinateEquiv` | [PrependEquivalence](https://github.com/apellis/odd-lean/blob/5bc81b836e321614011d2d777145682dd83dd971/OddMath/QuiverHecke/CyclotomicAction/PrependEquivalence.lean) |
| Balanced and shifted coefficient coordinates | `prependTensorEquiv`, `qPrependTensorEquiv` | [PrependCoefficientCoordinates](https://github.com/apellis/odd-lean/blob/e45c26dc8e94953a71b7b64cee7e882d672a3213/OddMath/QuiverHecke/CyclotomicAction/PrependCoefficientCoordinates.lean) |
| Moving-dot square cancellation | `targetRightDot_sq_sub_coefficient_injective` | [PrependDotCancellation](https://github.com/apellis/odd-lean/blob/4fb8259c9f705d7df3262f7df4116a6f0a2e2764/OddMath/QuiverHecke/CyclotomicAction/PrependDotCancellation.lean) |
| Signed linear cancellation on the content target | `contentTargetRightDot_sub_lastDot_injective` | [LinearDotCancellation](https://github.com/apellis/odd-lean/blob/d20454cad765adfad1785a85664754bc88e3c97f/OddMath/QuiverHecke/CyclotomicAction/LinearDotCancellation.lean) |
| Prescribed postcomposition inverse in SCat | `homContentPostSuperInvPos`, `homContentPostSuperInvNeg` | [RouquierHomPostSuperInverse](https://github.com/apellis/odd-lean/blob/c5b61420fff4f3fdc9f92d931000766ba91756a2/OddMath/SKM/RouquierHomPostSuperInverse.lean) |
| Raw reversed left windows | `leftWindowCup_inverse`, `leftWindowCap_inverse`, `leftWindow_zero_inverse` | [RouquierLeftWindowInverse](https://github.com/apellis/odd-lean/blob/d49a43f1aa4c11852191d6c01a52fd34d0573f4f/OddMath/SKM/RouquierLeftWindowInverse.lean) |
| All-prefix relation killing | `allPrefix_relation_tmul_zero`, `append_relation_move_tmul_zero` | [IntertwinerRelation](https://github.com/apellis/odd-lean/blob/497093ee3e982034530907bcedd4cb707f757e60/OddMath/QuiverHecke/CyclotomicAction/IntertwinerRelation.lean) |

These are constructive maps and identities, not an unconditional factor-model
or nondegeneracy instance. In particular, the balanced equivalence is additive
with separately proved right coefficient compatibility; it is not asserted
to carry new ground-ring-linear or integer-graded structure.

## Remaining formalization

1. **Factor construction.** The ordinary-polynomial all-prefix relation-killing
   identity is checked. Finish signed polynomial transport, global QP and subsequent local inversion
   on the prescribed quotients. Extend the required construction to the full
   ELV coefficient algebra; ordinary `Polynomial k` parameters alone do not
   realize the independent odd coefficient generators.
2. **Precomposition inverse.** Transport the checked raw reversed windows
   through the prescribed homogeneous Hom coordinates. Retain Hom height
   minus the factor height, the dotted normalizations and the exceptional
   principal sign at height zero; then prove the required natural packaging.
3. **Whole swapped action and fusion.** Assemble the remaining family fields,
   mixed-sector relations and augmented inversion from the specified maps.
   A pointwise local inverse or nilpotent feedback calculation alone does
   not provide this action.
4. **Concrete detection.** Implement the vacuum, bubble formulas and bounded
   signed recovery for the constructed factors, then instantiate the existing
   bounded-recovery and upward-to-oriented reductions, including the finite
   contextual witness passage for arbitrary colours.

The written proof describes how these obligations fit together. It does not
remove the need to construct and check their Lean terms. No percentage of
formal completion is assigned: the remaining work includes substantial
constructions, not merely final theorem composition.

## Preserved incomplete precomposition transport

[`RouquierHomPreInverse.lean`](https://github.com/apellis/odd-lean/blob/a5f512a3bedf0838c8cb9eda331c2905d6ce5bb8/OddMath/SKM/RouquierHomPreInverse.lean)
contains homogeneous-coordinate transport for both orientations and raw
Nat-indexed left-window inverse packages, including zero-height boundaries.
It has a scoped strict build but no importing consumer, owned-declaration
axiom audit or root integration. It is not the completed pre-Hom inverse.
Its accompanying mathematical handoff records the remaining coordinate,
normalization and literal-forward-map identifications. It must not be used
as evidence that the second remaining obligation above has been discharged.
