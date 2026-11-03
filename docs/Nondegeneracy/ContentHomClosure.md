# Replete exact-content Hom closure

This implements the formal support category F4 and (A1) of
`SwappedActionAssembly.md`, using the original-weight embedding from
`ELVContentHomSupport.lean`. The object property `Supported` means
isomorphic to a realization of an arbitrary functor on the chosen exact
probe and reservoir content categories. `SupportedHom` is its replete
full subcategory: every supernatural arrow between its objects is
retained. No whole-Hom faithfulness or exhaustiveness assertion is used.

The four isomorphisms `preEIso`, `preFIso`, `postEIso`, `postFIso` identify
the literal native pre/post compositions of an exact-content realization
with the realizations of composition by the chosen content induction or
restriction. Their morphisms are even. On the selected output component
they use the equality of the chosen Superfunctors, including all odd
maps; on every other component they use the unique isomorphism between
the proved zero functors. Consequently the comparison is on whole
Superfunctors and all inputs, rather than an evaluation at a regular
module.

`preE_supported`, `preF_supported`, `postE_supported`, `postF_supported`
then prove object closure for the replete category by transporting these
isomorphisms through the full native pre/post functors. No theorem that
the embedding is fully faithful is needed to keep the existing arrows.

`preE_absent_functor_isZero` and `postF_absent_functor_isZero` strengthen
the component support statements to actual zero objects in the whole
Hom category. The corresponding `*_supported_absent_isZero` theorems
apply to every replete-supported object. These are the missing native
boundary-zero facts when the moving colour is absent from the chosen
formal content. Every collision block and every module input is still
included in their proof.

Parity shift is treated by `postShiftIso` and `shift_supported`, with the
Hom parity completion chosen as `PiTwoSupercategory.homPiLeft`.
`supportedPi` equips the replete full subcategory with the resulting
parity completion. The component comparison retains the action of parity
shift on odd maps; equality only of its object function would not suffice.

The paired consumer uses the actual OLD probe and regular-power reservoir
categories at a symmetric affine two-odd datum. Its lowest-weight fibre
contains both the empty block and `[false,true]`, which has predecessors.
The exact-support realization vanishes at the latter and has a nonzero
product of the two odd coefficients at its regular selected input. It
tests all four primitive whole-functor charts, their evenness, replete
closure and the absent whole-functor zeros. The selected component of its
functor agrees with `WeightTensorVacuum.selectedHom` on every input.

Remaining attachments are the chosen initial whole-functor comparison
with `selectedHom`, the formal-sector indexing of these supported
categories and primitive functors, restriction of the already computed
generator matrices, and the central residual coefficient-ideal closure.
This construction does not assert central invertibility for arbitrary
unsupported objects of whole-weight Hom.

The producer and paired consumer pass strict Lean 4.34.1 checks with
warnings as errors and both compatibility transparency settings false.
All 64 owned declarations pass the standard axiom audit.
