# Coefficients on exact-content ELV module categories

Fix a multiset β, the full coefficient truncation N, and cutoff data. Let Cβ be the full truncated ELV category on **all** words with content β. The target is exactly `ContentModules β = Superfunctor k Cβ (SVec k)`, the category on which `contentE` and `contentF` are defined, not modules over a single word's endomorphism ring.

`ELVCategoryCoefficients.lean` constructs its parity shift pointwise, packaging the same category as `contentModuleTarget : PiSCat k`. A coefficient is a supernatural endomorphism of the identity of Cβ. Its realization acts on a module M by applying M to the coefficient components. Super interchange proves naturality against odd as well as even module maps. Realization is linear, preserves composition and identity, and commutes with parity projections.

`ELVCategoryCoefficientFaithful.lean` constructs the actual covariant representable supermodule at each source word. Evaluation of the realized coefficient on that representable at its identity recovers the source coefficient component. Thus `contentRealize_injective` proves faithfulness without a Morita comparison or a single-word replacement.

The integer degree of a coefficient requires every component at every word to have that degree in Cβ. `contentModuleCoeffGrading` is the image of these degrees under realization. It is not a grading on all morphisms between module functors, nor a claim that every module-category central endomorphism lies in the image.

For finite colours, `truncatedContent_bounded` supplies the bound at each word. The finite list of permutations of β yields a common threshold for the diagonal source components at this content. Thus a high-degree central family is zero, and its realization is zero. `contentModuleCoefficientIdeal` applies the existing coefficient-filtration theorem to produce the joint nilpotent ideal on functors into this exact module target, including arbitrary intervening morphisms. The exponent is content-dependent; no finite weight fibre or common exponent over infinitely many contents is asserted. No arithmetic hypothesis beyond the finite-colour source theorem is added. The ground ring remains any commutative ring, not only a field or a fixed numerical specialization.

## Exact remaining local-inverse interface

For the actual module-functor adjunctions `A₁ : E₁ ⊣ F₁`, `A₂ : E₂ ⊣ F₂`, normalized dots `x₁,x₂`, crossing `t`, parity `p`, and local height `h`, the existing `SuperRouquierLoc` interface requires:

```lean
invPos : 0 ≤ h → SuperSumInvTo (rouquierMate A₁ A₂ t)
  (fun n => F₁ ◁ rouquierPower x₁ n ≫ A₁.counit)
  p (fun n => n * p) h.toNat
invNeg : h ≤ 0 → SuperSumInvFrom (rouquierMate A₁ A₂ t)
  (fun n => A₂.unit ≫ rouquierPower x₂ n ▷ F₂)
  p (fun n => n * p) (-h).toNat
```

Its `f'` is the principal component of the whole augmented inverse; its `g'` components are the window coefficients. This is stronger than an inverse of the principal mate alone. The remaining coefficient-image task is to construct the source central family realizing the literal module closure

```lean
(A₂.unit ≫ rouquierPower x₂ r ▷ F₂) ≫ y ≫
  (F₁ ◁ rouquierPower x₁ s ≫ A₁.counit)
```

where `y` is that prescribed principal component, and to prove the source family's component degree. The present faithful realization can then supply the coefficient-ideal membership. An endofunctor contraction on the source word category does not by itself solve this step: the lowering module functor is restriction, not a constructed lowering endofunctor on source words. No closure theorem of that weaker kind is included in this milestone.

## Remaining reservoir dependency

This result does not identify the sigma/window residuals with the image coefficients. That requires the specified local augmented inverse and the literal cup–middle–cap closure, with the middle equal to the principal block of the **whole** inverse. No freely chosen inverse of a principal submatrix suffices. The required integer degrees remain d(h+1+2r), 0, and d(1-h+2s). A closure therefore has degree 2d(1+r+s), but identifying that closure with a coefficient in this image, and identifying the actual residual entries with its whiskerings, are separate obligations. This module neither assumes those memberships nor concludes central invertibility. Missing zero-content sectors must still be treated without a blanket two-summand reindexing.
