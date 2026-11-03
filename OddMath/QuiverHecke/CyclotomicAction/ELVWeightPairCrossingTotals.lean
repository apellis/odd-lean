/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairDots

/-! # Linear components of the original-weight pair crossing

DeformedActionAssembly §6 uses the original weight crossing and the
canonical pair coordinates in pointwise linear quadratic relations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u

private theorem crossing_total_of_component
    {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B E F : Superfunctor k C (SVec k)}
    (e : A ≅ B) (f : E ≅ F) (x : B ⟶ F) (y : A ⟶ E)
    (h : y = (e.hom ≫ x) ≫ f.inv) (w : C) :
    y.total w = (moduleIsoLinearEquiv f w).symm.toLinearMap.comp
      ((x.total w).comp (moduleIsoLinearEquiv e w).toLinearMap) := by
  subst y
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

private theorem cross_composite_of_linear_squares
    {k : Type u} [CommRing k]
    {A B C E : Type u}
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    [AddCommMonoid C] [Module k C] [AddCommMonoid E] [Module k E]
    (e : A ≃ₗ[k] B) (f : C ≃ₗ[k] E)
    (x : E →ₗ[k] B) (y : B →ₗ[k] E) (q : C →ₗ[k] A) (r : A →ₗ[k] C)
    (hq : q = e.symm.toLinearMap.comp (x.comp f.toLinearMap))
    (hr : r = f.symm.toLinearMap.comp (y.comp e.toLinearMap)) :
    q.comp r = e.symm.conjAlgEquiv k (x.comp y) := by
  subst q r
  apply LinearMap.ext
  intro z
  change e.symm (x (f (f.symm (y (e z))))) = e.symm (x (y (e z)))
  rw [f.apply_symm_apply]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- Evaluation of the independently assembled weight crossing uses exactly
the selected two-successor comparisons and the prescribed affine crossing. -/
theorem elvWeightCrossVia_total (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    ((elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app
      (D.parity i * D.parity j) M).total w =
      (moduleIsoLinearEquiv
        ((elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
          (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).app M) w).symm.toLinearMap.comp
        ((((contentInductionTransform D Sc cutoff bound
          (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
            (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) (M β)).total w).comp
          (moduleIsoLinearEquiv
            ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M) w).toLinearMap) :=
  crossing_total_of_component
    ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M)
    ((elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).app M)
    _ _ (elvWeightCrossVia_component D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε M) w

/-- The two actual weight crossings compose to the affine two-crossing
operator in their selected source coordinates. -/
theorem elvWeightCrossVia_composite_total (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    let hε' := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε
    let hs := elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε
    let ht := elvWeightPair_content_eq D j i Λ h₃ h₄ β ε hε'
    let e := moduleIsoLinearEquiv
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M) w
    (((elvWeightCrossVia D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂ β ε hε').app
        (D.parity j * D.parity i) M).total w).comp
      (((elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app
        (D.parity i * D.parity j) M).total w) =
      e.symm.conjAlgEquiv k
        ((((contentInductionTransform D Sc cutoff bound hs ht
          (contentCrossAffine_mem D Sc j i)).app (D.parity j * D.parity i) (M β)).total w).comp
          (((contentInductionTransform D Sc cutoff bound ht hs
            (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) (M β)).total w)) := by
  dsimp only
  exact cross_composite_of_linear_squares
    (moduleIsoLinearEquiv
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M) w)
    (moduleIsoLinearEquiv
      ((elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).app M) w)
    _ _ _ _
    (elvWeightCrossVia_total D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε) M w)
    (elvWeightCrossVia_total D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε M w)

/-- The globally chosen crossing has the same total formula at every
supported output block. -/
theorem elvWeightCrossComponent_total (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    (elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
      (D.parity i * D.parity j) M ε).total w =
      (moduleIsoLinearEquiv
        ((elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
          (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)).app M) w).symm.toLinearMap.comp
        ((((contentInductionTransform D Sc cutoff bound
          (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
            (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) (M β)).total w).comp
          (moduleIsoLinearEquiv
            ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M) w).toLinearMap) := by
  have h := congrArg (fun a => a.total w)
    (elvWeightCrossComponent_of D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
      (D.parity i * D.parity j) M β ε hε)
  exact h.trans (elvWeightCrossVia_total D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε M w)

/-- Where the double predecessor is absent, the given global crossing has
zero total at every target word. -/
theorem elvWeightCrossComponent_total_absent (p : ZMod 2)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    (elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε).total w = 0 := by
  rw [elvWeightCrossComponent_absent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M ε hε]
  change (0 : _ →ₗ[k] _) + (0 : _ →ₗ[k] _) = 0
  exact add_zero _

end OddMath.QuiverHecke.ELVOld
