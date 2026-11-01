/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations
import OddMath.QuiverHecke.CyclotomicAction.GlobalMixedSlideAlgebra

/-! # Distinct-colour slides on actual content induction

Brundan–Ellis Definition 1.5, (1.8). The pair crossing and both single-letter
dots are independently constructed. Common target content is retained at
both words; full coefficient parity is carried by balanced induction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

def contentPairInnerDotAt (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j γ h M z) :=
  BalancedInduction.mapComponent
    (contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ
      (by rw [add_assoc]; exact h))
    ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M)
    (D.parity i) z

def contentPairOuterDotAt (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j γ h M z) :=
  BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N
      (β := β + ([i] : Multiset I)) (γ := γ)
      (by rw [add_assoc]; exact h) (by rw [add_assoc]; exact h)
      (firstDot_parity D Sc j []))
    (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M) z

private theorem pairInner_transport (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentPairInnerDotAt D Sc cutoff N β i j γ h M z =
      (contentEPairEquiv D Sc cutoff N β i j γ h M z).symm.toLinearMap ∘ₗ
        BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc cutoff N h h
            (firstDot_parity D Sc i [j])) M z ∘ₗ
        (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap := by
  subst γ
  change contentEPairInnerDot D Sc cutoff N β i j M z = _
  rw [← contentEPairDot_zero_eq_inner]
  rfl

private theorem pairOuter_transport (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentPairOuterDotAt D Sc cutoff N β i j γ h M z =
      (contentEPairEquiv D Sc cutoff N β i j γ h M z).symm.toLinearMap ∘ₗ
        BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc cutoff N h h
            (contentPairDot_one_parity D Sc i j)) M z ∘ₗ
        (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap := by
  subst γ
  change contentEPairOuterDot D Sc cutoff N β i j M z = _
  rw [← contentEPairDot_one_eq_outer]
  rfl

private theorem contentTwoTransform_tensor {β γ : Multiset I} {σ τ υ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (hυ : β + (υ : Multiset I) = γ) {p q : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    {b : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D υ)}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β υ γ hυ).obj v ⟶ z) (m : M.obj v) :
    ((BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M z).comp
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hτ hυ hb) M z))
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β υ γ hυ) M.toFunctor v h m) =
    sign k (p*q) •
      BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ) M.toFunctor v
        (contentAppendToComponent D Sc cutoff N hσ hυ (a ≫ b) v ≫
          twist k (p+q) h) m := by
  rw [BalancedInduction.transformLinear_comp, LinearMap.smul_apply,
    BalancedInduction.transformLinear_tensor]
  congr 2
  rw [contentAppendToComponent_comp D Sc cutoff N hσ hτ hυ a hb]

private theorem firstDot_slide_source {i j : I} (hij : i ≠ j) :
    dotE D Sc [i,j] 0 ≫ contentCrossAffine D Sc i j =
      SKM.zsign k (D.parity i * D.parity j) •
        (contentCrossAffine D Sc i j ≫ dotE D Sc [j,i] 1) := by
  rw [contentCrossAffine_distinct D Sc i j hij]
  have h := inductionStrand_slide_left_ne D Sc hij
  have h0 : inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [j]) =
      dotE D Sc [i,j] 0 := by
    change dotE D Sc [i] 0 ▷ (pres D Sc).obj (ob D [j]) = _
    exact dotE_whiskerRight D Sc [i] [j] 0 (by simp)
  have h1 : (pres D Sc).obj (ob D [j]) ◁ inductionStrandDot D Sc i =
      dotE D Sc [j,i] 1 := by
    change (pres D Sc).obj (ob D [j]) ◁ dotE D Sc [i] 0 = _
    exact whiskerLeft_letter_dotE D Sc j [i] 0
  rw [h0, h1] at h
  exact h

private theorem lastDot_slide_source {i j : I} (hij : i ≠ j) :
    contentCrossAffine D Sc i j ≫ dotE D Sc [j,i] 0 =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc [i,j] 1 ≫ contentCrossAffine D Sc i j) := by
  rw [contentCrossAffine_distinct D Sc i j hij]
  have h := inductionStrand_slide_right_ne D Sc hij
  have h0 : inductionStrandDot D Sc j ▷ (pres D Sc).obj (ob D [i]) =
      dotE D Sc [j,i] 0 := by
    change dotE D Sc [j] 0 ▷ (pres D Sc).obj (ob D [i]) = _
    exact dotE_whiskerRight D Sc [j] [i] 0 (by simp)
  have h1 : (pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc j =
      dotE D Sc [i,j] 1 := by
    change (pres D Sc).obj (ob D [i]) ◁ dotE D Sc [j] 0 = _
    exact whiskerLeft_letter_dotE D Sc i [j] 0
  rw [h0, h1] at h
  exact h

private theorem block_slide_left (β : Multiset I) {i j : I} (hij : i ≠ j) (γ : Multiset I)
    (hij' : β + ([i,j] : Multiset I) = γ)
    (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hij'
      (firstDot_parity D Sc i [j])) M z).comp
      (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hji
        (contentCrossAffine_mem D Sc i j)) M z) =
    sign k (D.parity i * D.parity j) •
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hji
        (contentCrossAffine_mem D Sc i j)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hji hji
          (contentPairDot_one_parity D Sc j i)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentTwoTransform_tensor, LinearMap.smul_apply, contentTwoTransform_tensor,
    firstDot_slide_source D Sc hij, contentAppendToComponent_smul, Linear.smul_comp]
  simp only [add_comm (D.parity i) (D.parity i * D.parity j),
    mul_comm (D.parity i) (D.parity i * D.parity j)]
  simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul, smul_smul,
    sign_eq_zsign]
  congr 1
  ring

private theorem block_slide_right (β : Multiset I) {i j : I} (hij : i ≠ j) (γ : Multiset I)
    (hij' : β + ([i,j] : Multiset I) = γ)
    (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hji
      (contentCrossAffine_mem D Sc i j)) M z).comp
      (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hji hji
        (firstDot_parity D Sc j [i])) M z) =
    sign k (D.parity i * D.parity j) •
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hij'
        (contentPairDot_one_parity D Sc i j)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hij' hji
          (contentCrossAffine_mem D Sc i j)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentTwoTransform_tensor, LinearMap.smul_apply, contentTwoTransform_tensor,
    lastDot_slide_source D Sc hij, contentAppendToComponent_smul, Linear.smul_comp]
  simp only [add_comm (D.parity i * D.parity j) (D.parity j),
    mul_comm (D.parity i * D.parity j) (D.parity j)]
  simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul, smul_smul,
    sign_eq_zsign]
  congr 1
  ring

private theorem transport_slide
    {A B C E : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup E] [Module k E]
    (e : A ≃ₗ[k] B) (f : C ≃ₗ[k] E)
    (x : Module.End k B) (c : E →ₗ[k] B) (y : Module.End k E) (s : k)
    (h : x.comp c = s • c.comp y) :
    (e.symm.toLinearMap ∘ₗ x ∘ₗ e.toLinearMap).comp
        (e.symm.toLinearMap ∘ₗ c ∘ₗ f.toLinearMap) =
      s • (e.symm.toLinearMap ∘ₗ c ∘ₗ f.toLinearMap).comp
        (f.symm.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap) := by
  ext a
  have ha := LinearMap.congr_fun h (f a)
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, map_smul] using congrArg e.symm ha

/-- Left slide for the actual pair crossing and independent first/last dots. -/
theorem contentEPair_distinct_slide_left (β : Multiset I) {i j : I} (hij : i ≠ j)
    (γ : Multiset I) (hij' : β + ([i,j] : Multiset I) = γ)
    (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentPairInnerDotAt D Sc cutoff N β i j γ hij' M z).comp
        (contentEPairCross D Sc cutoff N β i j γ hij' hji M z) =
      sign k (D.parity i * D.parity j) •
        (contentEPairCross D Sc cutoff N β i j γ hij' hji M z).comp
          (contentPairOuterDotAt D Sc cutoff N β j i γ hji M z) := by
  rw [pairInner_transport, pairOuter_transport]
  exact transport_slide _ _ _ _ _ _
    (block_slide_left D Sc cutoff N β hij γ hij' hji M z)

/-- Right slide, retaining the explicit common target content after swapping. -/
theorem contentEPair_distinct_slide_right (β : Multiset I) {i j : I} (hij : i ≠ j)
    (γ : Multiset I) (hij' : β + ([i,j] : Multiset I) = γ)
    (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentEPairCross D Sc cutoff N β i j γ hij' hji M z).comp
        (contentPairInnerDotAt D Sc cutoff N β j i γ hji M z) =
      sign k (D.parity i * D.parity j) •
        (contentPairOuterDotAt D Sc cutoff N β i j γ hij' M z).comp
          (contentEPairCross D Sc cutoff N β i j γ hij' hji M z) := by
  rw [pairInner_transport, pairOuter_transport]
  have h := block_slide_right D Sc cutoff N β hij γ hij' hji M z
  ext a
  have ha := LinearMap.congr_fun h ((contentEPairEquiv D Sc cutoff N β j i γ hji M z) a)
  simpa only [contentEPairCross, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_smul] using
    congrArg (contentEPairEquiv D Sc cutoff N β i j γ hij' M z).symm ha
end OddMath.QuiverHecke.ELVOld
