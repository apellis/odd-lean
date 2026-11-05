/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations
import OddMath.QuiverHecke.CyclotomicAction.GlobalMixedSlideAlgebra

/-! # Distinct-colour slides on content induction

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
    ((contentEPairTo D Sc cutoff N β i j γ h).obj M).obj z ⟶
      ((contentEPairTo D Sc cutoff N β i j γ h).obj M).obj z :=
  ((contentInductionTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ
      ((contentPair_sum β i j).symm.trans h)).map
    ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M)).total z

def contentPairOuterDotAt (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentEPairTo D Sc cutoff N β i j γ h).obj M).obj z ⟶
      ((contentEPairTo D Sc cutoff N β i j γ h).obj M).obj z :=
  ((contentInductionTransform D Sc cutoff N
    (β := β + ([i] : Multiset I)) (γ := γ)
    ((contentPair_sum β i j).symm.trans h) ((contentPair_sum β i j).symm.trans h)
    (firstDot_parity D Sc j [])).app (D.parity j)
    (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M)).total z

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
  simp only [dotE_eq, crossTwo, cl_comp]
  exact slide_left_ne D Sc [] [] i j hij _ _

private theorem lastDot_slide_source {i j : I} (hij : i ≠ j) :
    contentCrossAffine D Sc i j ≫ dotE D Sc [j,i] 0 =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc [i,j] 1 ≫ contentCrossAffine D Sc i j) := by
  rw [contentCrossAffine_distinct D Sc i j hij]
  simp only [dotE_eq, crossTwo, cl_comp]
  exact slide_right_ne D Sc [] [] i j hij _ _

theorem contentInduction_distinct_slide_left_linear (β : Multiset I) {i j : I} (hij : i ≠ j) (γ : Multiset I)
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
  all_goals first
    | exact contentCrossAffine_mem D Sc i j
    | exact firstDot_parity D Sc i [j]
    | exact firstDot_parity D Sc j [i]
    | exact contentPairDot_one_parity D Sc i j
    | exact contentPairDot_one_parity D Sc j i

theorem contentInduction_distinct_slide_right_linear (β : Multiset I) {i j : I} (hij : i ≠ j) (γ : Multiset I)
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
  all_goals first
    | exact contentCrossAffine_mem D Sc i j
    | exact firstDot_parity D Sc j [i]
    | exact contentPairDot_one_parity D Sc i j

end OddMath.QuiverHecke.ELVOld

