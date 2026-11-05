/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight
import OddMath.QuiverHecke.CyclotomicAction.GlobalProduct
import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.QuiverHecke.CyclotomicAction.Slides
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import StringDiagrams.Super.MonoidalEnvelope
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import StringDiagrams.Super.Functor
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight
import OddMath.QuiverHecke.CyclotomicAction.Slides
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import StringDiagrams.Super.Functor
import OddMath.QuiverHecke.Centre

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

private theorem sourceTransform_congr {β γ : Multiset I} {σ : List I}
    (h : β + (σ : Multiset I) = γ) {p : ZMod 2}
    {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ p) (hab : a = b)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h ha) M z =
      BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h hb) M z := by
  cases hab
  rfl

private theorem square_comp_right_congr {A B : Type u}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    {f g : Module.End k B} (h : f = g) (e : A →ₗ[k] B) :
    f.comp e = g.comp e := by
  cases h
  rfl

private theorem pairInner_square (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap ∘ₗ
      contentPairInnerDotAt D Sc cutoff N β i j γ h M z =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N h h (firstDot_parity D Sc i [j])) M z ∘ₗ
      (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap := by
  unfold contentPairInnerDotAt
  rw [contentInductionDot_component]
  have hc := contentInductionComp_inner D Sc cutoff N β [i] [j] γ
    ((contentPair_sum β i j).symm.trans h) h (firstDot_parity D Sc i []) M z
  have ht := contentInductionMap_total_of_mem
    (contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ
      ((contentPair_sum β i j).symm.trans h))
    (BalancedInduction.transformComponent_mem
      (contentAppendTo_supernatural D Sc cutoff N
        (β := β) (γ := β + ([i] : Multiset I)) rfl rfl
        (firstDot_parity D Sc i [])) M) z
  rw [← ht] at hc
  have hf := sourceTransform_congr D Sc cutoff N h
    (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
      (firstDot_parity D Sc i []))
    (firstDot_parity D Sc i [j]) (dotE_whiskerRight D Sc [i] [j] 0 (by simp)) M z
  exact hc.trans (square_comp_right_congr (k := k) hf
    (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap)

private theorem pairOuter_square (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap ∘ₗ
      contentPairOuterDotAt D Sc cutoff N β i j γ h M z =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N h h (contentPairDot_one_parity D Sc i j)) M z ∘ₗ
      (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap := by
  unfold contentPairOuterDotAt
  have hc := contentInductionComp_outer D Sc cutoff N β [i] [j] γ
    ((contentPair_sum β i j).symm.trans h) h (firstDot_parity D Sc j []) M z
  have ht := contentInductionTransform_total D Sc cutoff N
    (β := β + ([i] : Multiset I)) (γ := γ)
    ((contentPair_sum β i j).symm.trans h) ((contentPair_sum β i j).symm.trans h) (firstDot_parity D Sc j [])
    (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M) z
  dsimp only [contentAppend] at ht
  rw [← ht] at hc
  have hf := sourceTransform_congr D Sc cutoff N h
    (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
      (firstDot_parity D Sc j []))
    (contentPairDot_one_parity D Sc i j) (whiskerLeft_letter_dotE D Sc i [j] 0) M z
  exact hc.trans (square_comp_right_congr (k := k) hf
    (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap)

private theorem equivalence_transport_square
    {A B C E : Type u}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup E] [Module k E]
    (e : A ≃ₗ[k] B) (f : C ≃ₗ[k] E) (a : E →ₗ[k] B) :
    e.toLinearMap.comp (e.symm.toLinearMap.comp (a.comp f.toLinearMap)) =
      a.comp f.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact e.apply_symm_apply _

private theorem pairCross_square (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (ht : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentEPairEquiv D Sc cutoff N β i j γ h M z).toLinearMap ∘ₗ
      contentEPairCross D Sc cutoff N β i j γ h ht M z =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N h ht (contentCrossAffine_mem D Sc i j)) M z ∘ₗ
      (contentEPairEquiv D Sc cutoff N β j i γ ht M z).toLinearMap := by
  exact equivalence_transport_square (k := k)
    (contentEPairEquiv D Sc cutoff N β i j γ h M z)
    (contentEPairEquiv D Sc cutoff N β j i γ ht M z)
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N h ht (contentCrossAffine_mem D Sc i j)) M z)

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

private theorem transport_slide_square
    {A B C E : SVec.{u} k}
    (e : A ≃ₗ[k] B) (f : C ≃ₗ[k] E)
    {x : Module.End k A} {c : C →ₗ[k] A} {y : Module.End k C}
    {X : Module.End k B} {b : E →ₗ[k] B} {Y : Module.End k E} {s : k}
    (hx : e.toLinearMap ∘ₗ x = X ∘ₗ e.toLinearMap)
    (hc : e.toLinearMap ∘ₗ c = b ∘ₗ f.toLinearMap)
    (hy : f.toLinearMap ∘ₗ y = Y ∘ₗ f.toLinearMap)
    (h : X.comp b = s • b.comp Y) : x.comp c = s • c.comp y := by
  apply LinearMap.ext
  intro a
  apply e.injective
  change e (x (c a)) = e (s • c (y a))
  rw [map_smul]
  calc
    e (x (c a)) = X (e (c a)) := LinearMap.congr_fun hx (c a)
    _ = X (b (f a)) := congrArg X (LinearMap.congr_fun hc a)
    _ = s • b (Y (f a)) := LinearMap.congr_fun h (f a)
    _ = s • b (f (y a)) := congrArg (fun v => s • b v) (LinearMap.congr_fun hy a).symm
    _ = s • e (c (y a)) := congrArg (fun v => s • v) (LinearMap.congr_fun hc (y a)).symm

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
  exact transport_slide_square
    (A := ((contentEPairTo D Sc cutoff N β i j γ hij').obj M).obj z)
    (B := ((contentInductionTo D Sc cutoff N β [i,j] γ hij').obj M).obj z)
    (C := ((contentEPairTo D Sc cutoff N β j i γ hji).obj M).obj z)
    (E := ((contentInductionTo D Sc cutoff N β [j,i] γ hji).obj M).obj z)
    (contentEPairEquiv D Sc cutoff N β i j γ hij' M z)
    (contentEPairEquiv D Sc cutoff N β j i γ hji M z)
    (pairInner_square D Sc cutoff N β i j γ hij' M z)
    (pairCross_square D Sc cutoff N β i j γ hij' hji M z)
    (pairOuter_square D Sc cutoff N β j i γ hji M z)
    (contentInduction_distinct_slide_left_linear D Sc cutoff N β hij γ hij' hji M z)

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
  have h := contentInduction_distinct_slide_right_linear D Sc cutoff N β hij γ hij' hji M z
  have h' := congrArg (fun q => sign k (D.parity i * D.parity j) • q) h
  simp only [smul_smul, Supercategory.sign_mul_self, one_smul] at h'
  have H := transport_slide_square
    (A := ((contentEPairTo D Sc cutoff N β i j γ hij').obj M).obj z)
    (B := ((contentInductionTo D Sc cutoff N β [i,j] γ hij').obj M).obj z)
    (C := ((contentEPairTo D Sc cutoff N β j i γ hji).obj M).obj z)
    (E := ((contentInductionTo D Sc cutoff N β [j,i] γ hji).obj M).obj z)
    (contentEPairEquiv D Sc cutoff N β i j γ hij' M z)
    (contentEPairEquiv D Sc cutoff N β j i γ hji M z)
    (pairOuter_square D Sc cutoff N β i j γ hij' M z)
    (pairCross_square D Sc cutoff N β i j γ hij' hji M z)
    (pairInner_square D Sc cutoff N β j i γ hji M z) h'.symm
  have H' := congrArg (fun q => sign k (D.parity i * D.parity j) • q) H
  simpa only [smul_smul, Supercategory.sign_mul_self, one_smul] using H'.symm
private theorem sign_slide_reverse {A B : SVec.{u} k}
    (p : ZMod 2) {a b : A ⟶ B} (h : a = sign k p • b) : b = sign k p • a := by
  rw [h, smul_smul, Supercategory.sign_mul_self, one_smul]

/-- The left distinct-colour slide in the orientation of
`RouquierMulticolour.slideLeft`, after total evaluation. -/
theorem contentEPair_slideLeft (β : Multiset I) {i j : I} (hij : i ≠ j)
    (γ : Multiset I) (hij' : β + ([i,j] : Multiset I) = γ)
    (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentEPairCross D Sc cutoff N β i j γ hij' hji M z).comp
        (contentPairOuterDotAt D Sc cutoff N β j i γ hji M z) =
      sign k (D.parity i * D.parity j) •
        (contentPairInnerDotAt D Sc cutoff N β i j γ hij' M z).comp
          (contentEPairCross D Sc cutoff N β i j γ hij' hji M z) := by
  exact sign_slide_reverse (k := k)
    (A := ((contentEPairTo D Sc cutoff N β j i γ hji).obj M).obj z)
    (B := ((contentEPairTo D Sc cutoff N β i j γ hij').obj M).obj z) _
    (contentEPair_distinct_slide_left D Sc cutoff N β hij γ hij' hji M z)

/-- The right distinct-colour slide in the orientation of
`RouquierMulticolour.slideRight`, after total evaluation. -/
theorem contentEPair_slideRight (β : Multiset I) {i j : I} (hij : i ≠ j)
    (γ : Multiset I) (hij' : β + ([i,j] : Multiset I) = γ)
    (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentPairOuterDotAt D Sc cutoff N β i j γ hij' M z).comp
        (contentEPairCross D Sc cutoff N β i j γ hij' hji M z) =
      sign k (D.parity i * D.parity j) •
        (contentEPairCross D Sc cutoff N β i j γ hij' hji M z).comp
          (contentPairInnerDotAt D Sc cutoff N β j i γ hji M z) := by
  exact sign_slide_reverse (k := k)
    (A := ((contentEPairTo D Sc cutoff N β j i γ hji).obj M).obj z)
    (B := ((contentEPairTo D Sc cutoff N β i j γ hij').obj M).obj z) _
    (contentEPair_distinct_slide_right D Sc cutoff N β hij γ hij' hji M z)

end OddMath.QuiverHecke.ELVOld


