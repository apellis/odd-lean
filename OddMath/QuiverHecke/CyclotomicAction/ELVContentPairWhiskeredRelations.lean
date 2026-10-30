/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering

/-! # Whiskered single-letter dots and the pair quadratic

The canonical transported positioned dots equal independently constructed
single-letter actions. The inner dot uses induction on the existing
`contentInductionDot`; the outer dot retains the explicit target-content
recast. The original-Sc ordered quadratic is consequently a relation in
these independently whiskered dots, not merely in conjugated block dots.
Triple crossing and associativity coherence are separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem conj_of_square {A B : Type u} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] (e : A ≃ₗ[k] B)
    (a : Module.End k A) (b : Module.End k B)
    (h : e.toLinearMap ∘ₗ a = b ∘ₗ e.toLinearMap) : e.symm.conjAlgEquiv k b = a := by
  apply LinearMap.ext
  intro x
  apply e.injective
  change e (e.symm (b (e x))) = e (a x)
  rw [e.apply_symm_apply]
  exact (congrArg (fun f : A →ₗ[k] B => f x) h).symm

private theorem endLinear_source_congr {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ p)
    (hab : a = b) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    contentInductionEndLinear D Sc cutoff N ha M w =
      contentInductionEndLinear D Sc cutoff N hb M w := by
  cases hab
  rfl

theorem contentEPairDot_zero_whisker (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    contentEPairDot D Sc cutoff N β i j M w 0 =
      BalancedInduction.mapComponent
        (contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j]
          (β + ([i,j] : Multiset I)) (by rw [add_assoc]; rfl))
        (BalancedInduction.transformComponent
          (contentAppendTo_supernatural D Sc cutoff N rfl rfl (firstDot_parity D Sc i [])) M)
        (D.parity i) w := by
  unfold contentEPairDot
  simp only [ite_true]
  apply conj_of_square
  have h := contentInductionComp_inner D Sc cutoff N β [i] [j]
    (β + ([i,j] : Multiset I)) (by rw [add_assoc]; rfl) rfl (firstDot_parity D Sc i []) M w
  have he := endLinear_source_congr D Sc cutoff N
    (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
      (firstDot_parity D Sc i [])) (firstDot_parity D Sc i [j])
    (dotE_whiskerRight D Sc [i] [j] 0 (by simp)) M w
  exact h.trans (congrArg (fun f => f ∘ₗ
    (contentEPairEquiv D Sc cutoff N β i j _ rfl M w).toLinearMap) he)

theorem contentEPairDot_one_whisker (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    contentEPairDot D Sc cutoff N β i j M w 1 =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N
          (β := β + ([i] : Multiset I))
          (γ := β + ([i,j] : Multiset I))
          (by rw [add_assoc]; rfl) (by rw [add_assoc]; rfl) (firstDot_parity D Sc j []))
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β [i] _ rfl) M) w := by
  unfold contentEPairDot
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false]
  apply conj_of_square
  have h := contentInductionComp_outer D Sc cutoff N β [i] [j]
    (β + ([i,j] : Multiset I)) (by rw [add_assoc]; rfl) rfl (firstDot_parity D Sc j []) M w
  have he := endLinear_source_congr D Sc cutoff N
    (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
      (firstDot_parity D Sc j [])) (contentPairDot_one_parity D Sc i j)
    (whiskerLeft_letter_dotE D Sc i [j] 0) M w
  exact h.trans (congrArg (fun f => f ∘ₗ
    (contentEPairEquiv D Sc cutoff N β i j _ rfl M w).toLinearMap) he)

theorem contentInductionDot_component (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β) :
    (contentInductionDot D Sc cutoff N β i).app (D.parity i) M =
      BalancedInduction.transformComponent
        (contentAppendTo_supernatural D Sc cutoff N rfl rfl (firstDot_parity D Sc i [])) M := by
  exact congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N rfl rfl (firstDot_parity D Sc i [])))) M

theorem contentEPairDot_zero_singleLetter (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    contentEPairDot D Sc cutoff N β i j M w 0 =
      BalancedInduction.mapComponent
        (contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j]
          (β + ([i,j] : Multiset I)) (by rw [add_assoc]; rfl))
        ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M)
        (D.parity i) w := by
  rw [contentInductionDot_component]
  exact contentEPairDot_zero_whisker D Sc cutoff N β i j M w

/-- The first single-letter dot, independently acted on by the second induction. -/
def contentEPairInnerDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j _ rfl M w) :=
  BalancedInduction.mapComponent
    (contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j]
      (β + ([i,j] : Multiset I)) (by rw [add_assoc]; rfl))
    ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M) (D.parity i) w

/-- The second single-letter dot at the explicitly recast target content. -/
def contentEPairOuterDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j _ rfl M w) :=
  BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N
      (β := β + ([i] : Multiset I)) (γ := β + ([i,j] : Multiset I))
      (by rw [add_assoc]; rfl) (by rw [add_assoc]; rfl) (firstDot_parity D Sc j []))
    (BalancedInduction.induced (contentAppendTo D Sc cutoff N β [i] _ rfl) M) w

theorem contentEPairDot_zero_eq_inner (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    contentEPairDot D Sc cutoff N β i j M w 0 = contentEPairInnerDot D Sc cutoff N β i j M w :=
  contentEPairDot_zero_singleLetter D Sc cutoff N β i j M w

theorem contentEPairDot_one_eq_outer (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    contentEPairDot D Sc cutoff N β i j M w 1 = contentEPairOuterDot D Sc cutoff N β i j M w :=
  contentEPairDot_one_whisker D Sc cutoff N β i j M w

/-- Original-Sc quadratic in the independently whiskered single-letter dots. -/
theorem contentEPair_whiskered_quadratic (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    let A := contentEPairInnerDot D (parameterTwist D Sc) cutoff N β i j M w
    let B := contentEPairOuterDot D (parameterTwist D Sc) cutoff N β i j M w
    (contentEPairCross D (parameterTwist D Sc) cutoff N β i j _ rfl
        (content_pair_swap β i j) M w).comp
      (contentEPairCross D (parameterTwist D Sc) cutoff N β j i _
        (content_pair_swap β i j) rfl M w) =
    if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
      ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j r s • (B ^ s * A ^ r) +
      ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i) := by
  dsimp only
  rw [contentEPair_quadratic D Sc cutoff N β hij]
  unfold contentEPairPolynomial
  rw [contentEPairDot_zero_eq_inner, contentEPairDot_one_eq_outer]

end OddMath.QuiverHecke.ELVOld
