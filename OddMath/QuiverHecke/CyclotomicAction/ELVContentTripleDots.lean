/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations

/-! # Three independently whiskered single-letter dots -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem transport_two_squares
    {A B C : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] (e : A ≃ₗ[k] B) (f : B ≃ₗ[k] C)
    (a : Module.End k A) (b : Module.End k B) (c : Module.End k C)
    (he : e.toLinearMap ∘ₗ a = b ∘ₗ e.toLinearMap)
    (hf : f.toLinearMap ∘ₗ b = c ∘ₗ f.toLinearMap) :
    (e.trans f).symm.toLinearMap ∘ₗ c ∘ₗ (e.trans f).toLinearMap = a := by
  ext x
  apply (e.trans f).injective
  change f (e (e.symm (f.symm (c (f (e x)))))) = f (e (a x))
  rw [e.apply_symm_apply, f.apply_symm_apply]
  have he' := congrArg (fun q : A →ₗ[k] B => q x) he
  have hf' := congrArg (fun q : B →ₗ[k] C => q (e x)) hf
  exact hf'.symm.trans (congrArg f he'.symm)

private theorem naturalIso_total_square
    {B : Type*} [Category* B] {T : Type u} [Category.{u} T]
    [Preadditive T] [Linear k T] [Supercategory k T]
    {F G : B ⥤ Superfunctor k T (SVec k)} (e : F ≅ G) {M : B} (a : M ⟶ M) (z : T) :
    (moduleIsoLinearEquiv (e.app M) z).toLinearMap ∘ₗ (F.map a).total z =
      (G.map a).total z ∘ₗ (moduleIsoLinearEquiv (e.app M) z).toLinearMap := by
  have h := congrArg (fun q => q.total z) (e.hom.naturality a)
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at h
  apply LinearMap.ext
  intro x
  exact congrArg (fun q => q x) h

private theorem induction_total_homogeneous
    {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {F G : Superfunctor k C (SVec k)} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : B) :
    ((BalancedInduction.induction J).map f).total z = BalancedInduction.mapComponent J f p z := by
  have hm := Supercategory.map_mem (BalancedInduction.induction J) hf
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 1) (by decide), add_zero]
    rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 0) (by decide), zero_add]
    rfl

private theorem source_transform_congr {β γ : Multiset I} {σ : List I}
    (h : β + (σ : Multiset I) = γ) {p : ZMod 2}
    {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ p) (hab : a = b)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h ha) M z =
      BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h hb) M z := by
  cases hab
  rfl

/-- First single-letter dot acted on by both following single-letter inductions. -/
def contentWhiskeredFirstDot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j l γ h M z) :=
  ((contentEPairTo D Sc cutoff N (β + ([i] : Multiset I)) j l γ
      (by rw [add_assoc]; exact h)).map
    ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M)).total z

theorem contentETripleMap_first_dot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h h (firstDot_parity D Sc i [j,l]) M z =
      contentWhiskeredFirstDot D Sc cutoff N β i j l γ h M z := by
  let hs : (β + ([i] : Multiset I)) + ([j,l] : Multiset I) = γ := by
    rw [add_assoc]; exact h
  unfold contentETripleMap contentWhiskeredFirstDot
  rw [contentETripleEquiv_suffix D Sc cutoff N β i j l γ h hs]
  apply transport_two_squares
  · exact naturalIso_total_square
      (contentEPairToComparison D Sc cutoff N (β + ([i] : Multiset I)) j l γ hs)
      ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M) z
  · rw [contentInductionDot_component,
      induction_total_homogeneous _ (BalancedInduction.transformComponent_mem _ _)]
    have hc := contentInductionComp_inner D Sc cutoff N β [i] [j,l]
      γ hs h (firstDot_parity D Sc i []) M z
    have he := source_transform_congr D Sc cutoff N h
      (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j,l]))
        (firstDot_parity D Sc i [])) (firstDot_parity D Sc i [j,l])
      (dotE_whiskerRight D Sc [i] [j,l] 0 (by simp)) M z
    exact hc.trans (congrArg (fun q => q ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β [i] [j,l] γ hs h).app M) z).toLinearMap) he)
/-- Middle single-letter dot acted on by the final single-letter induction. -/
def contentWhiskeredMiddleDot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j l γ h M z) :=
  ((contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
      (by rw [add_assoc, add_assoc]; exact h)).map
    ((contentInductionDot D Sc cutoff N (β + ([i] : Multiset I)) j).app (D.parity j)
      (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M))).total z

/-- Last single-letter dot on the already twice-induced module. -/
def contentWhiskeredLastDot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j l γ h M z) :=
  BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N
      (β := (β + ([i] : Multiset I)) + ([j] : Multiset I)) (γ := γ)
      (by rw [add_assoc, add_assoc]; exact h) (by rw [add_assoc, add_assoc]; exact h)
      (firstDot_parity D Sc l []))
    (BalancedInduction.induced (contentAppend D Sc cutoff N (β + ([i] : Multiset I)) [j])
      (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M)) z

theorem contentETripleMap_middle_dot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h h
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [l]))
          (firstDot_parity D Sc j []))) M z =
      contentWhiskeredMiddleDot D Sc cutoff N β i j l γ h M z := by
  let hs : (β + ([i] : Multiset I)) + ([j,l] : Multiset I) = γ := by
    rw [add_assoc]; exact h
  let hl : ((β + ([i] : Multiset I)) + ([j] : Multiset I)) + ([l] : Multiset I) = γ := by
    rw [add_assoc, add_assoc]; exact h
  unfold contentETripleMap contentWhiskeredMiddleDot
  rw [contentETripleEquiv_suffix D Sc cutoff N β i j l γ h hs]
  apply transport_two_squares
    (b := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N hs hs
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [l]))
          (firstDot_parity D Sc j [])))
      (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M) z)
  · rw [contentInductionDot_component,
      induction_total_homogeneous _ (BalancedInduction.transformComponent_mem _ _)]
    exact contentInductionComp_inner D Sc cutoff N (β + ([i] : Multiset I)) [j] [l]
      γ hl hs (firstDot_parity D Sc j [])
      (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M) z
  · exact contentInductionComp_outer D Sc cutoff N β [i] [j,l] γ hs h
      (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [l]))
        (firstDot_parity D Sc j [])) M z

theorem contentETripleMap_last_dot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h h
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc l []))) M z =
      contentWhiskeredLastDot D Sc cutoff N β i j l γ h M z := by
  let hs : (β + ([i] : Multiset I)) + ([j,l] : Multiset I) = γ := by
    rw [add_assoc]; exact h
  let hl : ((β + ([i] : Multiset I)) + ([j] : Multiset I)) + ([l] : Multiset I) = γ := by
    rw [add_assoc, add_assoc]; exact h
  unfold contentETripleMap contentWhiskeredLastDot
  rw [contentETripleEquiv_suffix D Sc cutoff N β i j l γ h hs]
  apply transport_two_squares
    (b := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N hs hs
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc l [])))
      (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M) z)
  · exact contentInductionComp_outer D Sc cutoff N (β + ([i] : Multiset I)) [j] [l]
      γ hl hs (firstDot_parity D Sc l [])
      (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M) z
  · exact contentInductionComp_outer D Sc cutoff N β [i] [j,l] γ hs h
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
        (firstDot_parity D Sc l [])) M z
private theorem tripleDotMap_congr {β γ : Multiset I} {i j l : I}
    (h : β + ([i,j,l] : Multiset I) = γ) {p : ZMod 2}
    {a b : End ((pres D Sc).obj (ob D [i,j,l]))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ p) (hab : a = b)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h h ha M z = contentETripleMap D Sc cutoff N h h hb M z := by
  cases hab
  rfl

private theorem tripleDotMap_end {β : Multiset I} {i j l : I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D [i,j,l]))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,l] : Multiset I))) :
    (contentETripleEquiv D Sc cutoff N β i j l _ rfl M z).symm.conjAlgEquiv k
      (contentInductionEndLinear D Sc cutoff N ha M z) =
      contentETripleMap D Sc cutoff N rfl rfl ha M z := by
  rw [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.symm_symm]
  rfl

theorem contentETripleDot_first (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETripleDot D Sc cutoff N β i j M z 0 =
      contentWhiskeredFirstDot D Sc cutoff N β i j i _ rfl M z := by
  simp only [contentETripleDot, ↓reduceIte, tripleDotMap_end]
  exact contentETripleMap_first_dot D Sc cutoff N β i j i _ rfl M z

theorem contentETripleDot_middle (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETripleDot D Sc cutoff N β i j M z 1 =
      contentWhiskeredMiddleDot D Sc cutoff N β i j i _ rfl M z := by
  simp only [contentETripleDot, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, tripleDotMap_end]
  refine (tripleDotMap_congr D Sc cutoff N rfl (contentTripleDot_one_parity D Sc i j)
    (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
      (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (firstDot_parity D Sc j []))) ?_ M z).trans
    (contentETripleMap_middle_dot D Sc cutoff N β i j i _ rfl M z)
  rw [dotE_whiskerRight D Sc [j] [i] 0 (by simp), whiskerLeft_letter_dotE]
  rfl

theorem contentETripleDot_last (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETripleDot D Sc cutoff N β i j M z 2 =
      contentWhiskeredLastDot D Sc cutoff N β i j i _ rfl M z := by
  simp only [contentETripleDot, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, tripleDotMap_end]
  refine (tripleDotMap_congr D Sc cutoff N rfl (contentTripleDot_two_parity D Sc i j)
    (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
        (firstDot_parity D Sc i []))) ?_ M z).trans
    (contentETripleMap_last_dot D Sc cutoff N β i j i _ rfl M z)
  rw [whiskerLeft_letter_dotE, whiskerLeft_letter_dotE]

/-- Ordered correction formed from the three independent single-letter dots. -/
def contentWhiskeredDotSum (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M z) :=
  let A := contentWhiskeredFirstDot D Sc cutoff N β i j i _ rfl M z
  let B := contentWhiskeredMiddleDot D Sc cutoff N β i j i _ rfl M z
  let C := contentWhiskeredLastDot D Sc cutoff N β i j i _ rfl M z
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) • (C^(r-1-l)*B^s*A^l)

theorem contentETripleDotSum_whiskered (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETripleDotSum D Sc cutoff N β i j r s d M z =
      contentWhiskeredDotSum D Sc cutoff N β i j r s d M z := by
  simp only [contentETripleDotSum, contentWhiskeredDotSum,
    contentETripleDot_first, contentETripleDot_middle, contentETripleDot_last]

/-- The coefficients are the original Sc, not its parameter twist. -/
def contentWhiskeredPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (z : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D (parameterTwist D Sc) cutoff N β i j i _ rfl M z) :=
  contentWhiskeredDotSum D (parameterTwist D Sc) cutoff N β i j (D.dn i j) 0 (Sc.t i j : k) M z +
    ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
      contentWhiskeredDotSum D (parameterTwist D Sc) cutoff N β i j r s (Sc.s i j r s) M z

theorem contentETriplePolynomial_whiskered (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (z : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETriplePolynomial D Sc cutoff N β i j M z =
      contentWhiskeredPolynomial D Sc cutoff N β i j M z := by
  simp only [contentETriplePolynomial, contentWhiskeredPolynomial, contentETripleDotSum_whiskered]
end OddMath.QuiverHecke.ELVOld
