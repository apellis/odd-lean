/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskeredMixedBraid

/-! # The uncorrected full-coefficient content braid

Brundan–Ellis Definition 1.5, the braid outside the repeated-outer correction
case. Both paths use the independent pair crossings and their induction
whiskerings. No local inverse or factor action is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private def crossingSign (i j : I) : k := by
  classical
  exact if i = j then -1 else 1

private theorem normalized_crossing (i j : I) :
    contentCrossAffine D Sc i j = crossingSign (k := k) i j • crossTwo D Sc i j := by
  classical
  by_cases h : i = j <;> simp [contentCrossAffine, crossingSign, h]

def contentNormalizedLeft (i j l : I) :=
  contentCrossAffine D Sc i j ▷ (pres D Sc).obj (ob D [l])
def contentNormalizedRight (i j l : I) :=
  (pres D Sc).obj (ob D [i]) ◁ contentCrossAffine D Sc j l

theorem contentNormalizedLeft_mem (i j l : I) :
    contentNormalizedLeft D Sc i j l ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
  MonoidalSupercategory.whiskerRight_mem (R := k) _ (contentCrossAffine_mem D Sc i j)
theorem contentNormalizedRight_mem (i j l : I) :
    contentNormalizedRight D Sc i j l ∈ parity (R := k) _ _ (D.parity j * D.parity l) :=
  MonoidalSupercategory.whiskerLeft_mem (R := k) _ (contentCrossAffine_mem D Sc j l)

/-- Both normalized source paths carry the same product of pair signs. -/
theorem contentNormalized_braid (i j l : I) (hb : ¬ (i = l ∧ i ≠ j)) :
    contentNormalizedLeft D Sc i j l ≫ contentNormalizedRight D Sc j i l ≫
        contentNormalizedLeft D Sc j l i =
      contentNormalizedRight D Sc i j l ≫ contentNormalizedLeft D Sc i l j ≫
        contentNormalizedRight D Sc l i j := by
  simp only [contentNormalizedLeft, contentNormalizedRight, normalized_crossing,
    MonoidalSupercategory.smul_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_smul (R := k),
    ← contentTripleLeft_whisker, ← contentTripleRight_whisker,
    Linear.smul_comp, Linear.comp_smul, smul_smul]
  have h := tripleCross_braid D Sc i j l hb ⟨[], rfl⟩
  change contentTripleLeft D Sc i j l ≫ contentTripleRight D Sc j i l ≫
      contentTripleLeft D Sc j l i =
    contentTripleRight D Sc i j l ≫ contentTripleLeft D Sc i l j ≫
      contentTripleRight D Sc l i j at h
  rw [h]
  congr 1
  ring

def contentWhiskeredBraidLeft (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :=
  let A := ((contentETripleMiddleIso D Sc cutoff N β i j l ((β + ([i] : Multiset I)) + ([j] : Multiset I)) γ rfl h0 (by rw [add_assoc, add_assoc]; exact h0)).inv.app M).total z ∘ₗ
      ((contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ (by rw [add_assoc, add_assoc]; exact h0)).map
        ((contentEPairCrossTransform D Sc cutoff N β i j ((β + ([i] : Multiset I)) + ([j] : Multiset I))
          ((contentPair_sum β i j).trans rfl)
          ((contentPair_sum β j i).trans (by ac_rfl))).app
          (D.parity i * D.parity j) M)).total z ∘ₗ
      ((contentETripleMiddleIso D Sc cutoff N β j i l ((β + ([i] : Multiset I)) + ([j] : Multiset I)) γ (by ac_rfl) h1 (by rw [add_assoc, add_assoc]; exact h0)).hom.app M).total z
  let B := contentWhiskeredSuffixCross D Sc cutoff N β j i l γ h1 h2 M z
  let C := ((contentETripleMiddleIso D Sc cutoff N β j l i ((β + ([j] : Multiset I)) + ([l] : Multiset I)) γ rfl h2 (by rw [add_assoc, add_assoc]; exact h2)).inv.app M).total z ∘ₗ
      ((contentInductionTo D Sc cutoff N ((β + ([j] : Multiset I)) + ([l] : Multiset I)) [i] γ (by rw [add_assoc, add_assoc]; exact h2)).map
        ((contentEPairCrossTransform D Sc cutoff N β j l ((β + ([j] : Multiset I)) + ([l] : Multiset I))
          ((contentPair_sum β j l).trans rfl)
          ((contentPair_sum β l j).trans (by ac_rfl))).app
          (D.parity j * D.parity l) M)).total z ∘ₗ
      ((contentETripleMiddleIso D Sc cutoff N β l j i ((β + ([j] : Multiset I)) + ([l] : Multiset I)) γ (by ac_rfl) h3 (by rw [add_assoc, add_assoc]; exact h2)).hom.app M).total z
  A.comp (B.comp C)

def contentWhiskeredBraidRight (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :=
  let A := contentWhiskeredSuffixCross D Sc cutoff N β i j l γ h0 h4 M z
  let B := ((contentETripleMiddleIso D Sc cutoff N β i l j ((β + ([i] : Multiset I)) + ([l] : Multiset I)) γ rfl h4 (by rw [add_assoc, add_assoc]; exact h4)).inv.app M).total z ∘ₗ
      ((contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([l] : Multiset I)) [j] γ (by rw [add_assoc, add_assoc]; exact h4)).map
        ((contentEPairCrossTransform D Sc cutoff N β i l ((β + ([i] : Multiset I)) + ([l] : Multiset I))
          ((contentPair_sum β i l).trans rfl)
          ((contentPair_sum β l i).trans (by ac_rfl))).app
          (D.parity i * D.parity l) M)).total z ∘ₗ
      ((contentETripleMiddleIso D Sc cutoff N β l i j ((β + ([i] : Multiset I)) + ([l] : Multiset I)) γ (by ac_rfl) h5 (by rw [add_assoc, add_assoc]; exact h4)).hom.app M).total z
  let C := contentWhiskeredSuffixCross D Sc cutoff N β l i j γ h5 h3 M z
  A.comp (B.comp C)

private theorem triple_transport_comp
    {β γ : Multiset I} {i j l a b c d e f g h q : I}
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([a,b,c] : Multiset I) = γ)
    (h2 : β + ([d,e,f] : Multiset I) = γ)
    (h3 : β + ([g,h,q] : Multiset I) = γ)
    {p0 p1 p2 : ZMod 2}
    {x : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    {y : (pres D Sc).obj (ob D [a,b,c]) ⟶ (pres D Sc).obj (ob D [d,e,f])}
    {t : (pres D Sc).obj (ob D [d,e,f]) ⟶ (pres D Sc).obj (ob D [g,h,q])}
    (hx : x ∈ parity (R := k) _ _ p0) (hy : y ∈ parity (R := k) _ _ p1)
    (ht : t ∈ parity (R := k) _ _ p2)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentETripleMap D Sc cutoff N h0 h1 hx M z).comp
      ((contentETripleMap D Sc cutoff N h1 h2 hy M z).comp
        (contentETripleMap D Sc cutoff N h2 h3 ht M z)) =
    (contentETripleEquiv D Sc cutoff N β i j l γ h0 M z).symm.toLinearMap ∘ₗ
      (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h0 h1 hx) M z).comp
        ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h1 h2 hy) M z).comp
          (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h2 h3 ht) M z)) ∘ₗ
      (contentETripleEquiv D Sc cutoff N β g h q γ h3 M z).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [contentETripleMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- The entire uncorrected braid on the independent pair crossings, including
all-equal and adjacent-equal triples as well as pairwise distinct colours. -/
theorem contentWhiskered_braid (β : Multiset I) (i j l : I)
    (hb : ¬ (i = l ∧ i ≠ j)) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredBraidLeft D Sc cutoff N β i j l γ h0 h1 h2 h3 M z =
      contentWhiskeredBraidRight D Sc cutoff N β i j l γ h0 h4 h5 h3 M z := by
  have hL : contentWhiskeredBraidLeft D Sc cutoff N β i j l γ h0 h1 h2 h3 M z =
      (contentETripleMap D Sc cutoff N h0 h1 (contentNormalizedLeft_mem D Sc i j l) M z).comp
        ((contentETripleMap D Sc cutoff N h1 h2 (contentNormalizedRight_mem D Sc j i l) M z).comp
          (contentETripleMap D Sc cutoff N h2 h3 (contentNormalizedLeft_mem D Sc j l i) M z)) := by
    exact congrArg₂ LinearMap.comp (contentETripleMap_prefix_cross D Sc cutoff N β i j l
      ((β + ([i] : Multiset I)) + ([j] : Multiset I)) γ rfl (by ac_rfl)
      h0 h1 (by rw [add_assoc, add_assoc]; exact h0) M z).symm
      (congrArg₂ LinearMap.comp
        (contentWhiskeredSuffixCross_comparison D Sc cutoff N β j i l γ h1 h2 M z)
        (contentETripleMap_prefix_cross D Sc cutoff N β j l i
      ((β + ([j] : Multiset I)) + ([l] : Multiset I)) γ rfl (by ac_rfl)
      h2 h3 (by rw [add_assoc, add_assoc]; exact h2) M z).symm)
  have hR : contentWhiskeredBraidRight D Sc cutoff N β i j l γ h0 h4 h5 h3 M z =
      (contentETripleMap D Sc cutoff N h0 h4 (contentNormalizedRight_mem D Sc i j l) M z).comp
        ((contentETripleMap D Sc cutoff N h4 h5 (contentNormalizedLeft_mem D Sc i l j) M z).comp
          (contentETripleMap D Sc cutoff N h5 h3 (contentNormalizedRight_mem D Sc l i j) M z)) := by
    exact congrArg₂ LinearMap.comp
      (contentWhiskeredSuffixCross_comparison D Sc cutoff N β i j l γ h0 h4 M z)
      (congrArg₂ LinearMap.comp (contentETripleMap_prefix_cross D Sc cutoff N β i l j
      ((β + ([i] : Multiset I)) + ([l] : Multiset I)) γ rfl (by ac_rfl)
      h4 h5 (by rw [add_assoc, add_assoc]; exact h4) M z).symm
        (contentWhiskeredSuffixCross_comparison D Sc cutoff N β l i j γ h5 h3 M z))
  rw [hL, hR, triple_transport_comp, triple_transport_comp]
  congr 2
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentTripleTransform_tensor, contentTripleTransform_tensor]
  have hs : (D.parity i * D.parity l) * (D.parity j * D.parity l) +
      (D.parity i * D.parity j) *
        (D.parity i * D.parity l + D.parity j * D.parity l) =
      (D.parity i * D.parity l) * (D.parity i * D.parity j) +
      (D.parity j * D.parity l) *
        (D.parity i * D.parity l + D.parity i * D.parity j) := by ring
  have hp : D.parity i * D.parity j +
      (D.parity i * D.parity l + D.parity j * D.parity l) =
      D.parity j * D.parity l +
        (D.parity i * D.parity l + D.parity i * D.parity j) := by ring
  rw [hs, hp, contentNormalized_braid D Sc i j l hb]
  all_goals first
    | exact contentNormalizedLeft_mem D Sc _ _ _
    | exact contentNormalizedRight_mem D Sc _ _ _
end OddMath.QuiverHecke.ELVOld
