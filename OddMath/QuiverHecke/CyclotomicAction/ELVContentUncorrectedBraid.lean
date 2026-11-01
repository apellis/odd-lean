/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization

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
  contentTriplePrefixAffine D Sc i j l
def contentNormalizedRight (i j l : I) :=
  (pres D Sc).obj (ob D [i]) ◁ contentCrossAffine D Sc j l

theorem contentNormalizedLeft_mem (i j l : I) :
    contentNormalizedLeft D Sc i j l ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
  contentTriplePrefixAffine_mem D Sc i j l
theorem contentNormalizedRight_mem (i j l : I) :
    contentNormalizedRight D Sc i j l ∈ parity (R := k) _ _ (D.parity j * D.parity l) :=
  MonoidalSupercategory.whiskerLeft_mem (R := k) _ (contentCrossAffine_mem D Sc j l)

/-- Both normalized source paths carry the same product of pair signs. -/
theorem contentNormalized_braid (i j l : I) (hb : ¬ (i = l ∧ i ≠ j)) :
    contentNormalizedLeft D Sc i j l ≫ contentNormalizedRight D Sc j i l ≫
        contentNormalizedLeft D Sc j l i =
      contentNormalizedRight D Sc i j l ≫ contentNormalizedLeft D Sc i l j ≫
        contentNormalizedRight D Sc l i j := by
  simp only [contentNormalizedLeft, contentTriplePrefixAffine_eq_whisker,
    contentNormalizedRight, normalized_crossing,
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
    (δij : Multiset I)
    (hij : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hji : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([l] : Multiset I) = γ)
    (δjl : Multiset I)
    (hjl : (β + ([j] : Multiset I)) + ([l] : Multiset I) = δjl)
    (hlj : (β + ([l] : Multiset I)) + ([j] : Multiset I) = δjl)
    (hjlγ : δjl + ([i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentETripleTo D Sc cutoff N β l j i γ h3).obj M).obj z ⟶
      ((contentETripleTo D Sc cutoff N β i j l γ h0).obj M).obj z :=
  (contentPrefixCrossComponent D Sc cutoff N β j l i δjl γ hjl hlj h2 h3 hjlγ M z ≫
    contentWhiskeredSuffixCross D Sc cutoff N β j i l γ h1 h2 M z) ≫
    contentPrefixCrossComponent D Sc cutoff N β i j l δij γ hij hji h0 h1 hijγ M z

def contentWhiskeredBraidRight (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (δil : Multiset I)
    (hil : (β + ([i] : Multiset I)) + ([l] : Multiset I) = δil)
    (hli : (β + ([l] : Multiset I)) + ([i] : Multiset I) = δil)
    (hilγ : δil + ([j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentETripleTo D Sc cutoff N β l j i γ h3).obj M).obj z ⟶
      ((contentETripleTo D Sc cutoff N β i j l γ h0).obj M).obj z :=
  (contentWhiskeredSuffixCross D Sc cutoff N β l i j γ h5 h3 M z ≫
    contentPrefixCrossComponent D Sc cutoff N β i l j δil γ hil hli h4 h5 hilγ M z) ≫
    contentWhiskeredSuffixCross D Sc cutoff N β i j l γ h0 h4 M z

private theorem uncorrected_comp3_congr {A B C E : SVec.{u} k}
    {f f' : A ⟶ B} {g g' : B ⟶ C} {h h' : C ⟶ E}
    (hf : f = f') (hg : g = g') (hh : h = h') :
    (f ≫ g) ≫ h = (f' ≫ g') ≫ h' := by
  cases hf
  cases hg
  cases hh
  rfl

private theorem four_equivalences_comp
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type u}
    [AddCommGroup A₀] [Module k A₀] [AddCommGroup A₁] [Module k A₁]
    [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₀] [Module k B₀] [AddCommGroup B₁] [Module k B₁]
    [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (e₀ : A₀ ≃ₗ[k] B₀) (e₁ : A₁ ≃ₗ[k] B₁)
    (e₂ : A₂ ≃ₗ[k] B₂) (e₃ : A₃ ≃ₗ[k] B₃)
    (a : B₁ →ₗ[k] B₀) (b : B₂ →ₗ[k] B₁) (c : B₃ →ₗ[k] B₂) :
    (e₀.symm.toLinearMap.comp (a.comp e₁.toLinearMap)).comp
      ((e₁.symm.toLinearMap.comp (b.comp e₂.toLinearMap)).comp
        (e₂.symm.toLinearMap.comp (c.comp e₃.toLinearMap))) =
    e₀.symm.toLinearMap ∘ₗ (a.comp (b.comp c)) ∘ₗ e₃.toLinearMap := by
  apply LinearMap.ext
  intro v
  change e₀.symm (a (e₁ (e₁.symm (b (e₂ (e₂.symm (c (e₃ v)))))))) =
    e₀.symm (a (b (c (e₃ v))))
  rw [e₁.apply_symm_apply, e₂.apply_symm_apply]

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
  exact four_equivalences_comp
    (contentETripleEquiv D Sc cutoff N β i j l γ h0 M z)
    (contentETripleEquiv D Sc cutoff N β a b c γ h1 M z)
    (contentETripleEquiv D Sc cutoff N β d e f γ h2 M z)
    (contentETripleEquiv D Sc cutoff N β g h q γ h3 M z)
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h0 h1 hx) M z)
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h1 h2 hy) M z)
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h2 h3 ht) M z)

private theorem normalized_block_braid (β : Multiset I) (i j l : I)
    (hb : ¬ (i = l ∧ i ≠ j)) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h0 h1 (contentNormalizedLeft_mem D Sc i j l)) M z).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h1 h2 (contentNormalizedRight_mem D Sc j i l)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h2 h3 (contentNormalizedLeft_mem D Sc j l i)) M z)) =
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h0 h4 (contentNormalizedRight_mem D Sc i j l)) M z).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h4 h5 (contentNormalizedLeft_mem D Sc i l j)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h5 h3 (contentNormalizedRight_mem D Sc l i j)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,j,l]) (τ := [j,i,l]) (υ := [j,l,i]) (ω := [l,j,i])
    h0 h1 h2 h3
    (contentNormalizedLeft_mem D Sc i j l) (contentNormalizedRight_mem D Sc j i l) (contentNormalizedLeft_mem D Sc j l i) M z v h m]
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,j,l]) (τ := [i,l,j]) (υ := [l,i,j]) (ω := [l,j,i])
    h0 h4 h5 h3
    (contentNormalizedRight_mem D Sc i j l) (contentNormalizedLeft_mem D Sc i l j) (contentNormalizedRight_mem D Sc l i j) M z v h m]
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

private theorem normalized_map_braid (β : Multiset I) (i j l : I)
    (hb : ¬ (i = l ∧ i ≠ j)) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (contentETripleMap D Sc cutoff N h0 h1 (contentNormalizedLeft_mem D Sc i j l) M z).comp
      ((contentETripleMap D Sc cutoff N h1 h2 (contentNormalizedRight_mem D Sc j i l) M z).comp
        (contentETripleMap D Sc cutoff N h2 h3 (contentNormalizedLeft_mem D Sc j l i) M z)) =
    (contentETripleMap D Sc cutoff N h0 h4 (contentNormalizedRight_mem D Sc i j l) M z).comp
      ((contentETripleMap D Sc cutoff N h4 h5 (contentNormalizedLeft_mem D Sc i l j) M z).comp
        (contentETripleMap D Sc cutoff N h5 h3 (contentNormalizedRight_mem D Sc l i j) M z)) := by
  have hL := triple_transport_comp D Sc cutoff N
    (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := j) (b := i) (c := l) (d := j) (e := l) (f := i)
    (g := l) (h := j) (q := i) h0 h1 h2 h3
    (contentNormalizedLeft_mem D Sc i j l) (contentNormalizedRight_mem D Sc j i l) (contentNormalizedLeft_mem D Sc j l i) M z
  have hR := triple_transport_comp D Sc cutoff N
    (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := i) (b := l) (c := j) (d := l) (e := i) (f := j)
    (g := l) (h := j) (q := i) h0 h4 h5 h3
    (contentNormalizedRight_mem D Sc i j l) (contentNormalizedLeft_mem D Sc i l j) (contentNormalizedRight_mem D Sc l i j) M z
  have hB := normalized_block_braid D Sc cutoff N β i j l hb γ h0 h1 h2 h3 h4 h5 M z
  have hMid := congrArg
    (fun t => (contentETripleEquiv D Sc cutoff N β i j l γ h0 M z).symm.toLinearMap ∘ₗ
      t ∘ₗ (contentETripleEquiv D Sc cutoff N β l j i γ h3 M z).toLinearMap) hB
  exact hL.trans (hMid.trans hR.symm)

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
    (δij : Multiset I)
    (hij : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hji : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([l] : Multiset I) = γ)
    (δil : Multiset I)
    (hil : (β + ([i] : Multiset I)) + ([l] : Multiset I) = δil)
    (hli : (β + ([l] : Multiset I)) + ([i] : Multiset I) = δil)
    (hilγ : δil + ([j] : Multiset I) = γ)
    (δjl : Multiset I)
    (hjl : (β + ([j] : Multiset I)) + ([l] : Multiset I) = δjl)
    (hlj : (β + ([l] : Multiset I)) + ([j] : Multiset I) = δjl)
    (hjlγ : δjl + ([i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredBraidLeft D Sc cutoff N β i j l γ h0 h1 h2 h3
      δij hij hji hijγ δjl hjl hlj hjlγ M z =
      contentWhiskeredBraidRight D Sc cutoff N β i j l γ h0 h4 h5 h3
      δil hil hli hilγ M z := by
  have hL : contentWhiskeredBraidLeft D Sc cutoff N β i j l γ h0 h1 h2 h3
      δij hij hji hijγ δjl hjl hlj hjlγ M z =
      (contentETripleMap D Sc cutoff N h0 h1 (contentNormalizedLeft_mem D Sc i j l) M z).comp
        ((contentETripleMap D Sc cutoff N h1 h2 (contentNormalizedRight_mem D Sc j i l) M z).comp
          (contentETripleMap D Sc cutoff N h2 h3 (contentNormalizedLeft_mem D Sc j l i) M z)) := by
    exact (uncorrected_comp3_congr
      (contentETripleMap_prefix_cross D Sc cutoff N β j l i
        δjl γ hjl hlj h2 h3 hjlγ M z).symm
      (contentWhiskeredSuffixCross_comparison D Sc cutoff N β j i l γ h1 h2 M z)
      (contentETripleMap_prefix_cross D Sc cutoff N β i j l
        δij γ hij hji h0 h1 hijγ M z).symm).trans (by rfl)

  have hR : contentWhiskeredBraidRight D Sc cutoff N β i j l γ h0 h4 h5 h3
      δil hil hli hilγ M z =
      (contentETripleMap D Sc cutoff N h0 h4 (contentNormalizedRight_mem D Sc i j l) M z).comp
        ((contentETripleMap D Sc cutoff N h4 h5 (contentNormalizedLeft_mem D Sc i l j) M z).comp
          (contentETripleMap D Sc cutoff N h5 h3 (contentNormalizedRight_mem D Sc l i j) M z)) := by
    exact (uncorrected_comp3_congr
      (contentWhiskeredSuffixCross_comparison D Sc cutoff N β l i j γ h5 h3 M z)
      (contentETripleMap_prefix_cross D Sc cutoff N β i l j
        δil γ hil hli h4 h5 hilγ M z).symm
      (contentWhiskeredSuffixCross_comparison D Sc cutoff N β i j l γ h0 h4 M z)).trans (by rfl)

  exact hL.trans ((normalized_map_braid D Sc cutoff N β i j l hb γ
    h0 h1 h2 h3 h4 h5 M z).trans hR.symm)
end OddMath.QuiverHecke.ELVOld
