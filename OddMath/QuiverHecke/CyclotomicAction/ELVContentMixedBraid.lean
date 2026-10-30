/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentOperatorQuadratic
import OddMath.QuiverHecke.CyclotomicAction.BraidOperators

/-! # Common-content mixed braid and its source correction

`DeformedMixedBraid.md` §2, equations (4)–(5), for the induction operators
needed by `DeformedActionAssembly.md` §6. The two middle equal-colour
crossings carry minus signs. The contravariant transforms use the three
words with common content, not endomorphism substitutes. Their difference
is the signed source correction, with the residual outside-colour twist
on the entire kernel morphism. The ordered dotted polynomial comparison
with the original parameters is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentTripleTransform_tensor {β γ : Multiset I} {σ τ υ ω : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (hυ : β + (υ : Multiset I) = γ) (hω : β + (ω : Multiset I) = γ)
    {p q r : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    {b : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D υ)}
    {c : (pres D Sc).obj (ob D υ) ⟶ (pres D Sc).obj (ob D ω)}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ r)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β ω γ hω).obj v ⟶ w) (m : M.obj v) :
    ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M w).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hτ hυ hb) M w).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hυ hω hc) M w)))
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β ω γ hω) M.toFunctor v h m) =
    sign k (q*r + p*(q+r)) •
      BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ) M.toFunctor v
        (contentAppendToComponent D Sc cutoff N hσ hω (a ≫ b ≫ c) v ≫
          twist k (p+(q+r)) h) m := by
  rw [BalancedInduction.transformLinear_comp, LinearMap.comp_smul,
    BalancedInduction.transformLinear_comp, smul_smul, ← sign_add,
    LinearMap.smul_apply, BalancedInduction.transformLinear_tensor]
  congr 2
  change (contentAppendToComponent D Sc cutoff N hσ hτ a v ≫
    contentAppendToComponent D Sc cutoff N hτ hυ b v ≫
    contentAppendToComponent D Sc cutoff N hυ hω c v) ≫ _ = _
  rw [contentAppendToComponent_comp D Sc cutoff N hτ hυ hω b hc,
    contentAppendToComponent_comp D Sc cutoff N hσ hτ hω a (comp_mem hb hc)]

theorem content_triple_iij (β : Multiset I) (i j : I) :
    β + ([i,i,j] : Multiset I) = β + ([i,j,i] : Multiset I) := by
  congr 1
  change i ::ₘ i ::ₘ j ::ₘ (0 : Multiset I) = i ::ₘ j ::ₘ i ::ₘ 0
  rw [Multiset.cons_swap i j]

theorem content_triple_jii (β : Multiset I) (i j : I) :
    β + ([j,i,i] : Multiset I) = β + ([i,j,i] : Multiset I) := by
  congr 1
  change j ::ₘ i ::ₘ i ::ₘ (0 : Multiset I) = i ::ₘ j ::ₘ i ::ₘ 0
  exact Multiset.cons_swap _ _ _

def contentTripleLeft (i j c : I) :
    (pres D Sc).obj (ob D [i,j,c]) ⟶ (pres D Sc).obj (ob D [j,i,c]) :=
  tripleCrossLeft D Sc i j c ⟨[], rfl⟩
def contentTripleRight (i j c : I) :
    (pres D Sc).obj (ob D [i,j,c]) ⟶ (pres D Sc).obj (ob D [i,c,j]) :=
  tripleCrossRight D Sc i j c ⟨[], rfl⟩
theorem contentTripleLeft_parity (i j c : I) :
    contentTripleLeft D Sc i j c ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
  tripleCrossLeft_parity D Sc i j c ⟨[], rfl⟩
theorem contentTripleRight_parity (i j c : I) :
    contentTripleRight D Sc i j c ∈ parity (R := k) _ _ (D.parity j * D.parity c) :=
  tripleCrossRight_parity D Sc i j c ⟨[], rfl⟩
def contentBraidCorrection (i j : I) : End ((pres D Sc).obj (ob D [i,j,i])) :=
  tripleBraidCorrection D Sc i j ⟨[], rfl⟩
theorem contentTriple_braid (i j : I) (hij : i ≠ j) :
    (contentTripleLeft D Sc i j i ≫ contentTripleRight D Sc j i i ≫ contentTripleLeft D Sc j i i) -
    (contentTripleRight D Sc i j i ≫ contentTripleLeft D Sc i i j ≫ contentTripleRight D Sc i i j) =
      contentBraidCorrection D Sc i j :=
  tripleCross_braid_correction D Sc i j hij ⟨[], rfl⟩

/-- Normalized mixed braid difference on one common content. -/
def contentMixedBraid (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :=
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_iij β i j)
      (contentTripleRight_parity D Sc i j i)) M w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j)
      (content_triple_iij β i j) (contentTripleLeft_parity D Sc i i j)) M w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) rfl
      (contentTripleRight_parity D Sc i i j)) M w
  let E := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_jii β i j)
      (contentTripleLeft_parity D Sc i j i)) M w
  let F := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j)
      (content_triple_jii β i j) (contentTripleRight_parity D Sc j i i)) M w
  let G := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) rfl
      (contentTripleLeft_parity D Sc j i i)) M w
  A.comp ((-B).comp C) - E.comp ((-F).comp G)

/-- The residual twist acts on the entire kernel, not just its affine factor. -/
theorem contentMixedBraid_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl).obj v ⟶ w) (m : M.obj v) :
    contentMixedBraid D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor v h m) =
    sign k (D.parity i * D.parity j) •
      contentTensorEval D Sc cutoff N M w v (twist k (D.parity i) h) m
        (contentBraidCorrection D Sc i j) := by
  let p := D.parity i
  let q := D.parity j
  have hdeg : p*q + (p*p + q*p) = p := by
    rcases parity_eq_zero_or_one p with hp | hp <;>
      rcases parity_eq_zero_or_one q with hq | hq <;> simp [hp,hq]
  have hsign : (p*p)*(q*p) + (p*q)*(p*p + q*p) = p*q := by
    rcases parity_eq_zero_or_one p with hp | hp <;>
      rcases parity_eq_zero_or_one q with hq | hq <;> simp [hp,hq]
  unfold contentMixedBraid
  simp only [LinearMap.neg_comp, LinearMap.comp_neg, LinearMap.sub_apply, LinearMap.neg_apply]
  rw [contentTripleTransform_tensor, contentTripleTransform_tensor]
  simp only [mul_comm q p] at hdeg hsign
  simp only [show D.parity i = p from rfl, show D.parity j = q from rfl]
  simp only [mul_comm q p, hdeg, hsign]
  rw [sub_neg_eq_add, neg_add_eq_sub, ← smul_sub]
  congr 1
  change contentTensorEval D Sc cutoff N M w v (twist k p h) m _ -
    contentTensorEval D Sc cutoff N M w v (twist k p h) m _ = _
  rw [← map_sub, contentTriple_braid D Sc i j hij]
  all_goals first | exact contentTripleLeft_parity D Sc _ _ _ |
    exact contentTripleRight_parity D Sc _ _ _

theorem contentBraidCorrection_parity {i j : I} (hij : i ≠ j) :
    contentBraidCorrection D Sc i j ∈ parity (R := k) _ _ (D.parity i) := by
  rw [← contentTriple_braid D Sc i j hij]
  have hp : D.parity i * D.parity j +
      (D.parity i * D.parity i + D.parity j * D.parity i) = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with hp | hp <;>
      rcases parity_eq_zero_or_one (D.parity j) with hq | hq <;> simp [hp,hq]
  apply Submodule.sub_mem
  · have h1 := comp_mem (contentTripleLeft_parity D Sc i j i)
      (comp_mem (contentTripleRight_parity D Sc j i i) (contentTripleLeft_parity D Sc j i i))
    rw [hp] at h1
    exact h1
  · have h2 := comp_mem (contentTripleRight_parity D Sc i j i)
      (comp_mem (contentTripleLeft_parity D Sc i i j) (contentTripleRight_parity D Sc i i j))
    have hp' : D.parity j * D.parity i +
        (D.parity i * D.parity i + D.parity i * D.parity j) = D.parity i := by
      simpa only [mul_comm (D.parity j) (D.parity i)] using hp
    rw [hp'] at h2
    exact h2

/-- Mixed braid as linear maps, with the full source correction over the prescribed twist. -/
theorem contentMixedBraid_source_linear (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentMixedBraid D (parameterTwist D Sc) cutoff N β i j M w =
      sign k (D.parity i * D.parity j) •
        contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (contentBraidCorrection_parity D (parameterTwist D Sc) hij) M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentMixedBraid_tensor D _ cutoff N β hij, LinearMap.smul_apply,
    contentInductionEndLinear, BalancedInduction.transformLinear_tensor]
  rfl

end OddMath.QuiverHecke.ELVOld
