/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot

/-! # Module-uniform bounds at each actual weight-content block

The exponent varies with the target content block, while one exponent at a
fixed block works for every input module. This is the form needed before
transposing the actual dot through the actual induction/restriction adjunction.
No exponent over an entire original-weight fibre is asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- A fixed source-content bound is uniform in the arbitrary input module. -/
theorem elvContentDotTo_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (β γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ContentModules D Sc cutoff bound β,
      (show End ((contentInductionTo D Sc cutoff bound β [i] γ hγ).obj M) from
        (elvContentDotTo D Sc cutoff bound i β γ hγ).app (D.parity i) M) ^ e = 0 := by
  classical
  subst γ
  have hp := contentInductionDot_module_pow_zero D Sc cutoff bound hdot β.toList i
  rw [Multiset.coe_toList] at hp
  exact hp

theorem elvBlockDot_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (β : WeightBlocks D Λ x) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ContentModules D Sc cutoff bound β.1,
      (show End ((elvBlockInd D Sc cutoff bound i Λ h β).obj M) from
        (elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) M) ^ e = 0 :=
  elvContentDotTo_pow_zero D Sc cutoff bound i hdot β.1
    (blockSucc D Λ i h β).1 (by rw [blockSucc_val, add_comm]; rfl)

private theorem end_eqToHom_conj_pow
    {C : Type*} [Category C] [Preadditive C]
    {M N : C} (e : M = N) (d : End N) (n : ℕ) :
    (show End M from eqToHom e ≫ d ≫ eqToHom e.symm) ^ n =
      eqToHom e ≫ (d ^ n) ≫ eqToHom e.symm := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Each actual target-weight block has one exponent for every input module.
The exponent may depend on the target block. -/
theorem elvWeightDotComponent_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (δ : WeightBlocks D Λ y) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ELVWeightProduct D Sc cutoff bound Λ x,
      (show End ((elvInductionComponent D Sc cutoff bound i Λ h δ).obj M) from
        elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) ^ e = 0 := by
  classical
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    obtain ⟨e, he, hp⟩ := elvBlockDot_pow_zero D Sc cutoff bound i Λ h hdot β
    refine ⟨e, he, fun M => ?_⟩
    rw [elvWeightDotComponent_blockSucc, end_eqToHom_conj_pow, hp (M β)]
    simp
  · refine ⟨1, by decide, fun M => ?_⟩
    simpa only [pow_one] using
      (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ M).eq_of_src
        (elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) 0

end OddMath.QuiverHecke.ELVOld
