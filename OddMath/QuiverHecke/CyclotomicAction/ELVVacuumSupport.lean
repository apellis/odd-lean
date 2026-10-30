/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncation

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem vacuum_index_target {w : List I} (j : NFIdx [] w) : w = [] := by
  apply List.eq_nil_of_length_eq_zero
  have h := congrArg List.length j.tgt_cw
  simpa only [length_tgt, List.length_nil] using h.symm

theorem vacuum_nf (j : NFIdx ([] : List I) []) :
    j.nf (D := D) (Sc := Sc) = 𝟙 _ := by
  have hd : j.val.1 = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have := j.property.2.1 x hx
    simp at this
  have hp : j.val.2 = 1 := by
    ext x
    exact Fin.elim0 x
  have hc : Categorification.TypeA.canWord 0 j.val.2 = [] := by
    rw [hp]
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  simp only [NFIdx.nf, hd, List.map_nil, List.nil_append, List.length_nil, hc, cw]
  exact cl_nil D Sc [] _

theorem vacuum_hom_span (f : hom D Sc cutoff [] []) :
    f ∈ Submodule.span k (Set.range (coefficientIdentity D Sc cutoff [])) := by
  change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D [])) at f
  change f ∈ Submodule.span k (Set.range fun a : SKM.SYM D k =>
    SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k] (𝟙 ((pres D Sc).obj (ob D []))))
  induction f using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a f =>
    obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
      (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon a
    have hf : f ∈ Submodule.span k (Set.range (fun j : NFIdx [] [] => j.nf (D := D) (Sc := Sc))) := by
      rw [span_nf]; trivial
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨j, rfl⟩ := hf
      simp only [vacuum_nf D Sc]
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero => simp only [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa only [TensorProduct.tmul_add] using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa only [TensorProduct.tmul_smul] using Submodule.smul_mem _ c hx

theorem vacuum_hom_eq_zero {w : List I} (hw : w ≠ []) (f : hom D Sc cutoff [] w) : f = 0 := by
  change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D w)) at f
  change f = (0 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D w)))
  induction f using TensorProduct.inductionOn with
  | add x y hx hy => rw [hx, hy, add_zero]
  | tmul a f =>
    have hf : f ∈ Submodule.span k (Set.range (fun j : NFIdx [] w => j.nf (D := D) (Sc := Sc))) := by
      rw [span_nf]; trivial
    have hf0 : f = 0 := by
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨j, rfl⟩ := hf
        exact (hw (vacuum_index_target j)).elim
      | zero => rfl
      | add x y _ _ hx hy => rw [hx, hy, add_zero]
      | smul c x _ hx => rw [hx, smul_zero]
    rw [hf0, TensorProduct.tmul_zero]

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

def vacuumClassLinear : SKM.SYM D k →ₗ[k] TruncatedOld D Sc cutoff N [] [] :=
  (truncatedIdeal D Sc cutoff N [] []).mkQ.comp
    (((TensorProduct.mk k _ _).flip (𝟙 ((pres D Sc).obj (ob D [])))).comp
      (SKM.SYM.elvCoefficientQuotient D cutoff).toLinearMap)

theorem vacuumClass_basis_zero (a : SKM.SYM.CoefficientIndex D)
    (ha : N ≤ SKM.SYM.coefficientWeight D a) :
    vacuumClassLinear D Sc cutoff N (SKM.SYM.coefficientBasis D k a) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.mem_sup_right
  apply Submodule.subset_span
  exact ⟨[], a, ha, 𝟙 _, 𝟙 _, by simp only [Category.id_comp, Category.comp_id]; rfl⟩

theorem vacuumClass_basis_degree (a : SKM.SYM.CoefficientIndex D) :
    vacuumClassLinear D Sc cutoff N (SKM.SYM.coefficientBasis D k a) ∈
      truncatedDegree D Sc cutoff sy hc N [] [] (SKM.SYM.coefficientDegree D sy a) := by
  apply mkQ_mem_truncatedDegree
  have ha : SKM.SYM.coefficientBasis D k a ∈
      SKM.SYM.coefficientDegreePart D k sy (SKM.SYM.coefficientDegree D sy a) :=
    Submodule.subset_span ⟨a, rfl, rfl⟩
  have hf : (𝟙 ((pres D Sc).obj (ob D []))) ∈ homDegree D sy Sc [] [] 0 :=
    (pres D Sc).id_mem_homDeg (gdeg D sy) _
  have h := elvQuotientMap_source_mem_degree D sy Sc hc cutoff ha hf
  rw [elvQuotientMap_source, add_zero] at h
  exact h
theorem truncatedVacuum_eq_zero {w : List I} (hw : w ≠ [])
    (z : TruncatedOld D Sc cutoff N [] w) : z = 0 := by
  obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N [] w).mkQ_surjective z
  rw [vacuum_hom_eq_zero D Sc cutoff hw f, map_zero]

/-- Actual vacuum support from a bound on coefficient degree versus total weight. -/
theorem truncatedVacuum_support_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (w : List I) :
    (⊤ : Submodule k (TruncatedOld D Sc cutoff N [] w)) =
      ⨆ n ∈ Set.Icc (0 : ℤ) (M * N), truncatedDegree D Sc cutoff sy hc N [] w n := by
  apply le_antisymm _ le_top
  intro z hz
  clear hz
  obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N [] w).mkQ_surjective z
  by_cases hw : w = []
  · subst w
    have hf := vacuum_hom_span D Sc cutoff f
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      change vacuumClassLinear D Sc cutoff N a ∈ _
      have ha : a ∈ Submodule.span k (Set.range (SKM.SYM.coefficientBasis D k)) := by
        rw [Module.Basis.span_eq]; trivial
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨b, rfl⟩ := ha
        by_cases hb : N ≤ SKM.SYM.coefficientWeight D b
        · rw [vacuumClass_basis_zero D Sc cutoff N b hb]
          exact Submodule.zero_mem _
        · have hw : (SKM.SYM.coefficientWeight D b : ℤ) ≤ N := by
            exact_mod_cast (by omega : SKM.SYM.coefficientWeight D b ≤ N)
          have hn : SKM.SYM.coefficientDegree D sy b ∈ Set.Icc (0 : ℤ) (M * N) :=
            ⟨SKM.SYM.coefficientDegree_nonneg D sy b,
              (hbound b).trans (mul_le_mul_of_nonneg_left hw hM)⟩
          exact Submodule.mem_iSup_of_mem (SKM.SYM.coefficientDegree D sy b)
            (Submodule.mem_iSup_of_mem hn (vacuumClass_basis_degree D Sc cutoff sy hc N b))
      | zero => simpa only [map_zero] using Submodule.zero_mem (⨆ n ∈ Set.Icc (0 : ℤ) (M * N),
          truncatedDegree D Sc cutoff sy hc N [] [] n)
      | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
      | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
    | zero => simpa only [map_zero] using Submodule.zero_mem (⨆ n ∈ Set.Icc (0 : ℤ) (M * N),
        truncatedDegree D Sc cutoff sy hc N [] [] n)
    | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
  · rw [vacuum_hom_eq_zero D Sc cutoff hw f, map_zero]
    exact Submodule.zero_mem _

/-- Finite colours supply the bound; no support premise is assumed. -/
theorem truncatedVacuum_finite_support [Finite I] (w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N [] w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N [] w n := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact ⟨Set.Icc 0 (M * N), Set.finite_Icc _ _,
    truncatedVacuum_support_of_bound D Sc cutoff sy hc N M hM hb w⟩

end OddMath.QuiverHecke.ELVOld
