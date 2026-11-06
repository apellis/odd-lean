/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncationOver
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport

/-!
# Degree support of the truncated vacuum over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜` in degrees `0, …, b`, the Hom modules out of
the empty word in the coefficient-truncated quotient lie in degrees `0, …, b + M N`, where `M`
bounds coefficient degree against coefficient weight
(`ELVOld.truncatedVacuum_support_of_boundOver`). The vacuum is spanned over `R` by the
coefficient basis vectors, and homogeneous scalars of `R` shift degrees by at most `b`
(`BasisGrading.mem_iSup_of_mem_span`).

For `K = R` with the trivial grading (`b = 0`) this is `ELVOld.truncatedVacuum_support_of_bound`.
-/

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory

namespace OddMath.QuiverHecke.ELVOld

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- A vacuum coefficient basis class lies in its coefficient degree, over a graded base. -/
theorem vacuumClass_basis_degreeOver (a : SKM.SYM.CoefficientIndex D) :
    (vacuumClassLinear D Sc cutoff N (SKM.SYM.coefficientBasis D R a) :
        (⟨[]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨[]⟩) ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨[]⟩ ⟨[]⟩ (SKM.SYM.coefficientDegree D sy a) :=
  mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
    (coefficientIdentity_basis_degreeOver D sy 𝒜 Sc hP cutoff [] a)

/-- **Vacuum support over a graded base.** If `𝒜` lives in degrees `0, …, b`, the truncated
Homs out of the empty word lie in degrees `0, …, b + M N`. -/
theorem truncatedVacuum_support_of_boundOver (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (w : List I) (z : (⟨[]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩) :
    letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    z ∈ ⨆ n ∈ Set.Icc (0 : ℤ) (b + M * N),
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨[]⟩ ⟨w⟩ n := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  by_cases hw : w = []
  · subst w
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N [] []).mkQ_surjective z
    let S : Set ((⟨[]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨[]⟩) :=
      Set.range fun a => vacuumClassLinear D Sc cutoff N (SKM.SYM.coefficientBasis D R a)
    have hspan : (truncatedIdeal D Sc cutoff N [] []).mkQ f ∈ Submodule.span R S := by
      have hf := vacuum_hom_span D Sc cutoff f
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨a, rfl⟩ := hf
        change vacuumClassLinear D Sc cutoff N a ∈ _
        have ha : a ∈ Submodule.span R (Set.range (SKM.SYM.coefficientBasis D R)) := by
          rw [Module.Basis.span_eq]; trivial
        induction ha using Submodule.span_induction with
        | mem a ha =>
          obtain ⟨c, rfl⟩ := ha
          exact Submodule.subset_span ⟨c, rfl⟩
        | zero => simpa only [map_zero] using Submodule.zero_mem _
        | add a a' _ _ ha ha' => simpa only [map_add] using Submodule.add_mem _ ha ha'
        | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
      | zero => simpa only [map_zero] using Submodule.zero_mem _
      | add a a' _ _ ha ha' => simpa only [map_add] using Submodule.add_mem _ ha ha'
      | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
    refine BasisGrading.mem_iSup_of_mem_span 𝒜
      (truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨[]⟩ ⟨[]⟩)
      (fun hr hy => smul_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N hr hy)
      (T := Set.Icc (0 : ℤ) (M * N)) h𝒜 ?_ ?_ hspan
    · rintro e ⟨he₀, he₁⟩ t ⟨ht₀, ht₁⟩
      exact ⟨by omega, by omega⟩
    · rintro g ⟨c, rfl⟩
      by_cases hc : N ≤ SKM.SYM.coefficientWeight D c
      · rw [vacuumClass_basis_zero D Sc cutoff N c hc]
        exact Submodule.zero_mem _
      · have hcw : (SKM.SYM.coefficientWeight D c : ℤ) ≤ N := by
          exact_mod_cast (by omega : SKM.SYM.coefficientWeight D c ≤ N)
        have hn : SKM.SYM.coefficientDegree D sy c ∈ Set.Icc (0 : ℤ) (M * N) :=
          ⟨SKM.SYM.coefficientDegree_nonneg D sy c,
            (hbound c).trans (mul_le_mul_of_nonneg_left hcw hM)⟩
        exact Submodule.mem_iSup_of_mem (SKM.SYM.coefficientDegree D sy c)
          (Submodule.mem_iSup_of_mem hn (vacuumClass_basis_degreeOver D sy 𝒜 Sc hP cutoff N c))
  · rw [truncatedVacuum_eq_zero D Sc cutoff N hw z]
    exact Submodule.zero_mem _

end OddMath.QuiverHecke.ELVOld
