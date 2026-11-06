/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixIntegerOver
import OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficientsOver

/-! # Degrees of the chosen reservoir closures over a graded base ring

BE (1.13)–(1.14), closure dependency G8, over a commutative `K`-algebra `R` graded by `𝒜`.
The represented unit and cap closure coefficients of the weighted content kernels lie in degree
`2 dᵢ (r + s + 1)` of the truncated quotient over `K`
(`weightedContentUnitClosureCoefficient_degreeOver`,
`weightedContentCapClosureCoefficient_degreeOver`), and so do the reconstructed source
coefficients of the chosen positive and negative reservoir closures
(`ReservoirClosures.positiveCoefficient_mem_degreeOver`,
`ReservoirClosures.negativeCoefficient_mem_degreeOver`).

For `K = R` with the trivial grading these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentKernelClosureCoordinates` and
`OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureDegree`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section
set_option backward.dsimp.instances true

open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath.Diagrams

namespace OddMath.QuiverHecke.ELVOld

open BalancedInduction CyclotomicCrossingTensor

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- Identities have degree zero in the old quotient, over a graded base. -/
theorem oldId_mem_degreeOver (v : OldCategory D Sc cutoff) :
    𝟙 v ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v v 0 := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  exact id_mem_degree (R := K) v

/-- Truncation preserves degrees, over a graded base. -/
theorem truncateOld_mem_degreeOver {v w : OldCategory D Sc cutoff} {n : ℤ} {f : v ⟶ w}
    (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    (truncateOld D Sc cutoff N v.word w.word f :
        (oldTruncateFunctor D Sc cutoff N).obj v ⟶ (oldTruncateFunctor D Sc cutoff N).obj w) ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
        ((oldTruncateFunctor D Sc cutoff N).obj v) ((oldTruncateFunctor D Sc cutoff N).obj w)
        n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ha

/-- Parity projections preserve degrees of the truncated quotient, over a graded base. -/
theorem truncatedProj_mem_degreeOver {v w : TruncatedCategory D Sc cutoff N} {n : ℤ}
    (p : ZMod 2) {f : v ⟶ w} (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n) :
    proj R p f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := truncatedGradedSupercategoryOver D sy 𝒜 Sc hP cutoff N
  have hf' : f ∈ degree (R := K) v w n := hf
  rw [← Supercategory.proj_restrictScalars K R (TruncatedCategory D Sc cutoff N) p f]
  exact proj_mem_degree (R := K) p hf'

/-- Source degree follows from the total action on every represented identity, over a graded
base. -/
theorem ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation (β : Multiset I)
    (η : ModuleCentre.Centre D Sc cutoff N β) (d : ℤ)
    (h : ∀ w : ContentCategory D Sc cutoff N β,
      (η.total (contentRepresentable D Sc cutoff N β w)).total w (𝟙 w) ∈
        truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj d) :
    ModuleCentre.reconstruct D Sc cutoff N β η ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N β d := by
  intro p w
  rw [ModuleCentre.reconstruct_app_eq_proj_total, ModuleCentre.reconstruct_total_evaluate]
  exact truncatedProj_mem_degreeOver D sy 𝒜 Sc hP cutoff N p (h w)

variable (i : I)

/-- The represented unit closure coefficient has the positive source degree, over a graded
base. -/
theorem weightedContentUnitClosureCoefficient_degreeOver (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) :
    weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  rcases w with ⟨t, ht⟩
  cases ht
  have h := positiveKernelClosure_degreeOver D sy 𝒜 Sc hP cutoff i
    (⟨t.word⟩ : OldCategory D Sc cutoff) ⟨t.word⟩ hh r s
    (oldId_mem_degreeOver D sy 𝒜 Sc hP cutoff ⟨t.word⟩)
  rw [zero_add] at h
  exact truncateOld_mem_degreeOver D sy 𝒜 Sc hP cutoff N h

/-- The represented cap closure coefficient has the same source degree, over a graded base. -/
theorem weightedContentCapClosureCoefficient_degreeOver (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) :
    weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  rcases w with ⟨t, ht⟩
  cases ht
  have h := negativeKernelClosure_degreeOver D sy 𝒜 Sc hP cutoff i
    (⟨t.word⟩ : OldCategory D Sc cutoff) ⟨t.word⟩ hh r s
    (oldId_mem_degreeOver D sy 𝒜 Sc hP cutoff ⟨t.word⟩)
  rw [zero_add] at h
  exact truncateOld_mem_degreeOver D sy 𝒜 Sc hP cutoff N h

namespace ReservoirClosures

variable (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (γ : WeightBlocks D Λ x₁)

/-- The represented positive-weight value has the positive closure degree, over a graded
base. -/
theorem positiveRepresentedValue_degreeOver (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N γ.1) :
    positiveRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r s w ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  unfold positiveRepresentedValue
  exact weightedContentCapClosureCoefficient_degreeOver D sy 𝒜 Sc hP cutoff N i γ.1 _ w r s

/-- The represented negative-weight value has the same degree, over a graded base. -/
theorem negativeRepresentedValue_degreeOver (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N γ.1) :
    negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r s w ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  unfold negativeRepresentedValue
  exact weightedContentUnitClosureCoefficient_degreeOver D sy 𝒜 Sc hP cutoff N i γ.1 _ w r s

attribute [local irreducible] positive negative positiveContent negativeContent
  positiveRepresentedValue negativeRepresentedValue

/-- The reconstructed coefficient of the chosen positive closure has its strictly positive
source degree on every output block, over a graded base. -/
theorem positiveCoefficient_mem_degreeOver (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s) ∈ _
  apply ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation
  intro w
  by_cases hγ : ∃ β₁, blockSucc D Λ i h₁ β₁ = γ
  · rcases hγ with ⟨β₁, rfl⟩
    have he := positiveContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh r s
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
    change ((positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂
      (blockSucc D Λ i h₁ β₁) hh r s).total
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
    erw [he]
    change (𝟙 w ≫ positiveRepresentedValue D Sc cutoff N Λ hcutoff i
      (blockSucc D Λ i h₁ β₁) hh r s w) ∈ _
    rw [Category.id_comp]
    exact positiveRepresentedValue_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff
      (blockSucc D Λ i h₁ β₁) hh r s w
  · rw [positiveContent_total_absent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hγ hh r s,
      supernatural_zero_total, SVec.zero_apply]
    exact zero_mem _

/-- The reconstructed coefficient of the chosen negative closure has the same strictly positive
source degree, over a graded base. -/
theorem negativeCoefficient_mem_degreeOver (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s) ∈ _
  apply ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation
  intro w
  by_cases hγ : ∃ β₁, blockSucc D Λ i h₁ β₁ = γ
  · rcases hγ with ⟨β₁, rfl⟩
    have he := negativeContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh r s
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
    change ((negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂
      (blockSucc D Λ i h₁ β₁) hh r s).total
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
    erw [he]
    change (𝟙 w ≫ negativeRepresentedValue D Sc cutoff N Λ hcutoff i
      (blockSucc D Λ i h₁ β₁) hh r s w) ∈ _
    rw [Category.id_comp]
    exact negativeRepresentedValue_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff
      (blockSucc D Λ i h₁ β₁) hh r s w
  · rw [negativeContent_total_absent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hγ hh r s,
      supernatural_zero_total, SVec.zero_apply]
    exact zero_mem _

end ReservoirClosures

end OddMath.QuiverHecke.ELVOld
