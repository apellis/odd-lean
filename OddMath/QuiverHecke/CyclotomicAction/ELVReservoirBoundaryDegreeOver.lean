/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureDegreeOver

/-! # Degrees of the chosen reservoir boundary contractions over a graded base ring

SwappedHomInversion §4 (7), over a commutative `K`-algebra `R` graded by `𝒜`. The window
contractions of the finite kernel inverses have the difference degrees `2 dᵢ (n - m)` and
`2 dᵢ (m - n)` (`positiveKernelBoundary_degreeOver`, `negativeKernelBoundary_degreeOver`), and
so do their represented content coefficients and the reconstructed source coefficients of the
chosen reservoir boundaries (`ReservoirBoundaries.positiveCoefficient_mem_degreeOver`,
`ReservoirBoundaries.negativeCoefficient_mem_degreeOver`).

For `K = R` with the trivial grading these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.ELVKernelBoundaryDegrees`,
`OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentKernelBoundaryCoordinates` and
`OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryDegree`.
-/

noncomputable section
set_option backward.dsimp.instances true

open CategoryTheory Opposite StringDiagrams Supercategory GradedSupercategory OddMath.Diagrams
open OddMath.IntegerMatrix

namespace OddMath.QuiverHecke.ELVOld

open BalancedInduction CyclotomicCrossingTensor

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

namespace CyclotomicCrossingTensor

/-- The positive inverse window row has degree `-2 dᵢ m`, over a graded base. -/
theorem positiveKernelWindowInverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) q) :
    positiveKernelWindowInverse D Sc cutoff i v t hh m y ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (q - 2 * sy.d i * m.val) := by
  exact (Coordinates.mem_shiftedDegree _ _ _ _).1
    (positiveKernelEquiv_inverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh hy) (some m)

/-- Inserting window column `m` gives inverse degree `-2 dᵢ m`, over a graded base. -/
theorem negativeKernelWindowInverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : Fin (contentCapCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t q) :
    negativeKernelWindowInverse D Sc cutoff i v t hh m y ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (q - 2 * sy.d i * m.val) := by
  classical
  change (negativeKernelEquiv D Sc cutoff i v t hh).symm
    (Pi.single (some m) y) ∈ _
  apply negativeKernelEquiv_inverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh
  apply (Coordinates.mem_shiftedDegree _ _ _ _).2
  intro a
  by_cases ha : a = some m
  · subst a
    simp only [Pi.single_eq_same]
    change y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t
      (q - 2 * sy.d i * m.val + 2 * sy.d i * m.val)
    simpa only [sub_add_cancel] using hy
  · rw [Pi.single_eq_of_ne ha]
    exact Submodule.zero_mem _

/-- All positive contractions have the difference degree, over a graded base. -/
theorem positiveKernelBoundary_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (n : ℕ) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t q) :
    positiveKernelBoundary D Sc cutoff i v t hh m n y ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (q + 2 * sy.d i * ((n : ℤ) - m.val)) := by
  have h := positiveKernelWindowInverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh m
    (unitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t n hy)
  have he : q + 2 * sy.d i * n - 2 * sy.d i * m.val =
      q + 2 * sy.d i * ((n : ℤ) - m.val) := by ring
  simpa only [positiveKernelBoundary, LinearMap.comp_apply, he] using h

/-- All negative contractions have the difference degree, over a graded base. -/
theorem negativeKernelBoundary_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (n : Fin (contentCapCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t q) :
    negativeKernelBoundary D Sc cutoff i v t hh m n y ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (q + 2 * sy.d i * ((m : ℤ) - n.val)) := by
  have h := capKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t m
    (negativeKernelWindowInverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh n hy)
  have he : q - 2 * sy.d i * n.val + 2 * sy.d i * m =
      q + 2 * sy.d i * ((m : ℤ) - n.val) := by ring
  simpa only [negativeKernelBoundary, LinearMap.comp_apply, he] using h

end CyclotomicCrossingTensor

variable (i : I)

/-- The represented unit boundary coefficient has the difference degree, over a graded base. -/
theorem weightedContentUnitBoundaryCoefficient_degreeOver (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ) :
    weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * ((s : ℤ) - r.val)) := by
  rcases w with ⟨t, ht⟩
  cases ht
  have h := positiveKernelBoundary_degreeOver D sy 𝒜 Sc hP cutoff i
    (⟨t.word⟩ : OldCategory D Sc cutoff) ⟨t.word⟩ hh r s
    (oldId_mem_degreeOver D sy 𝒜 Sc hP cutoff ⟨t.word⟩)
  rw [zero_add] at h
  exact truncateOld_mem_degreeOver D sy 𝒜 Sc hP cutoff N h

/-- The represented cap boundary coefficient has the difference degree, over a graded base. -/
theorem weightedContentCapBoundaryCoefficient_degreeOver (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r : ℕ) (s : Fin (contentCapCount D cutoff i β)) :
    weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * ((r : ℤ) - s.val)) := by
  rcases w with ⟨t, ht⟩
  cases ht
  have h := negativeKernelBoundary_degreeOver D sy 𝒜 Sc hP cutoff i
    (⟨t.word⟩ : OldCategory D Sc cutoff) ⟨t.word⟩ hh r s
    (oldId_mem_degreeOver D sy 𝒜 Sc hP cutoff ⟨t.word⟩)
  rw [zero_add] at h
  exact truncateOld_mem_degreeOver D sy 𝒜 Sc hP cutoff N h

namespace ReservoirBoundaries

variable (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (γ : WeightBlocks D Λ x₁)

/-- The represented positive boundary has the difference degree, over a graded base. -/
theorem positiveRepresentedValue_degreeOver (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat) (w : ContentCategory D Sc cutoff N γ.1) :
    positiveRepresentedValue D Sc cutoff N Λ hcutoff i γ hh j r hj w ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * ((r : ℤ) - j)) := by
  unfold positiveRepresentedValue
  exact weightedContentCapBoundaryCoefficient_degreeOver D sy 𝒜 Sc hP cutoff N i γ.1 _ w r _

/-- The represented negative boundary has the same difference degree, over a graded base. -/
theorem negativeRepresentedValue_degreeOver (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) (w : ContentCategory D Sc cutoff N γ.1) :
    negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N w.obj w.obj
        (2 * sy.d i * ((r : ℤ) - j)) := by
  unfold negativeRepresentedValue
  exact weightedContentUnitBoundaryCoefficient_degreeOver D sy 𝒜 Sc hP cutoff N i γ.1 _ w _ r

attribute [local irreducible] positive negative positiveContent negativeContent
  positiveRepresentedValue negativeRepresentedValue

/-- The reconstructed source coefficient of the chosen positive boundary has the difference
degree, over a graded base. -/
theorem positiveCoefficient_mem_degreeOver (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat) :
    positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh j r ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1 (2 * sy.d i * ((r : ℤ) - j)) := by
  have hpos : 0 < D.h i x₁ := by omega
  obtain ⟨β₁, rfl⟩ := elvWeightPredecessor_of_positive_height D cutoff i Λ h₁ (hcutoff i) hpos γ
  change ModuleCentre.reconstruct D Sc cutoff N (blockSucc D Λ i h₁ β₁).1
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ (blockSucc D Λ i h₁ β₁) hh j r) ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N (blockSucc D Λ i h₁ β₁).1
        (2 * sy.d i * ((r : ℤ) - j))
  apply ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation
  intro w
  have he := positiveContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh j r hj
    (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
  change ((positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂
    (blockSucc D Λ i h₁ β₁) hh j r).total
    (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
  erw [he]
  change (𝟙 w ≫ positiveRepresentedValue D Sc cutoff N Λ hcutoff i
    (blockSucc D Λ i h₁ β₁) hh j r hj w) ∈ _
  rw [Category.id_comp]
  exact positiveRepresentedValue_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff
    (blockSucc D Λ i h₁ β₁) hh j r hj w

/-- The reconstructed source coefficient of the chosen negative boundary has the difference
degree, including blocks without a predecessor, over a graded base. -/
theorem negativeCoefficient_mem_degreeOver (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1 (2 * sy.d i * ((r : ℤ) - j)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j) ∈
      contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N γ.1 (2 * sy.d i * ((r : ℤ) - j))
  apply ModuleCentre.reconstruct_mem_degreeOver_of_total_evaluation
  intro w
  have he := negativeContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j hj
    (contentRepresentable D Sc cutoff N γ.1 w) w (𝟙 w)
  change ((negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j).total
    (contentRepresentable D Sc cutoff N γ.1 w)).total w (𝟙 w) = _ at he
  erw [he]
  change (𝟙 w ≫ negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w) ∈ _
  rw [Category.id_comp]
  exact negativeRepresentedValue_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff γ hh r j hj w

end ReservoirBoundaries

end OddMath.QuiverHecke.ELVOld
