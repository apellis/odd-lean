/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentColour
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules

/-! # The absent-predecessor boundary for the weight matrices

Brundan–Ellis (1.13)–(1.14): at an output missing i, the lower E/F
coordinate vanishes, whereas the following F/E coordinate is retained.
The standing cutoff/highest-weight match puts this boundary at
nonpositive categorical height. Strictly positive height always has
a predecessor, so its row matrix has the supported content coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- Induction after append restriction has no vector at a word lacking the appended colour. -/
theorem truncatedIndRes_subsingleton_of_not_mem (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff bound) (SVec k))
    (w : TruncatedCategory D Sc cutoff bound) (hi : i ∉ (w.word : Multiset I)) :
    Subsingleton ((induced (truncatedAppend D Sc cutoff bound [i])
      ((restriction (truncatedAppend D Sc cutoff bound [i])).obj M)).obj w) := by
  have hz : ∀ z : Obj (truncatedAppend D Sc cutoff bound [i])
      ((restriction (truncatedAppend D Sc cutoff bound [i])).obj M).toFunctor w, z = 0 := by
    apply obj_eq_zero_of_coeff_eq_zero
    intro s g
    apply truncatedCategory_hom_eq_zero_of_content_ne D Sc cutoff bound (f := g)
    intro he
    apply hi
    rw [← he]
    change i ∈ ((s.word ++ [i] : List I) : Multiset I)
    simp only [Multiset.mem_coe, List.mem_append, List.mem_singleton, or_true]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The entire restricted E/F module is zero on a content block missing i. -/
theorem truncatedIndRes_restriction_isZero (i : I) (γ : Multiset I) (hi : i ∉ γ)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff bound) (SVec k)) :
    Limits.IsZero ((restriction (contentInclusion D Sc cutoff bound γ)).obj
      (induced (truncatedAppend D Sc cutoff bound [i])
        ((restriction (truncatedAppend D Sc cutoff bound [i])).obj M))) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext
  intro p w
  apply SVec.hom_ext
  intro x
  have hs := truncatedIndRes_subsingleton_of_not_mem D Sc cutoff bound i M w.obj
    (by simpa only [w.content] using hi)
  exact hs.elim _ _

/-- An absent predecessor puts the categorical weight at nonpositive height. -/
theorem elvWeightHeight_nonpos_of_absent (i : I) (Λ : X) {x₀ x : X}
    (h : x₀ + D.α i = x) (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (δ : WeightBlocks D Λ x) (hδ : ¬ ∃ β, blockSucc D Λ i h β = δ) :
    D.h i x ≤ 0 := by
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h δ).mpr hm)
  have hc := contentCrossingHeight_nonneg_of_not_mem D cutoff δ.1.toList i
    (by simpa only [Multiset.mem_toList] using hi)
  rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D cutoff i Λ x hcutoff δ] at hc
  exact neg_nonneg.mp hc

/-- Strictly positive categorical height excludes every absent predecessor sector. -/
theorem elvWeightPredecessor_of_positive_height (i : I) (Λ : X) {x₀ x : X}
    (h : x₀ + D.α i = x) (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (hpos : 0 < D.h i x) (δ : WeightBlocks D Λ x) :
    ∃ β, blockSucc D Λ i h β = δ := by
  by_contra hδ
  exact (not_lt_of_ge (elvWeightHeight_nonpos_of_absent D cutoff i Λ h hcutoff δ hδ)) hpos

end OddMath.QuiverHecke.ELVOld
