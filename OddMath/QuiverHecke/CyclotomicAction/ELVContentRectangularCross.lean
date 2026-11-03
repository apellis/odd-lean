/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctTargets
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleRelations

/-! # Positive distinct crossings in rectangular content coordinates

The crossing in the Brundan–Ellis (1.12) rectangular mate agrees with
the selected affine word crossing through the chosen induction
composition comparisons, including prescribed successor contents.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (β : Multiset I) (i j : I) (δj δi γ : Multiset I)
  (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
  (hL : δj + ([i] : Multiset I) = γ) (hU : δi + ([j] : Multiset I) = γ)
  (hji : β + ([j,i] : Multiset I) = γ) (hij : β + ([i,j] : Multiset I) = γ)
private theorem contentCompTo_eq_compOfEq
    (η : Multiset I) (σ : List I) (δ : Multiset I) (hδ : η + (σ : Multiset I) = δ)
    (τ : List I) (ζ : Multiset I) (hζ : δ + (τ : Multiset I) = ζ)
    (h : η + ((σ ++ τ : List I) : Multiset I) = ζ) :
    contentInductionCompTo D Sc cutoff bound η σ δ hδ τ ζ hζ h =
      inductionCompOfEq (contentAppendTo D Sc cutoff bound η σ δ hδ)
        (contentAppendTo D Sc cutoff bound δ τ ζ hζ)
        (contentAppendTo D Sc cutoff bound η (σ ++ τ) ζ h)
        (contentAppend_compTo_eq D Sc cutoff bound η σ δ hδ τ ζ hζ h) := by
  subst δ
  rfl

/-- Reversed induction labels retain the physical crossing degree. -/
theorem contentCrossAffine_reverse_mem : contentCrossAffine D Sc j i ∈
    parity (R := k) _ _ (D.parity i * D.parity j) := by
  simpa only [mul_comm] using contentCrossAffine_mem D Sc j i

local notation "J" => contentAppendTo D Sc cutoff bound β [j] δj hj
local notation "K" => contentAppendTo D Sc cutoff bound β [i] δi hi
local notation "L" => contentAppendTo D Sc cutoff bound δj [i] γ hL
local notation "U" => contentAppendTo D Sc cutoff bound δi [j] γ hU
local notation "F" => contentAppendTo D Sc cutoff bound β ([j] ++ [i]) γ hji
local notation "G" => contentAppendTo D Sc cutoff bound β ([i] ++ [j]) γ hij
local notation "eF" => contentAppend_compTo_eq D Sc cutoff bound β [j] δj hj [i] γ hL hji
local notation "eG" => contentAppend_compTo_eq D Sc cutoff bound β [i] δi hi [j] γ hU hij

/-- The positive crossing is the affine crossing with its two word endpoints transported. -/
theorem contentDistinctTargetsCross_coefficient (hne : i ≠ j)
    (s : ContentCategory D Sc cutoff bound β) :
    contentDistinctTargetsCross D Sc cutoff bound β i j δj δi γ hj hi hL hU s =
      eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eF) ≫
        contentAppendToComponent D Sc cutoff bound (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij (contentCrossAffine D Sc j i) s ≫
          eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eG).symm := by
  apply (conj_eqToHom_iff_heq
    (contentDistinctTargetsCross D Sc cutoff bound β i j δj δi γ hj hi hL hU s)
    (contentAppendToComponent D Sc cutoff bound (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij (contentCrossAffine D Sc j i) s)
    (congrArg (fun H => CategoryTheory.Functor.obj H s) eF)
    (congrArg (fun H => CategoryTheory.Functor.obj H s) eG)).mpr
  rw [contentCrossAffine_distinct D Sc j i hne.symm]
  exact truncatedDistinctCrossComponent_heq D Sc cutoff bound i j s.obj

/-- The word-induction crossing equals the rectangular crossing used by the content mate. -/
theorem contentDistinctTargetsCross_comparison (hne : i ≠ j)
    (P : ContentModules D Sc cutoff bound β) :
    ((contentInductionCompTo D Sc cutoff bound β [i] δi hi [j] γ hU hij).hom.app P ≫
      (contentInductionTransform D Sc cutoff bound (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
        (contentCrossAffine_reverse_mem D Sc i j)).app (D.parity i * D.parity j) P) ≫
      (contentInductionCompTo D Sc cutoff bound β [j] δj hj [i] γ hL hji).inv.app P =
        BalancedInduction.rectangularCrossComponent J K L U
          (contentDistinctTargetsCross_supernatural D Sc cutoff bound β i j δj δi γ hj hi hL hU) P := by
  have h := inductionCompOfEq_cross J K L U F G eF eG
    (contentDistinctTargetsCross_supernatural D Sc cutoff bound β i j δj δi γ hj hi hL hU)
    (contentAppendTo_supernatural D Sc cutoff bound (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij (contentCrossAffine_reverse_mem D Sc i j))
    (contentDistinctTargetsCross_coefficient D Sc cutoff bound β i j δj δi γ hj hi hL hU hji hij hne) P
  dsimp only [contentInductionTo] at h ⊢
  simpa only [contentCompTo_eq_compOfEq, contentInductionTransform, inductionTransform_app_self] using h

end OddMath.QuiverHecke.ELVOld
