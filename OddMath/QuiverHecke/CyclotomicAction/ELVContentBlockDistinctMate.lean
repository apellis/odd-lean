/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppendTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockRestrictionTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateLinear
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionIsoComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareSource

/-! # The prescribed distinct mate at canonical truncated content

Brundan–Ellis (1.12): compare the positive rectangular cup-crossing-cap
on canonical multiset-content modules with the proved global truncated
mate through the selected full-inclusion charts. Neither coefficient
parity nor the ordinary right action is discarded.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i j : I)

/-- The named canonical target proof is shared by the chosen append charts. -/
theorem contentBlockCanonicalSum (δ : Multiset I) (σ : List I) :
    δ + (σ : Multiset I) = δ + (σ : Multiset I) := rfl

/-- The common upper content keeps the prescribed j,i order as its index. -/
abbrev contentBlockDistinctUpper : Multiset I := (β + ([j] : Multiset I)) + ([i] : Multiset I)

theorem contentBlockDistinctUpper_eq :
    (β + ([i] : Multiset I)) + ([j] : Multiset I) = contentBlockDistinctUpper β i j := by
  unfold contentBlockDistinctUpper
  ac_rfl

local notation "γ" => contentBlockDistinctUpper β i j
local notation "hM" => contentBlockDistinctUpper_eq β i j
local notation "J" => contentAppendTo D Sc cutoff N β [j] (β + ([j] : Multiset I)) (contentBlockCanonicalSum β [j])
local notation "K" => contentAppendTo D Sc cutoff N β [i] (β + ([i] : Multiset I)) (contentBlockCanonicalSum β [i])
local notation "L" => contentAppendTo D Sc cutoff N (β + ([j] : Multiset I)) [i] γ (contentBlockCanonicalSum (β + ([j] : Multiset I)) [i])
local notation "U" => contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ hM
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Qi" => contentInclusion D Sc cutoff N (β + ([i] : Multiset I))
local notation "Qj" => contentInclusion D Sc cutoff N (β + ([j] : Multiset I))
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]

/-- The independently prescribed positive distinct crossing in the common upper block. -/
def contentBlockDistinctCross (s : ContentCategory D Sc cutoff N β) :
    (J ⋙ L).obj s ⟶ (K ⋙ U).obj s :=
  truncatedDistinctCrossComponent D Sc cutoff N i j s.obj

theorem contentBlockDistinctCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j) (contentBlockDistinctCross D Sc cutoff N β i j) where
  mem s := (truncatedDistinctCross_supernatural D Sc cutoff N i j).mem s.obj
  naturality := by
    intro s t p f hf
    exact (truncatedDistinctCross_supernatural D Sc cutoff N i j).naturality hf

theorem contentBlockRestrictionExtension_even
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ (contentBlockCanonicalSum β [j]) M).hom ∈
      parity (R := k) _ _ 0 := by
  rw [contentAppendToRestrictionExtensionIso_hom]
  have h := comp_mem
    (map_mem (BalancedInduction.induction Q₀)
      (map_mem (BalancedInduction.restriction J) (BalancedInduction.adjunctionUnit_mem Qj M)))
    (BalancedInduction.adjunctionCounit_mem Q₀
      ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj M)))
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.induction, contentAppend, BalancedInduction.adjunction] at h ⊢
  simpa only [zero_add] using h

end OddMath.QuiverHecke.ELVOld
