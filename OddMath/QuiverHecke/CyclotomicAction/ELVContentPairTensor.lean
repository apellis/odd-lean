import OddMath.QuiverHecke.CyclotomicAction.ELVContentTensorCoherence
/-! # Tensor formula for the raising-pair comparison

This retains the content cast needed in DeformedActionAssembly.md §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentPair_sum (β : Multiset I) (i j : I) :
    β + ([i,j] : Multiset I) = (β + ([i] : Multiset I)) + ([j] : Multiset I) := by
  rw [add_assoc]
  rfl

section Pair
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))
local notation "J" => contentAppend D Sc cutoff N β [i]
local notation "K" => contentAppendTo D Sc cutoff N δ₁ [j] δ₂ rfl
local notation "A" => contentAppendTo D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j)
local notation "e" => contentAppend_comp_eq D Sc cutoff N β [i] [j] δ₂ rfl (contentPair_sum β i j)

end Pair
end OddMath.QuiverHecke.ELVOld
