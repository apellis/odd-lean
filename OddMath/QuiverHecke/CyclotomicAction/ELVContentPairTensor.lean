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

theorem contentEPairComparison_eq :
    contentEPairComparison D Sc cutoff N β i j =
      inductionCompOfEq J K A e := by
  rfl

theorem contentEPairComparison_hom_total_tensor
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ₁) (z : ContentCategory D Sc cutoff N δ₂)
    (b : (K).obj w ⟶ z) (a : (J).obj v ⟶ w) (m : M.obj v) :
    ((contentEPairComparison D Sc cutoff N β i j).hom.app M).total z
      (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b
        (BalancedInduction.tensor J M.toFunctor v a m)) =
    BalancedInduction.tensor A M.toFunctor v
      (eqToHom (congrArg (fun F => F.obj v) e).symm ≫ (K).map a ≫ b) m := by
  rw [contentEPairComparison_eq]
  apply inductionCompOfEq_hom_total_tensor
end Pair
end OddMath.QuiverHecke.ELVOld
