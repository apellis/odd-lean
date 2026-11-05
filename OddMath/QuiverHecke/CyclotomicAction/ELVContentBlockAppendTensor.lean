/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquare

/-! # The selected append chart on truncated content tensors

For Brundan–Ellis (1.12), specialize the abstract commuting induction
square to the literal truncated content inclusion. Its chosen forward
map retains every entire quotient coefficient and inserts the selected
input inclusion unit, with no homogeneity assumption.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (σ : List I) (γ : Multiset I) (hσ : β + (σ : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff N β σ γ hσ
local notation "P" => contentInclusion D Sc cutoff N β
local notation "Q" => contentInclusion D Sc cutoff N γ
local notation "A" => truncatedAppend D Sc cutoff N σ

private theorem contentBlockInclusion_obj (δ : Multiset I)
    (s : ContentCategory D Sc cutoff N δ) :
    (contentInclusion D Sc cutoff N δ).obj s = s.obj := rfl
private theorem contentBlockInclusion_map (δ : Multiset I)
    (s t : ContentCategory D Sc cutoff N δ) (f : s ⟶ t) :
    (contentInclusion D Sc cutoff N δ).map f = f := rfl

/-- The selected comparison with both raw balanced-coend endpoints fixed generically. -/
def contentAppendToRestrictionLinear (M : ContentModules D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N γ) :
    BalancedInduction.Obj J M.toFunctor t →ₗ[k]
      BalancedInduction.Obj A (BalancedInduction.induced P M).toFunctor t.obj :=
  BalancedInduction.fullSquareRestrictionLinear J Q P A
    (contentAppendTo_inclusion D Sc cutoff N β σ γ hσ) M t

/-- Entire coefficient arrows remain unchanged and the actual input inclusion unit is inserted. -/
theorem contentAppendToRestrictionLinear_tensor (M : ContentModules D Sc cutoff N β)
    (s : ContentCategory D Sc cutoff N β) (t : ContentCategory D Sc cutoff N γ)
    (g : (A).obj s.obj ⟶ t.obj) (b : M.obj s) :
    contentAppendToRestrictionLinear D Sc cutoff N β σ γ hσ M t
      (BalancedInduction.tensor J M.toFunctor s g b) =
      BalancedInduction.tensor A (BalancedInduction.induced P M).toFunctor s.obj g
        (BalancedInduction.unit P M.toFunctor s b) := by
  have h := BalancedInduction.fullSquareRestrictionLinear_tensor J Q P A
    (contentAppendTo_inclusion D Sc cutoff N β σ γ hσ) M s t g b
  simpa only [contentAppendToRestrictionLinear, eqToHom_refl, Category.id_comp,
    contentBlockInclusion_obj, contentBlockInclusion_map] using h

end OddMath.QuiverHecke.ELVOld
