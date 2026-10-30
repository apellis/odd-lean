/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform

/-! # Normalized crossing coordinates

Common-content representable coordinates for the mixed induction generator
of `DeformedActionAssembly.md` §5. Block-to-iterated comparison and the
reservoir Hom action are separate obligations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumGeneratorCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

def equivTo (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :
    BalancedInduction.Obj (contentAppendTo D Sc cutoff N β σ γ hσ)
      (contentRepresentableFunctor D Sc cutoff N β v) w ≃ₗ[k]
      ((contentAppendTo D Sc cutoff N β σ γ hσ).obj v ⟶ w) := by
  subst γ
  exact InductionRepresentable.equiv D Sc cutoff N β σ v w

@[simp] theorem equivTo_tensor (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) (v z : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ)
    (h : (contentAppendTo D Sc cutoff N β σ γ hσ).obj z ⟶ w) (g : v ⟶ z) :
    equivTo D Sc cutoff N β σ γ hσ v w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ)
        (contentRepresentableFunctor D Sc cutoff N β v) z h g) =
      (contentAppendTo D Sc cutoff N β σ γ hσ).map g ≫ h := by
  subst γ
  exact InductionRepresentable.forward_tensor D Sc cutoff N β σ v w z h g

@[simp] theorem equivTo_symm (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ)
    (h : (contentAppendTo D Sc cutoff N β σ γ hσ).obj v ⟶ w) :
    (equivTo D Sc cutoff N β σ γ hσ v w).symm h =
      BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ)
        (contentRepresentableFunctor D Sc cutoff N β v) v h (𝟙 v) := by
  subst γ
  rfl

/-- Normalized mixed crossing in common-content representable coordinates.
The induction mate reverses the crossing; total coefficient parity remains in the twist. -/
theorem mixedCross_coordinates (β : Multiset I) (i j : I) (hij : i ≠ j)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (h : (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)).obj v ⟶ w) :
    equivTo D Sc cutoff N β [i, j] _ rfl v w
      (((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v)).app (D.parity i * D.parity j) w
        ((equivTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j) v w).symm h)) =
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (crossTwo D Sc i j) v ≫ twist k (D.parity i * D.parity j) h := by
  rw [equivTo_symm]
  have ht := contentInductionCross_distinct_tensor D Sc cutoff N β i j hij
    (contentRepresentable D Sc cutoff N β v) w v h (𝟙 v)
  exact (congrArg (equivTo D Sc cutoff N β [i, j] _ rfl v w) ht).trans
    ((equivTo_tensor D Sc cutoff N β [i, j] _ rfl v v w
      (contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (crossTwo D Sc i j) v ≫ twist k (D.parity i * D.parity j) h) (𝟙 v)).trans
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp]))

/-- Normalized equal-colour crossing carries the source minus sign.
The induction mate reverses the crossing; total coefficient parity remains in the twist. -/
theorem equalCross_coordinates (β : Multiset I) (i : I)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, i] : Multiset I)))
    (h : (contentAppendTo D Sc cutoff N β [i, i] _ (content_pair_swap β i i)).obj v ⟶ w) :
    equivTo D Sc cutoff N β [i, i] _ rfl v w
      (((contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i)
        (contentRepresentable D Sc cutoff N β v)).app (D.parity i * D.parity i) w
        ((equivTo D Sc cutoff N β [i, i] _ (content_pair_swap β i i) v w).symm h)) =
      -(contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i i)
        (crossTwo D Sc i i) v ≫ twist k (D.parity i * D.parity i) h) := by
  rw [equivTo_symm]
  have ht := contentInductionCross_equal_tensor D Sc cutoff N β i
    (contentRepresentable D Sc cutoff N β v) w v h (𝟙 v)
  have he := equivTo_tensor D Sc cutoff N β [i, i] _ rfl v v w
    (contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i i)
      (crossTwo D Sc i i) v ≫ twist k (D.parity i * D.parity i) h) (𝟙 v)
  exact (congrArg (equivTo D Sc cutoff N β [i, i] _ rfl v w) ht).trans
    ((map_neg (equivTo D Sc cutoff N β [i, i] _ rfl v w) _).trans
      (congrArg Neg.neg (he.trans (by rw [CategoryTheory.Functor.map_id, Category.id_comp]))))

end OddMath.QuiverHecke.ELVOld.VacuumGeneratorCoordinates
