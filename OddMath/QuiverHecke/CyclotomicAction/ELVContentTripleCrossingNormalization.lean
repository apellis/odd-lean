/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations

/-! # Normalization of independently whiskered triple crossings -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentTripleRight_whisker (i j l : I) :
    contentTripleRight D Sc i j l = (pres D Sc).obj (ob D [i]) ◁ crossTwo D Sc j l := by
  rw [crossTwo, cl_whiskerLeft]
  rfl

/-- Suffix crossing defined by the pair crossing on the first induced module. -/
def contentWhiskeredSuffixCross (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([i,l,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentETripleTo D Sc cutoff N β i l j γ ht).obj M).obj z ⟶
      ((contentETripleTo D Sc cutoff N β i j l γ h).obj M).obj z :=
  ((contentEPairCrossTransform D Sc cutoff N (β + ([i] : Multiset I)) j l γ
    (by rw [add_assoc]; exact h) (by rw [add_assoc]; exact ht)).app
    (D.parity j * D.parity l)
    (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M)).total z

end OddMath.QuiverHecke.ELVOld
