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

end OddMath.QuiverHecke.ELVOld
