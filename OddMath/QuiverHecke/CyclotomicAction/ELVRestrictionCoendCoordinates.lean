/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCoefficientIso
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Ordinary coefficient coordinates for restriction coends

The mixed mate quotient comparison in Brundan–Ellis (1.12) uses the native
restriction module and the identical ordinary composition coefficient
functor. Their canonical coordinate equivalence is fixed before
specializing the old and truncated categories. The right action is unchanged.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A B : C ⥤ C) [B.Additive] [B.Linear k] [IsSuperfunctor k B]
  (M : Superfunctor k C (SVec k))

/-- Native restriction has the same ordinary coefficient functor. -/
def restrictionCoefficientCoordinates :
    ((restriction B).obj M).toFunctor ≅ B ⋙ M.toFunctor := Iso.refl _

/-- Both quotient coends use the identical ordinary right action. -/
def restrictionCoendCoordinates (w : C) :
    Obj A ((restriction B).obj M).toFunctor w ≃ₗ[k] Obj A (B ⋙ M.toFunctor) w :=
  coefficientEquiv A (restrictionCoefficientCoordinates B M) w

@[simp] theorem restrictionCoendCoordinates_tensor (s w : C) (g : A.obj s ⟶ w)
    (b : M.obj (B.obj s)) :
    restrictionCoendCoordinates A B M w
      (tensor A ((restriction B).obj M).toFunctor s g b) =
      tensor A (B ⋙ M.toFunctor) s g b :=
  coefficientEquiv_tensor A (restrictionCoefficientCoordinates B M) w s g b

@[simp] theorem restrictionCoendCoordinates_symm_tensor (s w : C) (g : A.obj s ⟶ w)
    (b : M.obj (B.obj s)) :
    (restrictionCoendCoordinates A B M w).symm
      (tensor A (B ⋙ M.toFunctor) s g b) =
      tensor A ((restriction B).obj M).toFunctor s g b :=
  coefficientMap_tensor A (restrictionCoefficientCoordinates B M).inv w s g b

/-- The same forward formula with its raw linear-map endpoint fixed. -/
theorem restrictionCoendCoordinates_hom_tensor (s w : C) (g : A.obj s ⟶ w)
    (b : M.obj (B.obj s)) :
    (restrictionCoendCoordinates A B M w).toLinearMap
      (tensor A ((restriction B).obj M).toFunctor s g b) =
      tensor A (B ⋙ M.toFunctor) s g b :=
  coefficientMap_tensor A (restrictionCoefficientCoordinates B M).hom w s g b

/-- The inverse coefficient map retains both literal tensor factors. -/
theorem restrictionCoendCoordinates_inv_tensor (s w : C) (g : A.obj s ⟶ w)
    (b : M.obj (B.obj s)) :
    (restrictionCoendCoordinates A B M w).symm.toLinearMap
      (tensor A (B ⋙ M.toFunctor) s g b) =
      tensor A ((restriction B).obj M).toFunctor s g b :=
  coefficientMap_tensor A (restrictionCoefficientCoordinates B M).inv w s g b

end OddMath.QuiverHecke.ELVOld.BalancedInduction
