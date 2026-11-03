/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRectangularMate

/-! # Rouquier cup-crossing-cap in the PiSCat action target

Brundan–Ellis (1.13)–(1.14) uses the local rank-one Rouquier mate.
Its given component formula agrees with the rectangular cup-crossing-cap
used in the content matrix charts. Units and counits remain those of
the two specified adjunctions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u
variable {k : Type u} [CommRing k] {A B C : PiSCat.{u,u,u + 1} k}
  {E₁ : A ⟶ B} {F₁ : B ⟶ A} {E₂ : B ⟶ C} {F₂ : C ⟶ B}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)

/-- The prescribed Rouquier mate keeps the upper cup and lower cap at their distinct weight corners. -/
theorem rouquierMate_piscat_app (p : ZMod 2) (Z : B.carrier) :
    (rouquierMate A₁ A₂ t).app p Z =
      A₂.unit.app 0 (E₁.obj (F₁.obj Z)) ≫
        F₂.map (t.app p (F₁.obj Z)) ≫ F₂.map (E₂.map (A₁.counit.app 0 Z)) := by
  have hu := Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0)
  have hc := Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [rouquierMate, PiSCat.whiskerLeft_def, PiSCat.whiskerRight_def,
      Superfunctor.whiskerLeft_app, Superfunctor.whiskerRight_app, hu, hc]

/-- Both chosen mate conventions give the same whole supernatural map in PiSCat. -/
theorem rouquierMate_piscat_eq_rectangular :
    rouquierMate A₁ A₂ t = rectangularMate A₁ A₂ E₁ E₂ t := by
  apply Superfunctor.hom_ext
  intro p Z
  exact (rouquierMate_piscat_app A₁ A₂ t p Z).trans
    (rectangularMate_piscat_app A₁ A₂ E₁ E₂ t
      (Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0))
      (Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)) p Z).symm

end OddMath.SKM
