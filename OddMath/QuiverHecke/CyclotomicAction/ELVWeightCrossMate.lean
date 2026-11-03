/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMateInverse

/-! # The sideways crossing on ELV weight spaces

Brundan–Ellis (1.11)–(1.12): the presentation's ordered cup–crossing–cap
is the already constructed rectangular mate, with the same crossing and
both prescribed adjunctions. Its inverse therefore requires no new premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u
variable {k : Type u} [CommRing k] {A B C D : PiSCat.{u,u,u + 1} k}
  {E₁ : A ⟶ B} {F₁ : B ⟶ A} {E₂ : C ⟶ D} {F₂ : D ⟶ C}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (g : A ⟶ C) (h : B ⟶ D) (t : g ≫ E₂ ⟶ E₁ ≫ h)

/-- The presentation mate keeps all four weight corners independent. -/
theorem crossMate_piscat_app (p : ZMod 2) (Z : B.carrier) :
    (crossMate A₁ A₂ t).app p Z =
      A₂.unit.app 0 (g.obj (F₁.obj Z)) ≫
        F₂.map (t.app p (F₁.obj Z)) ≫ F₂.map (h.map (A₁.counit.app 0 Z)) := by
  have hu := Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0)
  have hc := Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [crossMate, PiSCat.whiskerLeft_def, PiSCat.whiskerRight_def,
      Superfunctor.whiskerLeft_app, Superfunctor.whiskerRight_app, hu, hc]

/-- The two mate conventions agree for the prescribed even bending maps. -/
theorem crossMate_piscat_eq_rectangular :
    crossMate A₁ A₂ t = rectangularMate A₁ A₂ g h t := by
  apply Superfunctor.hom_ext
  intro p Z
  exact (crossMate_piscat_app A₁ A₂ g h t p Z).trans
    (rectangularMate_piscat_app A₁ A₂ g h t
      (Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0))
      (Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)) p Z).symm
end OddMath.SKM

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d : X}
  (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
  (h₃ : a + D.α i = c) (h₄ : c + D.α j = d)

/-- The chosen sideways crossing is the constructed rectangular weight mate. -/
theorem elvActionCrossMate_eq :
    SKM.crossMate (elvActionAdjunction D Sc cutoff bound i Λ h₃)
      (elvActionAdjunction D Sc cutoff bound i Λ h₂)
      (elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) =
      elvWeightMixedMate D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂ :=
  SKM.crossMate_piscat_eq_rectangular _ _ _ _ _

/-- The exact distinct-colour inversion field of the presentation. -/
theorem elvActionCrossMate_isIso (hij : i ≠ j) :
    IsIso (SKM.crossMate (elvActionAdjunction D Sc cutoff bound i Λ h₃)
      (elvActionAdjunction D Sc cutoff bound i Λ h₂)
      (elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄)) := by
  rw [elvActionCrossMate_eq]
  exact elvWeightMixedMate_isIso D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂ hij.symm
end OddMath.QuiverHecke.ELVOld
