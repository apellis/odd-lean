/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierMixedMate
import StringDiagrams.Super.SCat

/-! # Rectangular mate components between four weight spaces

Brundan–Ellis (1.12) uses the selected crossing between the two orders
of different induction functors, bent by two j-adjunctions at different
weights. The cup and cap are even; the middle crossing may be odd.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u
variable {k : Type u} [CommRing k]
  {a b c d : PiSCat.{u,u,u + 1} k}
  {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₃ : c ⟶ d} {F₃ : d ⟶ c}

/-- All four corner categories remain independent in the component formula. -/
theorem rectangularMate_piscat_app
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (g : a ⟶ c) (h : b ⟶ d) (z : g ≫ E₃ ⟶ E₁ ≫ h)
    (hu : ∀ Z, A₃.unit.app 1 Z = 0) (hc : ∀ Z, A₁.counit.app 1 Z = 0)
    (r : ZMod 2) (Z : b.carrier) :
    (rectangularMate A₁ A₃ g h z).app r Z =
      A₃.unit.app 0 (g.obj (F₁.obj Z)) ≫
        F₃.map (z.app r (F₁.obj Z)) ≫ F₃.map (h.map (A₁.counit.app 0 Z)) := by
  rw [rectangularMate_eq]
  rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp [PiSCat.whiskerLeft_def, PiSCat.whiskerRight_def,
      Superfunctor.whiskerLeft_app, Superfunctor.whiskerRight_app, hu, hc]

/-- Even bending maps retain the complete crossing degree at all four corners. -/
theorem rectangularMate_piscat_mem
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (g : a ⟶ c) (h : b ⟶ d) {p : ZMod 2} (z : g ≫ E₃ ⟶ E₁ ≫ h)
    (hz : z ∈ parity (R := k) _ _ p) :
    rectangularMate A₁ A₃ g h z ∈ parity (R := k) _ _ p := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext Z
  rw [rectangularMate_piscat_app A₁ A₃ g h z
    (fun W => Superfunctor.app_eq_zero_of_mem A₃.unit_mem (by decide) W)
    (fun W => Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide) W)]
  rw [Superfunctor.app_eq_zero_of_mem hz hq]
  simp only [Superfunctor.map, CategoryTheory.Functor.map_zero,
    CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]
  rfl

end OddMath.SKM
