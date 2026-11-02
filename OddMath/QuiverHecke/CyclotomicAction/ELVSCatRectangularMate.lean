/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierMixedMate
import StringDiagrams.Super.SCat

/-! # Rectangular cup-crossing-cap components in SCat

The component expansion needed by the prescribed distinct-colour mate of
Brundan–Ellis (1.12). Both bending adjunctions are the same even adjunction;
the crossing changes the order of two different induction functors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u
variable {k : Type u} [CommRing k] {C : SCat.{u,u,u + 1} k}

theorem rectangularMate_scat_app {E F H : C ⟶ C}
    (A : SuperAdjunction (k := k) E F) (z : H ≫ E ⟶ E ≫ H)
    (hu : ∀ Z, A.unit.app 1 Z = 0) (hc : ∀ Z, A.counit.app 1 Z = 0)
    (r : ZMod 2) (Z : C.carrier) :
    (rectangularMate A A H H z).app r Z =
      A.unit.app 0 (Superfunctor.obj H (Superfunctor.obj F Z)) ≫
        F.map (z.app r (Superfunctor.obj F Z)) ≫
          F.map (H.map (A.counit.app 0 Z)) := by
  rw [rectangularMate_eq]
  rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp [SCat.whiskerLeft_def, SCat.whiskerRight_def,
      Superfunctor.whiskerLeft_app, Superfunctor.whiskerRight_app, hu, hc]

end OddMath.SKM
