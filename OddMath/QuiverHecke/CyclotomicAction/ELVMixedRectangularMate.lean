/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateLinear

/-! # The two-append specialization of the rectangular mate

Brundan–Ellis (1.12) uses the rectangular mate with equal lower and upper
append functors. Its whole raw linear map is identified with the
ordinary-coefficient mixed mate before specializing quotient categories.
This supplies the native module and input-natural inverse from the
proved truncated coend decoder.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
  {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

/-- Both bending constructions have the same whole linear map. -/
theorem orderedRectangularMateLinear_eq_mixed (N : Superfunctor k C (SVec k)) (t : C) :
    orderedRectangularMateLinear B A A B hα N t =
      orderedMixedMateLinear A B hα N t := by
  apply hom_ext
  intro s g b
  exact (orderedRectangularMateLinear_tensor B A A B hα N s t g b).trans
    (orderedMixedMateLinear_tensor A B hα N s t g b).symm

/-- Ordinary coefficient bijectivity is exactly native rectangular mate bijectivity. -/
theorem orderedRectangularMateLinear_bijective_iff (N : Superfunctor k C (SVec k)) (t : C) :
    Function.Bijective (orderedRectangularMateLinear B A A B hα N t) ↔
      Function.Bijective (orderedMixedMateCoend A B hα N t) := by
  rw [orderedRectangularMateLinear_eq_mixed, orderedMixedMateCoend_eq_linear]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
