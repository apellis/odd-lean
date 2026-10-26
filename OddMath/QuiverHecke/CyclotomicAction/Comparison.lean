/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Square
import OddMath.QuiverHecke.CyclotomicAction.CrossingTransformation

/-!
# Transporting the quadratic relation to superinduction

Ports the comparison mechanism of
`Categorification/KLR/CyclotomicAction/Comparison.lean`: equalities of the
concrete corner maps are carried through the even balanced-tensor comparison.
The same-colour crossing constructed in `CrossingTransformation` squares to
zero on every supermodule, including its odd morphisms. This is one upward
relation, not the projective Mackey comparison or local inversion.
-/
noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The comparison carries square-zero to the actual composed superinduction. -/
theorem inductionCrossingApp_square (M : CyclotomicSupermodules D Sc a ha n) :
    inductionCrossingApp D Sc i i a ha n M ≫
      inductionCrossingApp D Sc i i a ha n M = 0 := by
  unfold inductionCrossingApp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc (whiskerRight _ M), ← SuperBimodule.comp_whiskerRight,
    compositionSuperCrossing_square]
  simp [SuperBimodule.zero_whiskerRight]
/-- The homogeneous supernatural crossing component has square zero. -/
theorem cyclotomicSuperInductionCrossing_square
    (M : CyclotomicSupermodules D Sc a ha n) :
    (cyclotomicSuperInductionCrossing D Sc i i a ha n).app (D.parity i * D.parity i) M ≫
      (cyclotomicSuperInductionCrossing D Sc i i a ha n).app (D.parity i * D.parity i) M = 0 := by
  simpa [cyclotomicSuperInductionCrossing] using
    inductionCrossingApp_square D Sc i a ha n M

/-- Every homogeneous component of the vertical square vanishes. -/
theorem cyclotomicSuperInductionCrossing_vcomp_app (r : ZMod 2)
    (M : CyclotomicSupermodules D Sc a ha n) :
    ((cyclotomicSuperInductionCrossing D Sc i i a ha n).vcomp
      (cyclotomicSuperInductionCrossing D Sc i i a ha n)).app r M = 0 := by
  generalize hd : D.parity i * D.parity i = d
  fin_cases d <;> fin_cases r <;>
    simp [SuperNatTrans.vcomp, cyclotomicSuperInductionCrossing, hd,
      inductionCrossingApp_square]

end OddMath.QuiverHecke
