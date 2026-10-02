import OddMath.Frontier.EQHalfGradedUnitDerived
import DG.HalfGraded.Derived

/-!
# Actual internal-shift and parity compatibility of the integral unit

Restriction along the weight-unit functor commutes with the existing internal
shifts in every rank. Its compatibility with the cohomological shift then gives
compatibility with the actual parity functor `Π = ⟨-2⟩ ⋙ ⟦1⟧`. For ranks zero and
one this comparison passes across the unit and counit of Keller's equivalence to
actual derived induction. No action is defined by transport, and no numerical
Grothendieck-group calculation is asserted.
-/

noncomputable section
universe w w₂
namespace OddMath.Frontier.EQHalfGradedUnit
open CategoryTheory DG

/-- The actual unit functor commutes on the nose with translation of weights. -/
theorem weightFunctor_shift (N : ℕ) (s : ℤ) :
    WeightCategory.shiftFunctor source.Regraded s ⋙ weightFunctor N =
      weightFunctor N ⋙ WeightCategory.shiftFunctor (target N).Regraded s := rfl

variable {N : ℕ}
  [CatModule.HasDerivedCategory.{w, w} (WeightCategory source.Regraded)]
  [CatModule.HasDerivedCategory.{w₂, w} (WeightCategory (target N).Regraded)]

variable (N) in
/-- Actual derived restriction commutes with every existing internal shift. -/
def restrictInternalShiftIso (s : ℤ) :
    CatModule.DerivedCategory.restrict (weightFunctor N) ⋙
        CatModule.DerivedCategory.internalShift source.Regraded s ≅
      CatModule.DerivedCategory.internalShift (target N).Regraded s ⋙
        CatModule.DerivedCategory.restrict (weightFunctor N) :=
  (CatModule.DerivedCategory.restrictCompIso
    (WeightCategory.shiftFunctor source.Regraded s) (weightFunctor N)).symm ≪≫
  CatModule.DerivedCategory.restrictCompIso (weightFunctor N)
    (WeightCategory.shiftFunctor (target N).Regraded s)

variable (N) in
/-- Actual derived restriction commutes with the actual parity functors. -/
def restrictParityIso :
    CatModule.DerivedCategory.restrict (weightFunctor N) ⋙
        HalfGradedDGRing.parityShiftD source ≅
      HalfGradedDGRing.parityShiftD (target N) ⋙
        CatModule.DerivedCategory.restrict (weightFunctor N) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictInternalShiftIso N (-2)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((CatModule.DerivedCategory.restrict (weightFunctor N)).commShiftIso (1 : ℤ)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Pass a comparison for the inverse of this equivalence to its forward functor.
The two endofunctors are supplied independently; neither is defined by transport. -/
def forwardComparison (hN : N ≤ 1)
    (S : CatModule.DerivedCategory.{w, w} (WeightCategory source.Regraded) ⥤
      CatModule.DerivedCategory.{w, w} (WeightCategory source.Regraded))
    (T : CatModule.DerivedCategory.{w₂, w} (WeightCategory (target N).Regraded) ⥤
      CatModule.DerivedCategory.{w₂, w} (WeightCategory (target N).Regraded))
    (e : (derivedEquivalence hN).inverse ⋙ S ≅ T ⋙ (derivedEquivalence hN).inverse) :
    (derivedEquivalence hN).functor ⋙ T ≅ S ⋙ (derivedEquivalence hN).functor := by
  let E := derivedEquivalence hN
  calc
    E.functor ⋙ T ≅ (E.functor ⋙ T) ⋙ (E.inverse ⋙ E.functor) :=
      (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ E.counitIso.symm
    _ ≅ ((E.functor ⋙ T) ⋙ E.inverse) ⋙ E.functor :=
      (Functor.associator _ _ _).symm
    _ ≅ (E.functor ⋙ (T ⋙ E.inverse)) ⋙ E.functor :=
      Functor.isoWhiskerRight (Functor.associator _ _ _) _
    _ ≅ (E.functor ⋙ (E.inverse ⋙ S)) ⋙ E.functor :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft E.functor e.symm) _
    _ ≅ ((E.functor ⋙ E.inverse) ⋙ S) ⋙ E.functor :=
      Functor.isoWhiskerRight (Functor.associator _ _ _).symm _
    _ ≅ (𝟭 _ ⋙ S) ⋙ E.functor :=
      Functor.isoWhiskerRight (Functor.isoWhiskerRight E.unitIso.symm S) _
    _ ≅ S ⋙ E.functor := Functor.isoWhiskerRight (Functor.leftUnitor S) _

/-- Low-rank derived induction commutes with every actual internal shift. -/
def derivedEquivalenceInternalShiftIso (hN : N ≤ 1) (s : ℤ) :
    (derivedEquivalence hN).functor ⋙
        CatModule.DerivedCategory.internalShift (target N).Regraded s ≅
      CatModule.DerivedCategory.internalShift source.Regraded s ⋙
        (derivedEquivalence hN).functor :=
  forwardComparison hN _ _ (restrictInternalShiftIso N s)

/-- Low-rank derived induction commutes with the actual half-graded parity shift. -/
def derivedEquivalenceParityIso (hN : N ≤ 1) :
    (derivedEquivalence hN).functor ⋙ HalfGradedDGRing.parityShiftD (target N) ≅
      HalfGradedDGRing.parityShiftD source ⋙ (derivedEquivalence hN).functor :=
  forwardComparison hN _ _ (restrictParityIso N)

end OddMath.Frontier.EQHalfGradedUnit
