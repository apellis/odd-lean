import OddMath.Frontier.EQHalfGradedUnitQuasiEquivalence
import DG.K0.DGCategory

/-!
# Integral low-rank half-graded derived equivalence

Keller's theorem applied to the actual weight-category unit functor gives an
equivalence on all half-graded dg modules in ranks zero and one, not only on
modules in the diagonal image. It induces an equivalence of ordinary compact
Grothendieck groups and preserves the representable class at every weight.
This is not a numerical K₀ calculation, a super-K₀ quotient comparison, or a
tensor-product formula.
-/

noncomputable section
universe w w₂
namespace OddMath.Frontier.EQHalfGradedUnit
open CategoryTheory DG

variable {N : ℕ}
  [CatModule.HasDerivedCategory.{w, w} (WeightCategory source.Regraded)]
  [CatModule.HasDerivedCategory.{w₂, w} (WeightCategory (target N).Regraded)]

/-- Derived induction along the actual low-rank half-graded unit is an equivalence. -/
def derivedEquivalence (hN : N ≤ 1) :
    CatModule.DerivedCategory.{w, w} (WeightCategory source.Regraded) ≌
      CatModule.DerivedCategory.{w₂, w} (WeightCategory (target N).Regraded) :=
  CatModule.DerivedCategory.kellerEquivalence (QuasiIso.weightFunctor_isQuasiEquivalence hN)

/-- The forward functor is actual derived induction, not an unspecified equivalence. -/
@[simp] theorem derivedEquivalence_functor (hN : N ≤ 1) :
    (derivedEquivalence hN).functor = CatModule.DerivedCategory.induction (weightFunctor N) :=
  rfl

/-- The inverse is restriction along the same unit functor. -/
@[simp] theorem derivedEquivalence_inverse (hN : N ≤ 1) :
    (derivedEquivalence hN).inverse = CatModule.DerivedCategory.restrict (weightFunctor N) :=
  rfl

/-- The equivalence commutes with the actual cohomological shift. -/
instance derivedEquivalence_commShift (hN : N ≤ 1) :
    (derivedEquivalence hN).functor.CommShift ℤ :=
  inferInstanceAs ((CatModule.DerivedCategory.induction.{w, w₂, w}
    (weightFunctor N)).CommShift ℤ)

/-- The equivalence preserves distinguished triangles. -/
instance derivedEquivalence_isTriangulated (hN : N ≤ 1) :
    (derivedEquivalence hN).functor.IsTriangulated :=
  inferInstanceAs (CatModule.DerivedCategory.induction.{w, w₂, w}
    (weightFunctor N)).IsTriangulated

/-- Equivalence of ordinary Grothendieck groups of compact half-graded modules. -/
def compactK0Equiv (hN : N ≤ 1) :
    DGCategory.K0.{w, w} (WeightCategory source.Regraded) ≃+
      DGCategory.K0.{w₂, w} (WeightCategory (target N).Regraded) :=
  DGCategory.K0.mapEquivOfIsQuasiEquivalence (weightFunctor N)
    (QuasiIso.weightFunctor_isQuasiEquivalence hN)

/-- Every weight representable class is sent to the representable at that same weight. -/
theorem compactK0Equiv_representable (hN : N ≤ 1) (X : WeightCategory source.Regraded) :
    compactK0Equiv hN (DGCategory.K0.representable X) =
      DGCategory.K0.representable ((weightFunctor N).obj X) :=
  DGCategory.K0.map_representable (weightFunctor N) X

end OddMath.Frontier.EQHalfGradedUnit
