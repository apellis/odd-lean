import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerVacuum
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace NonVacuity.ELVCoefficientPowerVacuum
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev J := emptyCoefficientEmbedding (k := ℚ) D Sc cutoff
private abbrev R := coefficientPowerRegular (k := ℚ) D cutoff L

/-- The comparison is the chosen ordinary induction unit. -/
example : (coefficientPowerVacuumUnitIso D Sc cutoff L).hom =
    (BalancedInduction.adjunctionUnit J).app R :=
  BalancedInduction.fullyFaithfulUnitIso_hom J R

/-- Both maps use the actual balanced quotient and its prescribed
fully faithful unit inverse. -/
example (x : R.obj (SuperalgebraCat.star _)) :
    BalancedInduction.fullyFaithfulUnitInverse J R.toFunctor (SuperalgebraCat.star _)
      (BalancedInduction.unit J R.toFunctor (SuperalgebraCat.star _) x) = x :=
  LinearMap.congr_fun (BalancedInduction.fullyFaithfulUnitInverse_unit J R.toFunctor
    (SuperalgebraCat.star _)) x

end NonVacuity.ELVCoefficientPowerVacuum
