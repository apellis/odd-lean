import OddMath

/-! BE2 Lemma 11.1: odd principal-module splitting over rational coefficients. -/
noncomputable section
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples
open OddMath.QuiverHecke.DividedPowerModules
open OddMath.Frontier.BoxPartitionCount

example (r : ℕ) :
    wordProjective datum scalars 0 r ≃ₗ[ModuleRing datum scalars r]
      (Sq r → oddProjective datum scalars 0 rfl r) :=
  oddDecompositionInHn datum scalars 0 rfl r

example (r : ℕ) : Module.Projective (ModuleRing datum scalars r)
    (oddProjective datum scalars 0 rfl r) := inferInstance

#print axioms OddMath.QuiverHecke.DividedPowerModules.oddDecompositionInHn
#print axioms OddMath.QuiverHecke.DividedPowerModules.principalEquivHn
#print axioms OddMath.QuiverHecke.DividedPowerModules.oddDecompositionInHn_degree
#print axioms OddMath.QuiverHecke.DividedPowerModules.oddDecompositionInHn_symm_degree
#print axioms OddMath.QuiverHecke.DividedPowerModules.oddDecompositionInHn_degree_small
#print axioms OddMath.SKM.DividedPowerDecomposition.sum_shift_monomial
