import OddMath.QuiverHecke.DividedPowerModules
import OddMath.QuiverHecke.AlgebraExamples

/-!
# Principal-projective consumers

BE2, arXiv:1701.04133v2, Lemma 11.1: the underlying left-module
splitting for countably many odd colours over the rational numbers.
Integer and parity shifts are not asserted by these examples.
-/

noncomputable section
namespace OddMath.QuiverHecke.DividedPowerModulesExamples
open DividedPowerModules AlgebraExamples
open OddMath.Frontier.BoxPartitionCount

/-- Every rank, including the two empty-product ranks. -/
def decomposition (i r : ℕ) :
    wordProjective datum scalars i r ≃ₗ[ModuleRing datum scalars r]
      (Sq r → oddProjective datum scalars i rfl r) :=
  oddDecompositionInHn datum scalars i rfl r

example (i r : ℕ) :
    Module.Projective (ModuleRing datum scalars r)
      (oddProjective datum scalars i rfl r) := inferInstance

example (i r : ℕ) (x : wordProjective datum scalars i r) :
    (decomposition i r).symm (decomposition i r x) = x :=
  (decomposition i r).symm_apply_apply x

example (i : ℕ) : wordProjective datum scalars i 0 ≃ₗ[ModuleRing datum scalars 0]
    (Sq 0 → oddProjective datum scalars i rfl 0) := decomposition i 0

example (i : ℕ) : wordProjective datum scalars i 1 ≃ₗ[ModuleRing datum scalars 1]
    (Sq 1 → oddProjective datum scalars i rfl 1) := decomposition i 1

/-- The unitization description has precisely the vectors of the original ideal. -/
def idealIdentification (r : ℕ) (e : A r) :
    (principal datum scalars e).restrictScalars ℚ ≃ₗ[ℚ]
      principalInHn datum scalars e := principalEquivHn datum scalars e

#print axioms decomposition
#print axioms idealIdentification

end OddMath.QuiverHecke.DividedPowerModulesExamples
