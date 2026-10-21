import OddMath.QuiverHecke.DividedPowerGrading
import OddMath.QuiverHecke.AlgebraExamples

/-!
# Principal-projective consumers

BE2, arXiv:1701.04133v2, Lemma 11.1: the underlying left-module
splitting for countably many odd colours over the rational numbers, and
its integer/parity shifts.
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

/-- In rank `n + 2` the summand `ℓ` is shifted by the splitter's bidegree. -/
example (i n : ℕ) {d : ℤ × ZMod 2} (x : wordProjective datum scalars i (n + 2))
    (hx : PrincipalDegree datum scalars symmetrizer homogeneous d x) (ℓ : Sq (n + 2)) :
    PrincipalDegree datum scalars symmetrizer homogeneous
      (d + splitterDegree datum symmetrizer i n ℓ) (decomposition i (n + 2) x ℓ) :=
  oddDecompositionInHn_degree datum scalars symmetrizer homogeneous i rfl x hx ℓ

example (i n : ℕ) {d : ℤ × ZMod 2} (y : Sq (n + 2) → oddProjective datum scalars i rfl (n + 2))
    (hy : ∀ ℓ, PrincipalDegree datum scalars symmetrizer homogeneous
      (d + splitterDegree datum symmetrizer i n ℓ) (y ℓ)) :
    PrincipalDegree datum scalars symmetrizer homogeneous d ((decomposition i (n + 2)).symm y) :=
  oddDecompositionInHn_symm_degree datum scalars symmetrizer homogeneous i rfl y hy

example (i : ℕ) {d : ℤ × ZMod 2} (x : wordProjective datum scalars i 1)
    (hx : PrincipalDegree datum scalars symmetrizer homogeneous d x) (ℓ : Sq 1) :
    PrincipalDegree datum scalars symmetrizer homogeneous d (decomposition i 1 x ℓ) :=
  oddDecompositionInHn_degree_small datum scalars symmetrizer homogeneous i rfl (by omega) x hx ℓ

#print axioms decomposition
#print axioms idealIdentification

end OddMath.QuiverHecke.DividedPowerModulesExamples
