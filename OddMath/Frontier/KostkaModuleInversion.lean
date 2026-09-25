import OddMath.Frontier.DegreeShapes
import OddMath.SkewPolynomial

/-!
# Module-valued inversion of the exhaustive signed Kostka matrix

Row-vector convention: H(j) = sum_i K(i,j) • S(i), so recovery uses
K⁻¹(j,i). Coefficients are the genuine normalized signed tableau counts.
Only the algebraic inversion component is proved: no complete-product
expansion, symmetry/kernel membership, or Schur comparison is assumed.
-/
namespace OddMath.Frontier.KostkaModuleInversion
open scoped BigOperators
noncomputable section
variable {V : Type*} [AddCommGroup V]

def transform (d : ℕ) (S : DegreeShapes.DegreeShape d → V) :
    DegreeShapes.DegreeShape d → V := by
  classical
  letI := DegreeShapes.degreeFintype d
  exact fun j => ∑ i, TableauDominance.signedKostka i.val j.val • S i

def recover (d : ℕ) (H : DegreeShapes.DegreeShape d → V) :
    DegreeShapes.DegreeShape d → V := by
  classical
  letI := DegreeShapes.degreeFintype d
  let K := SignedKostkaInvertibility.kostkaMatrix (fun i : DegreeShapes.DegreeShape d => i.val)
  exact fun i => ∑ j, (K⁻¹) j i • H j

-- The finite-sum argument works in every additive commutative group,
-- not just in the scalar module used by the earlier matrix equivalence.
private theorem compose_action {I : Type*} [Fintype I]
    (A B : Matrix I I ℤ) (S : I → V) (k : I) :
    (∑ j, B j k • (∑ i, A i j • S i)) = ∑ i, (A * B) i k • S i := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

private theorem identity_action {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → V) (k : I) : (∑ i, (1 : Matrix I I ℤ) i k • S i) = S k := by
  simp [Matrix.one_apply]

theorem leftInverse (d : ℕ) (S : DegreeShapes.DegreeShape d → V) :
    recover d (transform d S) = S := by
  classical
  letI := DegreeShapes.degreeFintype d
  let K := SignedKostkaInvertibility.kostkaMatrix (fun i : DegreeShapes.DegreeShape d => i.val)
  have hu : IsUnit K.det := by
    have hd := SignedKostkaInvertibility.kostkaMatrix_det
      (fun i : DegreeShapes.DegreeShape d => i.val) (fun _ _ h => Subtype.ext h)
    change IsUnit (SignedKostkaInvertibility.kostkaMatrix
      (fun i : DegreeShapes.DegreeShape d => i.val)).det
    rw [hd]
    exact isUnit_one
  funext i
  change (∑ j, K⁻¹ j i • (∑ k, K k j • S k)) = S i
  rw [compose_action, Matrix.mul_nonsing_inv _ hu, identity_action]

theorem rightInverse (d : ℕ) (H : DegreeShapes.DegreeShape d → V) :
    transform d (recover d H) = H := by
  classical
  letI := DegreeShapes.degreeFintype d
  let K := SignedKostkaInvertibility.kostkaMatrix (fun i : DegreeShapes.DegreeShape d => i.val)
  have hu : IsUnit K.det := by
    have hd := SignedKostkaInvertibility.kostkaMatrix_det
      (fun i : DegreeShapes.DegreeShape d => i.val) (fun _ _ h => Subtype.ext h)
    change IsUnit (SignedKostkaInvertibility.kostkaMatrix
      (fun i : DegreeShapes.DegreeShape d => i.val)).det
    rw [hd]
    exact isUnit_one
  funext j
  change (∑ i, K i j • (∑ k, K⁻¹ k i • H k)) = H j
  rw [compose_action, Matrix.nonsing_inv_mul _ hu, identity_action]

theorem uniqueSolution (d : ℕ) (H : DegreeShapes.DegreeShape d → V) :
    ∃! S, transform d S = H := by
  refine ⟨recover d H, rightInverse d H, ?_⟩
  intro S hS
  rw [← hS, leftInverse]

theorem submoduleTarget (d : ℕ) (A : Submodule ℤ V)
    (S : DegreeShapes.DegreeShape d → V) :
    (∀ j, transform d S j ∈ A) ↔ ∀ i, S i ∈ A := by
  classical
  letI := DegreeShapes.degreeFintype d
  constructor
  · intro h i
    rw [← leftInverse d S]
    exact A.sum_mem (fun j _ => A.smul_mem _ (h j))
  · intro h j
    exact A.sum_mem (fun i _ => A.smul_mem _ (h i))

theorem polynomialTarget (n d : ℕ)
    (S : DegreeShapes.DegreeShape d → OddMath.SkewPolynomial.SkewPolynomial n) :
    recover d (transform d S) = S := leftInverse d S

end
end OddMath.Frontier.KostkaModuleInversion
