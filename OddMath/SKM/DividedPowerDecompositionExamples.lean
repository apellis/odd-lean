import OddMath.SKM.DividedPowerMultiplicity
import OddMath.SKM.TwoStrandShifts

/-! Concrete consumers for the algebraic portion of BE2 Lemma 11.1. -/

namespace OddMath.SKM.DividedPowerDecomposition.Examples

open OddMath.Frontier NilHeckeAction BoxPartitionCount Categorification
open DividedPowerIdempotents
open CategoryTheory StringDiagrams GradedSupercategory
open scoped BigOperators

noncomputable section

/-- The two factoradic tuples on two strands. -/
def lower : Sq 2 := ⟨fun _ => 0, mem_Sq.mpr fun _ => by omega⟩
def upper : Sq 2 := ⟨fun _ => 1, mem_Sq.mpr fun _ => by omega⟩

example : shift 0 lower = 1 ∧ shift 0 upper = 0 := by
  norm_num [shift, deg61, lower, upper, Fin.sum_univ_one]

/-- The exponent formula specializes to the coefficients of the landed EVEN
categorical rank-two normalization. This is a coefficient comparison, not an
unconstructed covariant equivalence between left ideals and Karoubi objects. -/
theorem even_twoStrand_coefficient
    {I X k : Type*} [AddCommGroup X] {D : Datum I X} [CommRing k]
    (Sc : Scalars D k) (sy : Symmetrizer D) (hc : Sc.Homogeneous)
    (i : I) (ν : X) (hi : D.parity i = 0) :
    letI := K₀.moduleLaurent k
      (CategoryTheory.Idempotents.Karoubi (CategoryTheory.Mat_ (TwoStrand.Base Sc sy hc i ν)))
    K₀.mk (TwoStrand.whole Sc sy hc i ν) =
      (LaurentPolynomial.T (sy.d i - 2 * sy.d i * shift 0 lower) +
       LaurentPolynomial.T (sy.d i - 2 * sy.d i * shift 0 upper) :
         LaurentPolynomial Zπ) • K₀.mk (TwoStrand.normalizedTwo Sc sy hc i ν hi) := by
  let := K₀.moduleLaurent k
    (CategoryTheory.Idempotents.Karoubi (CategoryTheory.Mat_ (TwoStrand.Base Sc sy hc i ν)))
  have hl : shift 0 lower = 1 := by
    norm_num [shift, deg61, lower, Fin.sum_univ_one]
  have hu : shift 0 upper = 0 := by
    norm_num [shift, deg61, upper, Fin.sum_univ_one]
  rw [hl, hu]
  have h : (sy.d i : ℤ) - 2 * (sy.d i : ℤ) * 1 = -(sy.d i : ℤ) := by omega
  simpa only [h, mul_zero, sub_zero] using
    TwoStrand.class_normalized_coefficient Sc sy hc i ν hi

/-- Both inverse laws in a nontrivial rank, with no assumed splitting data. -/
theorem rankThree_inverse (x : Presented 1)
    (y : Sq 3 → leftIdeal (oppositeProjector 1)) :
    (oddDecomposition 1).symm (oddDecomposition 1 x) = x ∧
      oddDecomposition 1 ((oddDecomposition 1).symm y) = y :=
  ⟨(oddDecomposition 1).symm_apply_apply x, (oddDecomposition 1).apply_symm_apply y⟩

example : (oddDecompositionAll 0).symm (oddDecompositionAll 0 1) = 1 :=
  (oddDecompositionAll 0).symm_apply_apply 1

example : (oddDecompositionAll 1).symm (oddDecompositionAll 1 1) = 1 :=
  (oddDecompositionAll 1).symm_apply_apply 1

/-- The same constructed splitting acts over the admissible field ℚ. -/
example (x : RationalPresented 0) :
    (oddDecompositionMap (n := 0) (rationalInclude 0).toRingHom).symm
      (oddDecompositionMap (n := 0) (rationalInclude 0).toRingHom x) = x :=
  (oddDecompositionMap (n := 0) (rationalInclude 0).toRingHom).symm_apply_apply x

example : oppositeProjector 0 * 1 * oppositeProjector 0 = 0 ∨
    oppositeProjector 0 * 1 * oppositeProjector 0 = oppositeProjector 0 :=
  oppositeProjector_primitive 1 (by
    have he : oppositeProjector 0 * oppositeProjector 0 = oppositeProjector 0 :=
      oppositeProjector_idempotent 0
    simp only [mul_one, he])

/-- The rank-two coefficient has BE2's orientation of the independent parity shift. -/
example {k : Type*} [CommRing k] (q : kˣ) (π : k) :
    (∑ ℓ ∈ Sq 2, multiplicity q π ℓ) = (q : k) + π * ((q⁻¹ : kˣ) : k) := by
  rw [sum_multiplicity]
  simp [OddMath.CoveringQuantum.qpFact, OddMath.CoveringQuantum.qpNat_two]

example : (∑ ℓ ∈ Sq 3, multiplicity (1 : ℤˣ) (-1 : ℤ) ℓ) = 0 := by
  rw [sum_multiplicity]
  norm_num [OddMath.CoveringQuantum.qpFact, OddMath.CoveringQuantum.qpNat]

example : summand 0 lower * summand 0 upper = 0 := by
  rw [summand_mul, ite_eq_right]
  intro h
  have hh := congrArg (fun z : Sq 2 => z.1 0) h
  norm_num [lower, upper] at hh

end
end OddMath.SKM.DividedPowerDecomposition.Examples
