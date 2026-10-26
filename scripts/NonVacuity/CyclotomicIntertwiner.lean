import OddMath.QuiverHecke.CyclotomicAction.Intertwiner
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.SignedNilHeckeExamples

/-! Same-colour intertwiners (KKO arXiv:1206.5933v2, (8.7)–(8.8), Lemma 8.3, (8.15)) on the
odd colour of the all-odd two-colour datum, in the endomorphism rings of the words
`[true, true]` and `[true, true, true]`, and on the polynomial representation of the nilHecke
ring. -/
noncomputable section
open OddMath.QuiverHecke OddMath.QuiverHecke.SignedNilHecke
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
open Categorification.NilHecke Categorification.KLR.KL2.NH

/-- The odd relations on the word `[true, true]`. -/
theorem odd_pair : OddTwo (dotE datum scalars [true, true] 0) (dotE datum scalars [true, true] 1)
    (crossE datum scalars [true, true] 0) :=
  oddTwo_block datum scalars [] [] true rfl

example : dotE datum scalars [true, true] 1 *
      phiOdd (dotE datum scalars [true, true] 0) (dotE datum scalars [true, true] 1)
        (crossE datum scalars [true, true] 0) =
    -(phiOdd (dotE datum scalars [true, true] 0) (dotE datum scalars [true, true] 1)
        (crossE datum scalars [true, true] 0) * dotE datum scalars [true, true] 0) :=
  odd_pair.x_succ_mul_phiOdd

example : phiOdd (dotE datum scalars [true, true] 0) (dotE datum scalars [true, true] 1)
      (crossE datum scalars [true, true] 0) *
      phiOdd (dotE datum scalars [true, true] 0) (dotE datum scalars [true, true] 1)
        (crossE datum scalars [true, true] 0) =
    (dotE datum scalars [true, true] 1 - dotE datum scalars [true, true] 0) *
      (dotE datum scalars [true, true] 1 - dotE datum scalars [true, true] 0) :=
  odd_pair.phiOdd_mul_phiOdd

example : crossE datum scalars [true, true] 0 *
      OddMath.OddNilHecke.Intertwiner.element (dotE datum scalars [true, true] 0)
        (dotE datum scalars [true, true] 1) (crossE datum scalars [true, true] 0) =
    crossE datum scalars [true, true] 0 *
      (dotE datum scalars [true, true] 1 - dotE datum scalars [true, true] 0) *
        OddMath.OddNilHecke.Intertwiner.squareDiff (dotE datum scalars [true, true] 0)
          (dotE datum scalars [true, true] 1) :=
  odd_pair.element_identities.2.2.2.2

/-- A third strand anticommutes with the intertwiner of the first two. -/
example : dotE datum scalars [true, true, true] 2 *
      phiOdd (dotE datum scalars [true, true, true] 0) (dotE datum scalars [true, true, true] 1)
        (crossE datum scalars [true, true, true] 0) =
    -(phiOdd (dotE datum scalars [true, true, true] 0) (dotE datum scalars [true, true, true] 1)
        (crossE datum scalars [true, true, true] 0) * dotE datum scalars [true, true, true] 2) := by
  have hF := isSignedNilHeckeFamily_block datum scalars [] [] true 3
  rw [show datum.parity true = 1 from rfl, show zunit (1 : ZMod 2) = -1 by simp [zunit]] at hF
  exact hF.x_far_mul_phiOdd (a := 2) (j := 0) (by simp) (by simp) (by simp) (by simp)
    (by norm_num) (by norm_num)

/-- The even intertwiner squares to one on polynomials: it acts by the transposition. -/
example : phiEven (xv ℚ 3 0) (xv ℚ 3 1) (dd ℚ 3 0) * phiEven (xv ℚ 3 0) (xv ℚ 3 1) (dd ℚ 3 0) = 1 :=
  ((isSignedNilHeckeFamily_nilHecke ℚ 3).evenTwo (j := 0) le_rfl (by norm_num)).phiEven_mul_phiEven

example : gEven (xv ℚ 3 0) (xv ℚ 3 1) (dd ℚ 3 0) * gEven (xv ℚ 3 0) (xv ℚ 3 1) (dd ℚ 3 0) =
    -((xv ℚ 3 1 - xv ℚ 3 0) * (xv ℚ 3 1 - xv ℚ 3 0)) :=
  ((isSignedNilHeckeFamily_nilHecke ℚ 3).evenTwo (j := 0) le_rfl (by norm_num)).gEven_mul_gEven

#print axioms OddTwo.x_succ_mul_phiOdd
#print axioms OddTwo.x_mul_phiOdd
#print axioms OddTwo.phiOdd_mul_phiOdd
#print axioms OddTwo.element_identities
#print axioms IsSignedNilHeckeFamily.x_far_mul_element
#print axioms EvenTwo.phiEven_mul_phiEven
#print axioms EvenTwo.gEven_mul_gEven
#print axioms EvenTwo.t_mul_gEven
#print axioms IsSignedNilHeckeFamily.x_far_mul_phiOdd
#print axioms IsSignedNilHeckeFamily.t_far_mul_element
#print axioms IsSignedNilHeckeFamily.t_far_mul_phiEven
#print axioms oddTwo_block
#print axioms evenTwo_block
