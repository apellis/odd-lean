import OddMath.QuiverHecke.CyclotomicAction.IntertwinerWords
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.SignedNilHeckeExamples

/-! Same-colour intertwiners (KKO arXiv:1206.5933v2, (8.7)–(8.8), Lemma 8.3, (8.15)) on the
odd colour of the all-odd two-colour datum, in the endomorphism rings of the words
`[true, true]` and `[true, true, true]`, and on the polynomial representation of the nilHecke
ring. -/
noncomputable section
open CategoryTheory OddMath.QuiverHecke OddMath.QuiverHecke.SignedNilHecke
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

/-- The dot passes through the crossing of two distinct odd colours with a minus sign. -/
example : dotE datum scalars [true, false] 0 ≫ intertwinerHom datum scalars [] [] true false =
    -(intertwinerHom datum scalars [] [] true false ≫ dotE datum scalars [false, true] 1) := by
  have h := dot_comp_intertwinerHom datum scalars [] [] true false
  simpa [OddMath.SKM.zsign, datum] using h

/-- On two strands of the odd colour, `g` is KKO's odd variant and the dot changes sign. -/
example : dotE datum scalars [true, true] 1 ≫ intertwinerHom datum scalars [] [] true true =
    -(intertwinerHom datum scalars [] [] true true ≫ dotE datum scalars [true, true] 0) := by
  have h := dot_succ_comp_intertwinerHom datum scalars [] [] true true
  simpa [OddMath.SKM.zsign, datum] using h

example : intertwinerHom datum scalars [] [] true true =
    OddMath.OddNilHecke.Intertwiner.element (dotE datum scalars [true, true] 0)
      (dotE datum scalars [true, true] 1) (crossE datum scalars [true, true] 0) := by
  rw [intertwinerHom_self]
  simp [sameIntertwiner, datum]

/-- The braid identity for the odd variants on three strands of the odd colour. -/
example : crossE datum scalars [true, true, true] 0 *
      (OddMath.OddNilHecke.Intertwiner.element (dotE datum scalars [true, true, true] 1)
          (dotE datum scalars [true, true, true] 2) (crossE datum scalars [true, true, true] 1) *
        OddMath.OddNilHecke.Intertwiner.element (dotE datum scalars [true, true, true] 0)
          (dotE datum scalars [true, true, true] 1) (crossE datum scalars [true, true, true] 0)) =
    OddMath.OddNilHecke.Intertwiner.element (dotE datum scalars [true, true, true] 1)
        (dotE datum scalars [true, true, true] 2) (crossE datum scalars [true, true, true] 1) *
      OddMath.OddNilHecke.Intertwiner.element (dotE datum scalars [true, true, true] 0)
        (dotE datum scalars [true, true, true] 1) (crossE datum scalars [true, true, true] 0) *
      crossE datum scalars [true, true, true] 1 := by
  have hF := isSignedNilHeckeFamily_block datum scalars [] [] true 3
  rw [show datum.parity true = 1 from rfl, show zunit (1 : ZMod 2) = -1 by simp [zunit]] at hF
  exact hF.braid_element (j := 0) (by simp) (by simp)

/-- The even intertwiners satisfy the braid identity on polynomials in three variables. -/
example : dd ℚ 3 0 * (phiEven (xv ℚ 3 1) (xv ℚ 3 2) (dd ℚ 3 1) * phiEven (xv ℚ 3 0) (xv ℚ 3 1)
      (dd ℚ 3 0)) =
    phiEven (xv ℚ 3 1) (xv ℚ 3 2) (dd ℚ 3 1) * phiEven (xv ℚ 3 0) (xv ℚ 3 1) (dd ℚ 3 0) *
      dd ℚ 3 1 :=
  (isSignedNilHeckeFamily_nilHecke ℚ 3).braid_phiEven (j := 0) le_rfl (by norm_num)

#print axioms IsSignedNilHeckeFamily.braid_phiOdd
#print axioms IsSignedNilHeckeFamily.braid_element
#print axioms IsSignedNilHeckeFamily.braid_phiEven
#print axioms IsSignedNilHeckeFamily.braid_gEven
/-- The dot on the moving odd strand reaches the end of `[true, false, true]` with the sign
`(-1)^{p(true)(p(false) + p(true))} = 1`. -/
example : dotE datum scalars [true, false, true] 0 ≫ moveHom datum scalars true [] [false, true] =
    moveHom datum scalars true [] [false, true] ≫ dotE datum scalars [false, true, true] 2 := by
  have h := dot_comp_moveHom datum scalars true [] [false, true]
  have hs : OddMath.SKM.zsign ℚ (datum.parity true * wordParity datum [false, true]) = 1 := by
    simp [OddMath.SKM.zsign, wordParity, datum]
  rw [hs, one_smul] at h
  exact h

#print axioms dot_comp_moveHom
#print axioms dot_comp_intertwinerHom
#print axioms dot_succ_comp_intertwinerHom
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
