import OddMath

/-! BE2 §11: locally unital `H_n` for countably many odd colours over `ℚ`. -/
noncomputable section
open scoped Classical
open CategoryTheory OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

example (n : ℕ) : NonUnitalRing (A n) := inferInstance
example (n : ℕ) : Module ℚ (A n) := inferInstance
example (n : ℕ) : IsScalarTower ℚ (A n) (A n) := inferInstance
example (n : ℕ) : SMulCommClass ℚ (A n) (A n) := inferInstance
example (n : ℕ) : SetLike.GradedMul (Hn.bidegree datum scalars symmetrizer homogeneous n) :=
  inferInstance

example : cross 0 1 * cross 0 1 = 0 := cross_self_zero
example : cross 0 1 * cross 1 0 =
    Hn.single (twoWord 1 0) (twoWord 1 0) (crossHom 1 0 ≫ crossHom 0 1) := cross_product
example : cross 0 1 ∈ Hn.bidegree datum scalars symmetrizer homogeneous 2 (0,1) := cross_bidegree
example : dot 0 * dot 0 ∈ Hn.bidegree datum scalars symmetrizer homogeneous 1 (4,0) :=
  dot_square_bidegree 0
example : (Hn.wordIdempotent emptyWord : A 0) * Hn.wordIdempotent emptyWord =
    Hn.wordIdempotent emptyWord := empty_idempotent
example : (Hn.wordIdempotent (twoWord 0 1) : A 2) * Hn.wordIdempotent (twoWord 1 0) = 0 :=
  orthogonal_words
example : ∃ s : Finset (Word ℕ 1),
    Hn.localUnit (D := datum) (Sc := scalars) s * Hn.localUnit s = Hn.localUnit s ∧
      ∀ a ∈ ({dot 0, dot 1 * dot 1} : Finset (A 1)),
        Hn.localUnit s * a = a ∧ a * Hn.localUnit s = a := polynomial_local_unit 0 1
example (n : ℕ) : DirectSum.IsInternal (Hn.bidegree datum scalars symmetrizer homogeneous n) :=
  internal_grading n
example : Function.Injective (Hn.cornerInclusion (D := datum) (Sc := scalars) (oneWord 0)) :=
  Hn.cornerInclusion_injective _

example (i n : ℕ) :
    Hn.sameColourInclusion (D := datum) (Sc := scalars) i n 1 =
      Hn.wordIdempotent (repeatedWord i n) := Hn.sameColourInclusion_one i n
example : Function.Injective (Hn.sameColourInclusion (D := datum) (Sc := scalars) 0 2) :=
  Hn.sameColourInclusion_injective 0 2

#print axioms Hn.exists_localUnit
#print axioms Hn.mem_range_cornerInclusion_iff
#print axioms Hn.isInternal_bidegree
#print axioms Hn.mul_mem_bidegree
#print axioms Hn.wordIdempotent_mem_bidegree
#print axioms dot_corner
#print axioms cross_product
#print axioms cross_bidegree
