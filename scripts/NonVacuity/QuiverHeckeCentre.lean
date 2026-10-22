import OddMath

/-! # Consumers of the finiteness of `H_n` over its centre -/

noncomputable section
open CategoryTheory OddMath.QuiverHecke

/-- The odd rank-one datum (one colour): `H_3` is finite over its centre. -/
example : ∃ G : Finset (Hn Examples.datum Examples.scalars 3), ∀ x, ∃ c : _ → _,
    (∀ g, c g ∈ Set.center (Hn Examples.datum Examples.scalars 3)) ∧ x = ∑ g ∈ G, c g * g :=
  exists_centre_finite_of_finite _ _

/-- Mixed parities over infinitely many colours: the block of the words with letters `0, 1`
is finite over the centre. -/
example (W : Finset (Word ℕ 2)) (hW : IsBlock W) :
    ∃ G : Finset (Hn AlgebraExamples.datum AlgebraExamples.scalars 2), ∀ x,
      (∀ a b, x (a, b) ≠ 0 → a ∈ W ∧ b ∈ W) → ∃ c : _ → _,
        (∀ g, c g ∈ Set.center (Hn AlgebraExamples.datum AlgebraExamples.scalars 2)) ∧
          x = ∑ g ∈ G, c g * g :=
  exists_centre_finite _ _ W hW

/-- The symmetric functions of the squared dots commute with every morphism of `H`. -/
example (t t' : List ℕ) (f : (pres AlgebraExamples.datum AlgebraExamples.scalars).obj
      (ob AlgebraExamples.datum t) ⟶ (pres AlgebraExamples.datum AlgebraExamples.scalars).obj
      (ob AlgebraExamples.datum t'))
    (q : MvPolynomial (ℕ × ℕ) ℚ) :
    (zeta _ _ t q : _ ⟶ _) ≫ f = f ≫ zeta _ _ t' q :=
  zeta_comp _ _ f q

#print axioms OddMath.QuiverHecke.exists_centre_finite
#print axioms OddMath.QuiverHecke.exists_centre_finite_of_finite
#print axioms OddMath.QuiverHecke.zeta_comp
