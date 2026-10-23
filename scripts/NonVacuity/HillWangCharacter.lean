import OddMath

/-! Non-vacuity of the Hill–Wang character comparison (Lemma 6.11), for a datum that is not
bar-consistent: a single odd simple root with symmetrizer two. -/

noncomputable section

namespace NonVacuity.HillWangCharacter

open OddMath.CoveringQuantum

/-- A single odd simple root with symmetrizer two. -/
def datum : SuperCartanDatum Unit where
  a := Matrix.of fun _ _ ↦ 2
  isGCM :=
    { diag := fun _ ↦ rfl
      offDiag_nonpos := fun i j h ↦ absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ ↦ Iff.rfl }
  d := fun _ ↦ 2
  d_pos := fun _ ↦ two_pos
  d_mul_symm := fun _ _ ↦ rfl
  parity := fun _ ↦ 1
  even_of_odd := fun _ _ _ ↦ even_two

theorem not_barConsistent : ¬ datum.BarConsistent := fun h ↦ by
  have h0 := h ()
  simp [datum] at h0

private def q : (RatFunc ℚ)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero

private theorem transcendental_q : Transcendental ℚ (q : RatFunc ℚ) := by
  have hi : (RatFunc.instAlgebraOfPolynomial ℚ ℚ : Algebra ℚ (RatFunc ℚ)) =
      (DivisionRing.toRatAlgebra : Algebra ℚ (RatFunc ℚ)) := Subsingleton.elim _ _
  exact (congrArg (fun a : Algebra ℚ (RatFunc ℚ) ↦
    @Transcendental ℚ (RatFunc ℚ) _ _ a RatFunc.X) hi).mp
      (RatFunc.transcendental_X (K := ℚ))

example (ν : Unit →₀ ℕ) :
    Module.finrank (RatFunc ℚ) (datum.serreWeightSpace q 1 ν) =
      Module.finrank (RatFunc ℚ) (datum.serreWeightSpace q (-1) ν) :=
  datum.finrank_serreWeightSpace_one_eq_neg_one transcendental_q ν

example (ν : Unit →₀ ℕ) : FiniteDimensional (RatFunc ℚ)
    (datum.serreWeightSpace q (-1) ν) := inferInstance

example : datum.serreIdeal q (-1) = PreF.radical (datum.chi q (-1)) (datum.norm q (-1)) :=
  datum.serreIdeal_neg_one_eq_radical_of_transcendental transcendental_q

#print axioms SuperCartanDatum.finrank_serreWeightSpace_one_eq_neg_one
#print axioms SuperCartanDatum.serreIdeal_neg_one_eq_radical_of_transcendental
#print axioms SuperCartanDatum.finrank_productSpan_neg_one
#print axioms SuperCartanDatum.finrank_serreWeightSpace_twist
#print axioms SuperCartanDatum.finrank_serreWeightSpace_baseChange
#print axioms SuperCartanDatum.finrank_serreWeightSpace_one_eq

end NonVacuity.HillWangCharacter
