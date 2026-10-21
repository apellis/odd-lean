import OddMath

/-! Non-vacuity of the bar-consistent Hill–Wang character comparison. -/

noncomputable section

namespace NonVacuity.HillWangCharacter

open OddMath.CoveringQuantum

/-- A single odd simple root with symmetrizer one. -/
def datum : SuperCartanDatum Unit where
  a := Matrix.of fun _ _ ↦ 2
  isGCM :=
    { diag := fun _ ↦ rfl
      offDiag_nonpos := fun i j h ↦ absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ ↦ Iff.rfl }
  d := fun _ ↦ 1
  d_pos := fun _ ↦ one_pos
  d_mul_symm := fun _ _ ↦ rfl
  parity := fun _ ↦ 1
  even_of_odd := fun _ _ _ ↦ even_two

private theorem barConsistent : datum.BarConsistent := fun _ ↦ Nat.cast_one

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
  datum.finrank_serreWeightSpace_one_eq_neg_one q barConsistent transcendental_q ν

example (ν : Unit →₀ ℕ) : FiniteDimensional (RatFunc ℚ)
    (datum.serreWeightSpace q (-1) ν) := inferInstance

#print axioms SuperCartanDatum.finrank_serreWeightSpace_one_eq_neg_one
#print axioms SuperCartanDatum.finrank_serreWeightSpace_twist
#print axioms SuperCartanDatum.finrank_serreWeightSpace_baseChange
#print axioms SuperCartanDatum.finrank_serreWeightSpace_one_eq

end NonVacuity.HillWangCharacter
