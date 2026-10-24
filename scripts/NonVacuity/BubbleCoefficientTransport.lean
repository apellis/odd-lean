import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.OddBubbleCentrality
import OddMath.SKM.MixedCrossingLocalExamples

/-! The first odd elementary bubble has a nontrivial dot correction when slid.
This checks the actual SKM relation, not injectivity of a matching expansion. -/

noncomputable section
namespace NonVacuity.BubbleCoefficientTransport
open CategoryTheory StringDiagrams Presentation OddMath.SKM

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Degree two of the same-colour slide, with the normalization used by `betaDGen`. -/
theorem normalized_two (cs : CScalars Sc) (i : I) (μ : X) (hi : D.parity i = 1) :
    lbub i μ (betaDGen cs i (wt D μ [up i]) (some 0)) =
      rbub i μ (betaDGen cs i (wt D μ []) (some 0)) +
        (3 : k) • cl D Sc μ [up i] [up i] (dotsL [] i [] 2) := by
  have H := congrArg (fun f => (↑(cs.c μ i)⁻¹ : k) • f) (eq_7_10 cs i μ hi 2)
  simp only [betaDGen, Nat.cast_zero, zero_add, mul_one]
  rw [c_wt_up cs i μ]
  norm_num [lbub, rbub, dotsL, Finset.sum_range_succ,
    bubLs_zero, cl_nil, plcL_id, smul_smul, mul_left_comm, mul_assoc] at H ⊢
  erw [Category.comp_id] at H
  exact H

/-- The same equality on the actual first polynomial generator of full `SYM`. -/
theorem elementary_one (cs : CScalars Sc) (i : I) (μ : X) (hi : D.parity i = 1) :
    lbub i μ (betaSYM cs (wt D μ [up i]) (SYM.e D k i 0)) =
      rbub i μ (betaSYM cs (wt D μ []) (SYM.e D k i 0)) +
        (3 : k) • cl D Sc μ [up i] [up i] (dotsL [] i [] 2) := by
  simpa only [SYM.e, betaSYM_ι, betaSYMGen, hi, one_ne_zero, ite_false] using
    normalized_two cs i μ hi

private abbrev D₂ := MixedCrossingLocalExamples.oddDatum
private def sc : Scalars D₂ ℚ where
  t := fun _ _ => 1
  t_self := by intros; rfl
  t_symm_of_d_eq_zero := by intros; rfl
  s := fun _ _ _ _ => 0
  s_symm := by intros; rfl
  s_eq_zero := by intros; rfl
  two_isUnit := by intro _; exact isUnit_iff_ne_zero.mpr (by norm_num)

private def cs : CScalars sc where
  c := fun _ _ => 1
  shift := by intros; simp [sc]

/-- Concrete odd scalar data satisfy the bundled invertibility condition. -/
example :
    lbub false (0 : Bool → ℤ)
        (betaSYM cs (wt D₂ 0 [up false]) (SYM.e D₂ ℚ false 0)) =
      rbub false (0 : Bool → ℤ)
        (betaSYM cs (wt D₂ 0 []) (SYM.e D₂ ℚ false 0)) +
        (3 : ℚ) • cl D₂ sc 0 [up false] [up false] (dotsL [] false [] 2) :=
  elementary_one cs false 0 rfl

#print axioms normalized_two
#print axioms elementary_one
end NonVacuity.BubbleCoefficientTransport
