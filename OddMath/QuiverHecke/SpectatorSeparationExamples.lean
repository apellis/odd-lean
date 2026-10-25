import OddMath.QuiverHecke.SpectatorSeparation
import OddMath.SKM.MixedCrossingLocalExamples

/-! # Separation with a nonempty spectator and two exterior coefficients -/
noncomputable section
namespace OddMath.QuiverHecke.SpectatorSeparationExamples
open CategoryTheory StringDiagrams OddMath.SKM
open scoped Classical
open OddMath.SKM.MixedCrossingLocalExamples

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def i : {i : Bool // oddDatum.parity i = 1} := ⟨false, rfl⟩
private def j : {i : Bool // oddDatum.parity i = 1} := ⟨true, rfl⟩

private def identityIndex : NFIdx [false, false, true] [false, false, true] := by
  have hc : Categorification.TypeA.canWord 3 1 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  exact ⟨([], 1), by simp, by simp, by simp [hc, cw]⟩

private def idx : SYM.CoefficientIndex oddDatum × NFIdx [false, false, true] [false, false, true] :=
  ((0, {i, j}), identityIndex)

/-- Odd cutoffs detect a concrete exterior-product vector with one spectator.
This is algebraic quotient separation, not a bubble-value assertion. -/
example : ∃ m : ℕ,
    (ELVRelationSpan oddDatum params (fun _ => 2 * m + 1)
      ([false] ++ [false, true]) ([false] ++ [false, true])).mkQ
      (extensionBasis oddDatum params [false, false, true] [false, false, true] idx) ≠ 0 := by
  by_contra h
  push Not at h
  apply (extensionBasis oddDatum params [false, false, true] [false, false, true]).ne_zero idx
  exact cofinal_elv_quotients_with_spectators_detect oddDatum params
    (fun m _ => 2 * m + 1) (fun N => ⟨N, by intro; omega⟩)
    [false] [false, true] [false, true] _ h

/-- At three total strands, cutoff six is already too small for the estimate. -/
example : ¬ (0 + 2 * Nat.choose 3 2 < 6) :=
  spectator_crossing_bound_obstruction (by decide) (by decide)

end OddMath.QuiverHecke.SpectatorSeparationExamples

#print axioms OddMath.QuiverHecke.cofinal_elv_quotients_with_spectators_detect
#print axioms OddMath.QuiverHecke.spectator_quotientImage_ne_zero
#print axioms OddMath.QuiverHecke.spectator_images_detect_of_bounds
#print axioms OddMath.QuiverHecke.spectator_crossing_bound_obstruction
