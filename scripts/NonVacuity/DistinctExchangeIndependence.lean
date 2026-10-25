import OddMath.SKM.DistinctExchangeIndependence
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.DistinctExchangeIndependence
open CategoryTheory StringDiagrams Presentation OddMath.SKM

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

private def p : SYM D₂ ℚ :=
  SYM.delta D₂ ℚ ⟨false, rfl⟩ +
    SYM.delta D₂ ℚ ⟨false, rfl⟩ * SYM.delta D₂ ℚ ⟨true, rfl⟩ + SYM.e D₂ ℚ false 0

private def L : List (Letter Bool) := [up false]
private def Q : List (Letter Bool) := [dn true]
private def A : List (Letter Bool) := L ++ [up true, dn false] ++ Q
private def B : List (Letter Bool) := L ++ [dn false, up true] ++ Q

/-- Two actual top dots survive the high-side crossing cancellation in a
nonempty context, with exact leading coefficient +1. -/
theorem decorated_high_cancellation :
    xev cs 0 B A (dotsOn B [0, 2] ++ (xCrL (dn false) (up true)).map (xwhL L Q)) ≫
      contextualSigma 0 L Q false true = xev cs 0 B B (dotsOn B [0, 2]) :=
  distinct_target_high_eval cs 0 false true (by decide)
    (xChain_dotsOn (by simp [B, L, Q]))

/-- The corresponding low-side formula includes its literal terminal crossing. -/
theorem decorated_low_insertion :
    xev cs 0 A A (dotsOn A [0, 1]) ≫ contextualSigma 0 L Q false true =
      xev cs 0 A B (dotsOn A [0, 1] ++ (xCrL (up true) (dn false)).map (xwhL L Q)) :=
  distinct_target_low_eval cs 0 false true (xChain_dotsOn (by simp [A, L, Q]))

theorem decorated_source_high :
    contextualSigma 0 L Q false true ≫
      xev cs 0 B A ((xCrL (dn false) (up true)).map (xwhL L Q) ++ dotsOn A [0, 1]) =
        xev cs 0 A A (dotsOn A [0, 1]) :=
  distinct_source_high_eval cs 0 L Q A false true (by decide) (dotsOn A [0, 1])

#print axioms distinct_source_high_eval
#print axioms distinct_target_adapted_independent
#print axioms distinct_source_adapted_independent
#print axioms decorated_high_cancellation
#print axioms decorated_low_insertion
end NonVacuity.DistinctExchangeIndependence
