import OddMath.SKM.UpwardWordTransport
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.UpwardWordTransport
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

/-- Three actual upward strands, including repeated odd color, with a mixed
left context and an inhomogeneous full coefficient. -/
theorem repeated_word_slide :
    ∃ z : PositiveWordDots ([dn true] ++ [] ++ ups [false, true, false]) →₀ SYM D₂ ℚ,
      plcL D₂ sc 0 [dn true] (ups [false, true, false]) [] []
        (betaSYM cs (wt D₂ 0 (ups [false, true, false])) p) =
      bubAt D₂ sc 0 ([dn true] ++ [] ++ ups [false, true, false]) (betaSYM cs 0 p) +
        positiveWordExpansion cs 0 ([dn true] ++ [] ++ ups [false, true, false]) z :=
  betaSYM_exists_positiveWordExpansion cs 0 [false, true, false] [dn true] p

#print axioms betaSYM_upward_word_difference
#print axioms betaSYM_exists_positiveWordExpansion
#print axioms repeated_word_slide
end NonVacuity.UpwardWordTransport
