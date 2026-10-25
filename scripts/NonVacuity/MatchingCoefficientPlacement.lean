import OddMath.SKM.MatchingCoefficientPlacement
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.MatchingCoefficientPlacement
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

private def word : List (Letter Bool) := [up false, up true]
private def F : MatchingBasisChoice word word := Classical.choice (MatchingBasisChoice.nonempty word word)

theorem actual_choice_placement_iff :
    Function.Injective (F.expansion cs 0) ↔ Function.Injective (F.targetExpansion cs 0) :=
  F.expansion_injective_iff_target cs 0

/-- The diagonal change acts on an inhomogeneous coefficient containing both
odd and even exterior degree, and is involutive without quotient assumptions. -/
theorem full_coefficient_twice :
    labelParityTwist (D := D₂) (k := ℚ) (fun _ : Bool => 1)
      (labelParityTwist (fun _ : Bool => 1) (Finsupp.single true p)) = Finsupp.single true p :=
  labelParityTwist_involutive _ _

#print axioms source_target_expansion_injective_iff
#print axioms MatchingBasisChoice.expansion_injective_iff_target
#print axioms actual_choice_placement_iff
#print axioms full_coefficient_twice
end NonVacuity.MatchingCoefficientPlacement
