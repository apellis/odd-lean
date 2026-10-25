import OddMath.SKM.DistinctContextualCrossing
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.DistinctContextualCrossing
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

theorem actual_contextual_inverse :
    contextualSigma (D := D₂) (Sc := sc) 0 L Q false true ≫ contextualLCross 0 L Q false true = 𝟙 _ :=
  contextualSigma_lcross 0 L Q false true (by decide)

/-- Inhomogeneous full coefficients acquire the exact parity involution on
source sorting; both surrounding contexts are nonempty. -/
theorem contextual_full_coefficient
    (f : (pres D₂ sc).obj (ob D₂ 0 B) ⟶ (pres D₂ sc).obj (ob D₂ 0 A)) :
    distinctSourceExchange 0 L Q A false true (by decide)
      (bubAt D₂ sc 0 B (betaSYM cs 0 p) ≫ f) =
    bubAt D₂ sc 0 A (betaSYM cs 0 (SYM.parityTwist D₂ ℚ 1 p)) ≫
      distinctSourceExchange 0 L Q A false true (by decide) f :=
  distinctSourceExchange_coefficient cs 0 L Q A false true (by decide) f p

#print axioms distinctTargetExchange
#print axioms distinctSourceExchange_coefficient
#print axioms actual_contextual_inverse
#print axioms contextual_full_coefficient
end NonVacuity.DistinctContextualCrossing
