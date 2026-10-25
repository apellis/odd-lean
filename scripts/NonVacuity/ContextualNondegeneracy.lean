import OddMath.SKM.ContextualNondegeneracy
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.ContextualNondegeneracy
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

/-- Concrete two-odd-color instance; all three still-open local/base premises
remain visible rather than being hidden in a new nondegeneracy axiom. -/
theorem conditional_assembly
    (hsorted : ∀ μ l r u v, BoundaryIndependence cs μ (ups u ++ dns r) (dns l ++ ups v))
    (hsource : SourceExchangeDescent cs) (htarget : TargetExchangeDescent cs) :
    NondegeneracyConjecture cs :=
  nondegeneracy_of_contextual_descent cs hsorted hsource htarget

example : wt D₂ 0 ([up true] ++ dn false :: up true :: [dn true]) =
    wt D₂ 0 ([up true] ++ up true :: dn false :: [dn true]) :=
  wt_context_opposite_swap 0 [up true] [dn true] false true

example : wt D₂ 0 ([up true] ++ dn false :: up false :: [dn true]) =
    wt D₂ 0 ([up true] ++ [dn true]) :=
  wt_context_pair_delete 0 [up true] [dn true] false

#print axioms nondegeneracy_of_contextual_descent
#print axioms conditional_assembly
end NonVacuity.ContextualNondegeneracy
