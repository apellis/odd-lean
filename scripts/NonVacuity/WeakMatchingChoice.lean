import OddMath.SKM.WeakMatchingChoice
import OddMath.SKM.WeakMateMatchings
import OddMath.SKM.MixedCrossingLocalExamples

/-! Finite coefficient transition on an actual nonempty odd boundary, and
literal mixed cup/cap inverse mates with a bijective dot count map. -/
noncomputable section
namespace NonVacuity.WeakMatchingChoice
open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord OddMath.SKM
open MixedCrossingLocalExamples

private abbrev D₂ := oddDatum
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
private def F : MatchingBasisChoice A [] :=
  Classical.choice (MatchingBasisChoice.nonempty A [])


theorem finite_transition_surjective :
    Function.Surjective (F.toWeak.transition cs (0 : Bool → ℤ)) :=
  F.toWeak.transition_surjective cs 0

theorem finite_transition_evaluates (v : F.Labels →₀ SYM D₂ ℚ) :
    F.expansion cs 0 (F.toWeak.transition cs 0 v) = F.toWeak.expansion cs 0 v :=
  F.toWeak.transition_evaluation cs 0 v

private def u : Letter Unit := (true, ())
private theorem hm : IsMatching₂ (ups [()] ++ [u]) ([u] ++ [u]) [] := ⟨trivial, rfl⟩
private theorem hr : Reduced₂ (ups [()] ++ [u]) [] := by
  change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
  simp

theorem cup_and_cap_reduced :
    Reduced₂ ([u] ++ dualW [u]) (WeakMate.matching [()] [u] [u] []) :=
  WeakMate.reduced hm hr

theorem cup_and_cap_all_dot_counts (n : MatchingStrand (ups [()] ++ [u]) [] → ℕ) :
    ∑ j, WeakMate.dotsEquiv hm n j = ∑ j, n j := WeakMate.dotsEquiv_sum hm n

#print axioms finite_transition_surjective
#print axioms finite_transition_evaluates
#print axioms cup_and_cap_reduced
#print axioms cup_and_cap_all_dot_counts
#print axioms OddMath.SKM.WeakMatchingChoice.strict_expansion_injective
end NonVacuity.WeakMatchingChoice
