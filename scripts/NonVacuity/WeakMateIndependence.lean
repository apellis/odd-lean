import OddMath.SKM.WeakMateIndependence
import OddMath.SKM.MixedCrossingLocalExamples

/-! A concrete conditional reduction at a fixed nonzero external weight.
Both bending blocks and both unbent words are nonempty. Upward independence
is explicitly the remaining hypothesis; this file does not claim to prove it.
-/
noncomputable section
namespace NonVacuity.WeakMateIndependence
open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord OddMath.SKM
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

private def ξ : Bool → ℤ := fun i => if i then 7 else 3
private def F : MatchingBasisChoice (ups [true] ++ dns [false])
    (dns [false] ++ ups [true]) := Classical.choice (MatchingBasisChoice.nonempty _ _)

/-- The native implication specializes to an actual odd, mixed-oriented boundary
and a prescribed external weight, without an additional closure-weight premise. -/
theorem fixed_weight_sorted_independence (h : WeakMate.UpwardIndependence cs) :
    Function.Injective (F.expansion cs ξ) :=
  WeakMate.sorted_independence cs h [false] [true] [true] [false] ξ F

theorem both_bending_blocks_nonempty :
    (ups [false] : List (Letter Bool)) ≠ [] ∧ (dns [false] : List (Letter Bool)) ≠ [] := by
  decide

#print axioms fixed_weight_sorted_independence
#print axioms WeakMate.sorted_independence
#print axioms WeakMate.strict_injective_of_top_data
#print axioms WeakMate.closure_decorated_coefficient
end NonVacuity.WeakMateIndependence
