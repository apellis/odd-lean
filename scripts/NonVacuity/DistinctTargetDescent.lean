import OddMath.SKM.DistinctTargetDescent
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.DistinctTargetDescent
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

private def L : List (Letter Bool) := [up false]
private def Q : List (Letter Bool) := [dn true]
private def A : List (Letter Bool) := L ++ up true :: dn false :: Q
private def B : List (Letter Bool) := L ++ dn false :: up true :: Q

/-- The actual complete adapted choices exist with nonempty contexts and two
odd colours, with every construction hypothesis discharged. -/
example : ∃ (F : MatchingBasisChoice A A) (G : MatchingBasisChoice A B)
    (e : F.Labels ≃ G.Labels), ∀ t,
    G.layers (e t) = F.layers t ++ (xCrL (up true) (dn false)).map (xwhL L Q) ∨
    F.layers t = G.layers (e t) ++ (xCrL (dn false) (up true)).map (xwhL L Q) := by
  have h := exists_adapted_distinct_colour_choices A L Q (up true) (dn false) (by decide)
  simpa only [A, B, List.append_assoc, List.cons_append, List.nil_append] using h

/-- The complete native descent specializes to the same concrete boundaries. -/
example (h : BoundaryIndependence cs 0 A B) : BoundaryIndependence cs 0 A A := by
  have h' := distinct_target_exchange_descent cs 0 A L Q true false (by decide)
  simpa only [A, B, List.append_assoc, List.cons_append, List.nil_append] using h' h

#print axioms OddMath.SKM.distinct_target_exchange_descent
end NonVacuity.DistinctTargetDescent
