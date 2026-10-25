import OddMath.SKM.UpwardTopDots
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.UpwardTopDots
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

/-- Exact top-dot reordering for two distinct odd strands. -/
theorem swap_top_dots :
    ∃ p : ZMod 2,
      xev cs 0 [up false, up true] [up false, up true]
        ([] ++ dotsOn [up false, up true] [0, 1] ++ []) =
      zsign ℚ p • xev cs 0 [up false, up true] [up false, up true]
        ([] ++ dotsOn [up false, up true] [1, 0] ++ []) :=
  top_dots_perm_eq cs (List.Perm.swap 1 0 []) (by simp) 0 [] [] (by simp)

private def correction : PositiveWordDots [up false, up true] :=
  ⟨[([], Shape.dot false, [up true])], by simp [Shape.dom, Shape.cod],
    by intro x hx; simp only [List.mem_singleton] at hx; subst x; exact ⟨[], false, [up true], rfl⟩,
    by simp⟩

example : ∃ js : List ℕ,
    [] ++ dotsOn [up false, up true] [1, 1] ++ correction.val.map ofL =
      [] ++ dotsOn [up false, up true] js ∧
    [1, 1].length < js.length ∧ ∀ j ∈ js, j ∈ [1, 1] ∨ j < [up false, up true].length :=
  positiveWordDots_append_top correction [] [1, 1]

#print axioms top_dots_perm_eq
#print axioms positiveWordDots_append_top
#print axioms swap_top_dots
end NonVacuity.UpwardTopDots
