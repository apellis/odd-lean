import OddMath.SKM.RightClosureCoefficients
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.RightClosureCoefficients
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

/-- This includes both a single exterior generator and an ordered product of
two different exterior generators in the same coefficient. -/
theorem inhomogeneous_coefficient :
    cupPrefixMap D₂ sc 0 [false] [up true] [up true, up false]
      (bubAt D₂ sc 0 (ups [false] ++ [up true]) (betaSYM cs 0 p) ≫
        cl D₂ sc 0 (ups [false] ++ [up true]) [up true, up false] (crossL [] false true [])) =
    bubAt D₂ sc 0 [up true] (betaSYM cs 0 p) ≫
      cupPrefixMap D₂ sc 0 [false] [up true] [up true, up false]
        (cl D₂ sc 0 (ups [false] ++ [up true]) [up true, up false] (crossL [] false true [])) :=
  cupPrefixMap_bubAt 0 [false] [up true] [up true, up false] _ _

theorem crossing_recovered :
    capPrefixMap D₂ sc 0 [false] [up true] [up true, up false]
      (cupPrefixMap D₂ sc 0 [false] [up true] [up true, up false]
        (cl D₂ sc 0 (ups [false] ++ [up true]) [up true, up false] (crossL [] false true []))) =
    cl D₂ sc 0 (ups [false] ++ [up true]) [up true, up false] (crossL [] false true []) :=
  capPrefixMap_cupPrefixMap 0 [false] [up true] [up true, up false] _

example : Function.Injective (cupPrefixMap D₂ sc 0 [false] [up true] [up true, up false]) :=
  cupPrefixMap_injective 0 [false] [up true] [up true, up false]

#print axioms cupPrefixMap_bubAt
#print axioms cupPrefixMap_injective
#print axioms inhomogeneous_coefficient
end NonVacuity.RightClosureCoefficients
