import OddMath.SKM.ClosureCoefficientExpansion
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.ClosureCoefficientExpansion
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

/-- Both adjunction sides are nonempty. The upward diagram is a mixed-color
crossing and its coefficient includes a product of two odd generators. -/
theorem crossing_mate_full_coefficient :
    ∃ z : PositiveWordDots ([up true] ++ [] ++ ups [false]) →₀ SYM D₂ ℚ,
      rightClosure D₂ sc 0 [false] [false] [up true] [up true]
        (cl D₂ sc (wt D₂ 0 (ups [false])) ([up true] ++ dns [false])
          (dns [false] ++ [up true])
          (partialRightMateL [false] [false] [up true] [up true] (crossL [] false true [])) ≫
          bubAt D₂ sc (wt D₂ 0 (ups [false])) (dns [false] ++ [up true])
            (betaSYM cs (wt D₂ 0 (ups [false])) p)) =
      cl D₂ sc 0 (ups [false] ++ [up true]) ([up true] ++ ups [false]) (crossL [] false true []) ≫
        bubAt D₂ sc 0 ([up true] ++ ups [false]) (betaSYM cs 0 p) +
      cl D₂ sc 0 (ups [false] ++ [up true]) ([up true] ++ ups [false]) (crossL [] false true []) ≫
        wordCast 0 (by simp) (by simp)
          (positiveWordExpansion cs 0 ([up true] ++ [] ++ ups [false]) z) :=
  rightClosure_partialMate_betaSYM_expansion cs 0 [false] [false] [up true] [up true]
    (by simp [ups, crossL, Shape.dom, Shape.cod]) p

#print axioms rightClosure_bubAt
#print axioms rightClosure_partialMate_betaSYM_expansion
#print axioms crossing_mate_full_coefficient
end NonVacuity.ClosureCoefficientExpansion
