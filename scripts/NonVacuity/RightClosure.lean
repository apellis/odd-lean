import OddMath.SKM.RightClosure
import OddMath.SKM.MixedCrossingLocalExamples

/-! Literal right-closure calculations on a concrete two-color odd datum.
These are equalities in the SKM quotient, not independence assertions. -/

noncomputable section
namespace NonVacuity.RightClosure
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

theorem distinct_odd_crossing :
    cl D₂ sc 0 [up false, up true] [up true, up false]
      (rightClosureL [false] [false] [up true] [up true] (sigmaL false true)) =
    cl D₂ sc 0 [up false, up true] [up true, up false] (crossL [] false true []) :=
  cl_rightClosure_sigma sc 0 false true

theorem equal_odd_crossing :
    cl D₂ sc 0 [up false, up false] [up false, up false]
      (rightClosureL [false] [false] [up false] [up false] (sigmaL false false)) =
    cl D₂ sc 0 [up false, up false] [up false, up false] (crossL [] false false []) :=
  cl_rightClosure_sigma sc 0 false false

theorem paired_odd_decorations :
    cl D₂ sc 0 [up false, up false] [up false, up false]
      (rightClosureL [false] [false] [up false] [up false]
        (pairedRightL false (dotsL [] false [] 3) (dotsL [] false [] 1))) =
    cl D₂ sc 0 [up false, up false] [up false, up false]
      ((dotsL [] false [] 3).map (whL [up false] []) ++
        (dotsL [] false [] 1).map (whL [] [up false])) :=
  cl_rightClosure_pair sc 0 false
    (sChain_dotsL [] false [] 3) (sChain_dotsL [] false [] 1)

theorem two_downward_odd_dots :
    cl D₂ sc 0 [up false] [up false]
      (rightClosureL [] [false] [up false] []
        ((ddotsL false 2).map (whL [up false] []) ++ [([], Shape.cap false, [])])) =
    -cl D₂ sc 0 [up false] [up false] (dotsL [] false [] 2) := by
  simpa [MixedCrossingLocalExamples.oddDatum, zsign] using
    cl_rightClosure_downward_cap sc 0 false 2

/-- Two nested caps and two nested cups, with odd decorations in different
positions of the two-colored blocks. -/
theorem nested_paired_decorations :
    cl D₂ sc 0 (ups [false, true] ++ ups [true, false])
      (ups [false, true] ++ ups [true, false])
      (rightClosureL [false, true] [true, false] (ups [true, false]) (ups [false, true])
        (pairedRightBlocksL [false, true] [true, false]
          (dotsL [] true [up false] 3) (dotsL [up false] true [] 1))) =
    cl D₂ sc 0 (ups [false, true] ++ ups [true, false])
      (ups [false, true] ++ ups [true, false])
      ((dotsL [] true [up false] 3).map (whL (ups [false, true]) []) ++
        (dotsL [up false] true [] 1).map (whL [] (ups [true, false]))) :=
  cl_rightClosure_pairBlocks sc 0 [false, true] [true, false]
    (sChain_dotsL [] true [up false] 3) (sChain_dotsL [up false] true [] 1)

/-- Unequal-size closing blocks and a dotted upward diagram. -/
theorem partial_mate_recovered :
    cl D₂ sc 0 (ups [false, true] ++ [up false]) ([up false, up true] ++ ups [false])
      (rightClosureL [false, true] [false] [up false] [up false, up true]
        (partialRightMateL [false, true] [false] [up false] [up false, up true]
          (dotsL [up false, up true] false [] 2))) =
    cl D₂ sc 0 (ups [false, true] ++ [up false]) ([up false, up true] ++ ups [false])
      (dotsL [up false, up true] false [] 2) :=
  cl_rightClosure_partialMate sc 0 [false, true] [false] [up false] [up false, up true]
    (sChain_dotsL [up false, up true] false [] 2)

-- A nonzero local region is retained when the rightmost strand is closed.
example : rightClosure D₂ sc 0 [false] [false] [up true] [up true]
      (cl D₂ sc (wt D₂ 0 (ups [false])) ([up true] ++ dns [false])
        (dns [false] ++ [up true]) (sigmaL false true)) =
    cl D₂ sc 0 (ups [false] ++ [up true]) ([up true] ++ ups [false])
      (rightClosureL [false] [false] [up true] [up true] (sigmaL false true)) :=
  rightClosure_cl 0 [false] [false] [up true] [up true] (sigmaL false true)

example : SChain [up false, up true]
    (rightClosureL [false] [false] [up true] [up true] (sigmaL false true))
    [up true, up false] :=
  sChain_rightClosureL [false] [false] [up true] [up true] (sChain_sigmaL false true)

#print axioms cl_rightClosure_sigma
#print axioms cl_rightClosure_pair
#print axioms cl_rightClosure_pairBlocks
#print axioms cl_rightClosure_partialMate
#print axioms cl_rightClosure_downward_cap
#print axioms two_downward_odd_dots
end NonVacuity.RightClosure
