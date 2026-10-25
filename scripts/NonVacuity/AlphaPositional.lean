import OddMath.QuiverHecke.AlphaPositional
import OddMath.SKM.BottomMatchingChoice
import OddMath.SKM.MixedCrossingLocalExamples

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.SKM
open OddMath.SKM.MixedCrossingLocalExamples

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def bubbles : CScalars params where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [params]

private def gs : List PG := [.dot 0, .cross 0, .dot 1]
private theorem chain : OddMath.QuiverHecke.SChain [false, true]
    (pl [false, true] gs) [true, false] := by
  simp [gs, pl, PG.ld, PG.act, OddMath.QuiverHecke.SChain,
    OddMath.QuiverHecke.Shape.dom, OddMath.QuiverHecke.Shape.cod]

/-- The actual two-odd dot/cross/dot word has exactly its decorated-matching
evaluation, with no assumed diagram independence or scalar correction. -/
example : (alpha oddDatum params (0 : Bool → ℤ)).map
    (OddMath.QuiverHecke.cl oddDatum params [false, true] [true, false] gs chain) =
    xev bubbles 0 (upWord [false, true]) (upWord [true, false])
      (dLay (upWord [false, true]) (gs.map PG.toDTMove)) := by
  apply alpha_cl_eq_xev
  simp [gs, PG.pos, PG.width]

#print axioms alpha_cl_eq_xev
#print axioms alpha_nf_eq_xev
#print axioms MatchingBasisChoice.atBottomSorted
#print axioms MatchingBasisChoice.bottomPositions_injective
