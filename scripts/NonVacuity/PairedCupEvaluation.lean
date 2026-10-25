import OddMath.SKM.PairedCupEvaluation
import OddMath.SKM.MixedCrossingLocalExamples
noncomputable section
namespace NonVacuity.PairedCupEvaluation
open CategoryTheory StringDiagrams StringDiagrams.Chord OddMath.SKM Presentation
private abbrev D := MixedCrossingLocalExamples.oddDatum
private def Sc : Scalars D ℚ where
  t := fun _ _ => 1
  t_self := by intros; rfl
  t_symm_of_d_eq_zero := by intros; rfl
  s := fun _ _ _ _ => 0
  s_symm := by intros; rfl
  s_eq_zero := by intros; rfl
  two_isUnit := by intro _; exact isUnit_iff_ne_zero.mpr (by norm_num)
private def cs : CScalars Sc where
  c := fun _ _ => 1
  shift := by intros; simp [Sc]
private def a : List (Letter Bool) := [up false]
private theorem hm : IsMatching₂ a a [] := ⟨trivial, rfl⟩
private theorem hr : StrictReduced₂ a [] :=
  ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
private def F : PointedMatching a ([] ++ a) := PointedMatching.ofStrict hm hr

-- Nonempty residual strand, two colours, positive residual and isolated dot counts.
example : xev cs 0 a (up true :: dn true :: a)
    ((F.appendCup true true).layers
      ((terminalCupCountsEquiv F.matching true true).symm (2, fun _ => 1))) =
  xev cs 0 a a (F.layers (fun _ => 1)) ≫
    plcW 0 a (up true :: dn true :: a) [] a [] [up true, dn true]
      (etaP cs true (wt D 0 a) ≫ cpow (uLM D Sc true (wt D 0 a)) 2) :=
  F.appendCup_up_eval cs 0 true 2 (fun _ => 1)

example : xev cs 0 a (dn true :: up true :: a)
    ((F.appendCup false true).layers
      ((terminalCupCountsEquiv F.matching false true).symm (3, fun _ => 2))) =
  xev cs 0 a a (F.layers (fun _ => 2)) ≫
    plcW 0 a (dn true :: up true :: a) [] a [] [dn true, up true]
      (hLM D Sc true (wt D 0 a) 3) :=
  F.appendCup_dn_eval cs 0 true 3 (fun _ => 2)
#print axioms PointedMatching.appendCup_up_eval
#print axioms PointedMatching.appendCup_dn_eval
end NonVacuity.PairedCupEvaluation
