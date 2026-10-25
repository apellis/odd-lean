import OddMath.SKM.ResidualCoefficientLift
import OddMath.SKM.MixedCrossingLocalExamples

noncomputable section
namespace NonVacuity.ResidualCoefficientLift
open CategoryTheory StringDiagrams StringDiagrams.Chord OddMath.SKM MatchingBasisChoice Presentation
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
private def F : MatchingBasisChoice a a := Classical.choice (MatchingBasisChoice.nonempty a a)
private theorem hm : IsMatching₂ a a [] := ⟨trivial, rfl⟩
private theorem hr : StrictReduced₂ a [] :=
  ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
private def rep : F.members :=
  ⟨(F.complete [] hm hr).choose, (F.complete [] hm hr).choose_spec.1⟩
private def label : F.Labels := ⟨rep, fun _ => 0⟩
private def p : SYM D ℚ := SYM.delta D ℚ ⟨false, rfl⟩ * SYM.delta D ℚ ⟨true, rfl⟩
private def q (n : ℤ) : End ((pres D Sc).obj (ob D 0 a)) :=
  if n < 0 then 0 else if n = 0 then 𝟙 _ else bubAt D Sc 0 a (betaSYM cs 0 p)
private theorem qneg (n : ℤ) (hn : n < 0) : q n = 0 := by simp [q, hn]
private theorem qzero : q 0 = 𝟙 _ := by simp [q]

-- A populated one-strand family keeps the full mixed exterior coefficient.
example : F.residualCoefficientColumn cs 0
    (fun n t => xev cs 0 a a (F.layers t) ≫ q n) 0 label 1 p =
      Finsupp.single label (SYM.parityTwist D ℚ 1 p) :=
  F.residualCoefficientColumn_zero cs 0 _ label 1 p

example : F.residualUnitColumn cs 0
    (fun n t => xev cs 0 a a (F.layers t) ≫ q n) (-1) label = 0 :=
  F.residualUnitColumn_neg cs 0 _ (-1) (by decide) label

example : F.expansion cs 0 (F.residualCoefficientColumn cs 0
    (fun n t => xev cs 0 a a (F.layers t) ≫ q n) 1 label 1 p) =
      rightAction cs 0 (xev cs 0 a a (F.layers label) ≫ q 1)
        (SYM.parityTwist D ℚ 1 p) :=
  F.residualPostColumn_eval cs 0 q qneg qzero 1 label 1 p

example : F.expansion cs 0 (F.residualCoefficientColumn cs 0
    (fun n t => q n ≫ xev cs 0 a a (F.layers t)) 1 label 1 p) =
      rightAction cs 0 (q 1 ≫ xev cs 0 a a (F.layers label))
        (SYM.parityTwist D ℚ 1 p) :=
  F.residualPreColumn_eval cs 0 q qneg qzero 1 label 1 p

private def capSource : List (Letter Bool) := [up true, dn true] ++ a
private def capLayers (n : ℕ) : List (XLayer Bool) :=
  ((epsL true n).map (whL [] a)).map ofL
private def caps (n : ℕ) :
    (pres D Sc).obj (ob D 0 capSource) ⟶ (pres D Sc).obj (ob D 0 a) :=
  xev cs 0 capSource a (capLayers n)

example (n : ℕ) : XChain capSource (capLayers n) a := by
  exact XChain.of_sChain ((sChain_epsL true n).wh [] a rfl rfl)

-- The source-side residual twist is tested on an actual one-dot cap in a
-- nonempty context, with two distinct exterior coefficients kept symbolic.
example : F.preRowsExpansion cs 0 caps (MatchingTransition.rightColumn (k := ℚ)
    (F.residualRow 1 (labelParityTwist (fun _ => xpar D 0 (capLayers 1))
      (Finsupp.single label (SYM.delta D ℚ ⟨false, rfl⟩))))
      (SYM.parityTwist D ℚ 1 (SYM.delta D ℚ ⟨true, rfl⟩))) =
    rightAction cs 0
      (caps 1 ≫ F.expansion cs 0 (Finsupp.single label (SYM.delta D ℚ ⟨false, rfl⟩)))
      (SYM.parityTwist D ℚ 1 (SYM.delta D ℚ ⟨true, rfl⟩)) := by
  apply F.preRowsExpansion_twistedColumn
  exact xev_mem_homPar cs 0 capSource a (capLayers 1)

example : F.residualRow (D := D) (k := ℚ) 2 (Finsupp.single label p) (label, 1) = 0 :=
  F.residualRow_apply_ne 2 1 (by decide) _ label

#print axioms MatchingBasisChoice.residualUnitColumn_eval
#print axioms MatchingBasisChoice.residualCoefficientColumn_eval
#print axioms MatchingBasisChoice.residualPostColumn_eval
#print axioms MatchingBasisChoice.residualPreColumn_eval
#print axioms MatchingBasisChoice.residualRow_apply_ne
#print axioms MatchingBasisChoice.postRowsExpansion_residualRow
#print axioms MatchingBasisChoice.preRowsExpansion_residualRow
#print axioms MatchingBasisChoice.preRowsExpansion_twistedColumn
end NonVacuity.ResidualCoefficientLift
