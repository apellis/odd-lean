import OddMath.SKM.SameColourTargetFrame
import OddMath.SKM.PairedTargetDetection
import OddMath.SKM.MixedCrossingLocalExamples

/-! Concrete two-colour odd consumers of the actual paired target columns. -/
noncomputable section
namespace OddMath.SKM.SameColourTargetFrameExamples
open CategoryTheory StringDiagrams StringDiagrams.Chord Presentation
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
private abbrev P : List (Letter Bool) := [up false]
private abbrev Q : List (Letter Bool) := [dn true]
private abbrev a : List (Letter Bool) := P ++ Q
private def frame (m : ℤ) : SameColourTargetFrame cs (fun _ => m) a P Q false :=
  Classical.choice (sameColourTargetFrame_nonempty cs (fun _ => m) a P Q false)
private def label (m : ℤ) : (frame m).residual.Labels := by
  have hm : IsMatching₂ a a [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ a [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  let h := (frame m).residual.complete [] hm hr
  exact ⟨⟨h.choose, h.choose_spec.1⟩, fun _ => 1⟩
private theorem local_height (m : ℤ) : D.h false (wt D (fun _ => m) Q) = m := by
  simp [D, MixedCrossingLocalExamples.oddDatum, PositivePointGradingExamples.twoColourDatum,
    Datum.h, Datum.α, wt, sh]

/-- Nonempty residual family, nonempty contexts, positive local height, and
arbitrary abstract bubble coefficient. -/
theorem positive_column (d : SYM D ℚ) :
    (frame 2).swapped.expansion cs (fun _ => 2)
      ((frame 2).residual.pairedRowsInclusion false (frame 2).swapped (frame 2).swappedPaired
        (MatchingTransition.rightColumn (k := ℚ)
          ((frame 2).residual.targetPositiveColumn cs (fun _ => 2) false 2 5 (label 2)) d)) =
    (frame 2).original.expansion cs (fun _ => 2)
      (Finsupp.single ((frame 2).paired (5, label 2)) d) ≫
        sameColourTargetCross (Sc := Sc) (fun _ => 2) P Q false :=
  (frame 2).positive_column 2 5 (label 2) d (local_height 2) (by decide)

/-- Negative local height exercises both the shifted inverse block and the
dot-slide correction sum. -/
theorem negative_column (d : SYM D ℚ) :
    (frame (-2)).swapped.expansion cs (fun _ => -2)
      ((frame (-2)).residual.pairedRowsInclusion false (frame (-2)).swapped (frame (-2)).swappedPaired
        (MatchingTransition.rightColumn (k := ℚ)
          ((frame (-2)).residual.targetNonpositiveColumn cs (fun _ => -2) false 2 3 (label (-2))) d)) =
    (frame (-2)).original.expansion cs (fun _ => -2)
      (Finsupp.single ((frame (-2)).paired (3, label (-2))) d) ≫
        sameColourTargetCross (Sc := Sc) (fun _ => -2) P Q false :=
  (frame (-2)).nonpositive_column 2 3 (label (-2)) d (by rw [local_height]; norm_num)

#print axioms positive_column
#print axioms negative_column
#print axioms MatchingBasisChoice.targetPositiveColumns_detect
#print axioms MatchingBasisChoice.targetNonpositiveColumns_detect
end OddMath.SKM.SameColourTargetFrameExamples
