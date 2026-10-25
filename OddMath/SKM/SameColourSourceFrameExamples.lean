import OddMath.SKM.SameColourSourceDescent
import OddMath.SKM.MixedCrossingLocalExamples

/-! Two-odd-colour consumers of contextual source descent. -/
noncomputable section
namespace OddMath.SKM.SameColourSourceFrameExamples
open CategoryTheory StringDiagrams StringDiagrams.Chord Presentation
abbrev D := MixedCrossingLocalExamples.oddDatum

def Sc : Scalars D ℚ where
  t := fun _ _ => 1
  t_self := by intros; rfl
  t_symm_of_d_eq_zero := by intros; rfl
  s := fun _ _ _ _ => 0
  s_symm := by intros; rfl
  s_eq_zero := by intros; rfl
  two_isUnit := by intro _; exact isUnit_iff_ne_zero.mpr (by norm_num)

def cs : CScalars Sc where
  c := fun _ _ => 1
  shift := by intros; simp [Sc]

private abbrev P : List (Letter Bool) := [up false]
private abbrev Q : List (Letter Bool) := [dn true]
private abbrev Z : List (Letter Bool) := P ++ Q
private def frame : SameColourSourceFrame P Q Z false :=
  Classical.choice (sameColourSourceFrame_nonempty P Q Z false)
private def label : frame.residual.Labels := by
  have hm : IsMatching₂ Z Z [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ Z [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  let h := frame.residual.complete [] hm hr
  exact ⟨⟨h.choose, h.choose_spec.1⟩, fun _ => 1⟩

/-- The complete source exchange interface, with no independence premise. -/
theorem all_source_exchanges : SourceExchangeDescent cs := source_exchange_descent cs

/-- The actual finite source column admits unrestricted abstract coefficients;
contexts and the residual decorated label are both nonempty. -/
theorem actual_source_column (m : ℤ) (d : SYM D ℚ) :
    frame.swapped.expansion cs (fun _ => m) (frame.swappedPairedInclusion
      (MatchingTransition.rightColumn (k := ℚ)
        (frame.capResidualColumn 3 (Finsupp.single label 1))
        (SYM.parityTwist D ℚ 1 d))) =
      MatchingBasisChoice.rightAction cs (fun _ => m)
        (sourceCapRows (Sc := Sc) (fun _ => m) P Q false 3 ≫
          frame.residual.expansion cs (fun _ => m) (Finsupp.single label 1))
        (SYM.parityTwist D ℚ 1 d) :=
  frame.capResidualColumn_eval cs (fun _ => m) 3 (Finsupp.single label 1) 1 d

#print axioms all_source_exchanges
#print axioms actual_source_column
end OddMath.SKM.SameColourSourceFrameExamples
