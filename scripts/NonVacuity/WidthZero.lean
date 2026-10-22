import OddMath

/-! # BE2 Theorem 11.7, surjectivity, width zero, on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`, with the normalizing
units and homogeneous scalars proved there.
-/

noncomputable section
namespace NonVacuity.WidthZero
open CategoryTheory StringDiagrams OddMath OddMath.SKM
open OddMath.SKM.LaurentianK0Examples OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.DimensionFormulaExamples

/-- `End(1_0)` is spanned by bubbles. -/
example := endOne_mem_bubbleSpan cScalars 0

/-- Its degree-zero part is `ℚ · 1`. -/
example := homDeg_endOne_zero cScalars twoOddDatum.skmSymmetrizer homogeneous 0
  (Presentation.id_mem_homDeg _ _ _)

/-- `Q Π 1_0` is indecomposable or zero. -/
example := isIndec_or_isZero_one (sy := twoOddDatum.skmSymmetrizer) (hc := homogeneous)
  cScalars 0 rfl 1 1

/-- Indecomposable retracts of `Q Π 1_0` are isomorphic to it; here the retract is itself. -/
example (Z : K0Relations.weight scalars twoOddDatum.skmSymmetrizer homogeneous 0 ⟶
      K0Relations.weight scalars twoOddDatum.skmSymmetrizer homogeneous 0)
    (hZ : KrullSchmidt.IsIndec Z)
    (ι : Z ⟶ K0Relations.completed scalars twoOddDatum.skmSymmetrizer homogeneous 0 0 [] rfl 1 1)
    (π : K0Relations.completed scalars twoOddDatum.skmSymmetrizer homogeneous 0 0 [] rfl 1 1 ⟶ Z)
    (h : ι ≫ π = 𝟙 Z) :=
  iso_of_retract_one cScalars 0 rfl 1 1 hZ ι π h

#print axioms OddMath.SKM.endOne_mem_bubbleSpan
#print axioms OddMath.SKM.homDeg_endOne_zero
#print axioms OddMath.SKM.iso_of_retract_one

end NonVacuity.WidthZero
