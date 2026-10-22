import OddMath

/-! # BE2 Theorem 11.7, surjectivity: sorting summands, on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`, where the scalar and
local-finiteness hypotheses are proved.
-/

noncomputable section
namespace NonVacuity.SortedSummands
open CategoryTheory StringDiagrams OddMath OddMath.SKM
open OddMath.SKM.LaurentianK0Examples OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.DimensionFormulaExamples

/-- The identity of `F_0 E_1 1_0` factors through sorted words. -/
example := thru_sorted (Sc := scalars) (sy := twoOddDatum.skmSymmetrizer) 0
  [dn false, up true]

/-- Sorting indecomposable summands, with every hypothesis on the datum proved. -/
example
    (Z : K0Relations.weight scalars twoOddDatum.skmSymmetrizer homogeneous
        (wt twoOddDatum.toSKM 0 [dn false, up true]) ⟶
      K0Relations.weight scalars twoOddDatum.skmSymmetrizer homogeneous 0)
    (hZ : KrullSchmidt.IsIndec Z)
    (ι : Z ⟶ K0Relations.completed scalars twoOddDatum.skmSymmetrizer homogeneous _ 0
      [dn false, up true] rfl 0 0)
    (π : K0Relations.completed scalars twoOddDatum.skmSymmetrizer homogeneous _ 0
      [dn false, up true] rfl 0 0 ⟶ Z)
    (h : ι ≫ π = 𝟙 Z) :=
  exists_retract_sorted cScalars homogeneous locallyFinite hZ ι π h

#print axioms OddMath.SKM.thru_sorted
#print axioms OddMath.SKM.exists_retract_sorted

end NonVacuity.SortedSummands
