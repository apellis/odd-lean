import OddMath

/-! Non-vacuity checks in `NonVacuity.NormalizedDownAdjoint`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.NormalizedDownAdjoint
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositivePointGradingExamples

example : tableDegree twoColourDatum twoColourSymmetrizer 0 (tLay [(false, false)] []) =
    tableDegree twoColourDatum twoColourSymmetrizer 0
      (tLay [(false, false)] [.mv (.cup 0 (false, false)), .cap 1]) ∧
    xpar twoColourDatum 0 (tLay [(false, false)] []) =
      xpar twoColourDatum 0 (tLay [(false, false)] [.mv (.cup 0 (false, false)), .cap 1]) :=
  TwoSidedGradingExamples.odd_cap_zigzag_normalization

open OddMath.CoveringQuantum UDot UDot.GenericTensor
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.CoveringQuantum.UDot.DownAdjointExamples

example : (signLaurent 1 (by norm_num) downPairing).coeff 1 = 1 ∧
    (signLaurent (-1) (by norm_num) downPairing).coeff 1 = 1 :=
  repeated_odd_down_both_signs

example :
    (signLaurent 1 (by norm_num) (sesquilinearForm oddDatum
      (GenericVerma.MixedGram.algebraWord oddDatum 0
        [(false, ()), (true, ()), (true, ())])
      (GenericVerma.MixedGram.algebraWord oddDatum 0 [(true, ())]))).coeff 1 = 1 ∧
    (signLaurent (-1) (by norm_num) (sesquilinearForm oddDatum
      (GenericVerma.MixedGram.algebraWord oddDatum 0
        [(false, ()), (true, ()), (true, ())])
      (GenericVerma.MixedGram.algebraWord oddDatum 0 [(true, ())]))).coeff 1 = 1 :=
  ⟨repeated_odd_physical_down_coeff 1 (by norm_num),
    repeated_odd_physical_down_coeff (-1) (by norm_num)⟩

end NonVacuity.NormalizedDownAdjoint
