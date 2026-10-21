import OddMath

/-! Non-vacuity checks in `NonVacuity.LabelledPositive`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.LabelledPositive
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveLabelledCoefficientsExamples
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open scoped BigOperators

example :
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain repeatedWord (L t) repeatedWord),
      (∀ t, (L t).map ofL = dLay repeatedWord (serializer t.1 t.2)) ∧
      ∃ hf : Set.Finite {t : Index |
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
          (mkD oddDatum.toSKM 0 (L t) (hL t)) = -2},
        (∑ t ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (serializer t.1 t.2))).val) = 1 ∧
        (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (serializer t.1 t.2))).val) = -1 := repeated_signs

example :
    let R : {R // R ∈ repeatedFamily} := ⟨[], by simp⟩
    serializer R (fun _ => 1) = [.dt 0, .dt 1] ∧
      topDotMoves repeatedWord R.val (fun j => position R.val j.val) (fun _ => 1) =
        [.dt 1, .dt 0] := noncanonical_order

end NonVacuity.LabelledPositive
