import OddMath

/-! Non-vacuity checks in `NonVacuity.MixedFamilyCoefficients`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.MixedFamilyCoefficients
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples (oddDatum)
open OddMath.SKM.PositiveFormCoefficientsExamples (odd_barConsistent)
open OddMath.CoveringQuantum UDot GenericTensor GenericVerma.MixedGram
open scoped BigOperators

example : Set.Finite {t : MixedFibresExamples.Index |
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (dLay [] (MixedFibresExamples.serializer t.1 t.2)) = 3} ∧
    MixedFibresExamples.oneDot ∈ {t : MixedFibresExamples.Index |
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
        (dLay [] (MixedFibresExamples.serializer t.1 t.2)) = 3} :=
  MixedFibresExamples.cup_degree_three

example : ∃ (L : MixedFibresExamples.Index → List (LayerData Unit))
    (hL : ∀ t, SChain [] (L t) MixedFibresExamples.B),
    (∀ t, Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
      (mkD oddDatum.toSKM 0 (L t) (hL t)) =
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
        (dLay [] (MixedFibresExamples.serializer t.1 t.2))) ∧
    ∀ z : ℤ, Set.Finite {t : MixedFibresExamples.Index |
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (L t) (hL t)) = z} :=
  MixedFibresExamples.cup_ordinary_fibres

example : ∃ (U : Type) (d : U → ℤ) (p : U → ZMod 2)
    (h : Set.Finite {u | d u = 2}),
    (∑ u ∈ h.toFinset, (1 : ℚ) ^ (p u).val) = 1 ∧
    (∑ u ∈ h.toFinset, (-1 : ℚ) ^ (p u).val) = -1 := by
  classical
  obtain ⟨⟨hp, hpv⟩, ⟨hn, hnv⟩⟩ := CupFamilyCoefficientsExamples.odd_one_dot_signs
  exact ⟨_, _, _, hp, hpv, hnv⟩

example : ∃ (U : Type) (d : U → ℤ) (p : U → ZMod 2)
    (h : Set.Finite {u | d u = 4}),
    (∑ u ∈ h.toFinset, (1 : ℚ) ^ (p u).val) = 1 ∧
    (∑ u ∈ h.toFinset, (-1 : ℚ) ^ (p u).val) = 1 := by
  classical
  obtain ⟨⟨hp, hpv⟩, ⟨hn, hnv⟩⟩ := CupFamilyCoefficientsExamples.odd_two_dot_signs
  exact ⟨_, _, _, hp, hpv, hnv⟩

example :
    (signLaurent 1 (by norm_num) MixedUpAdjointExamples.mixedCupPairing).coeff 2 = 1 ∧
    (signLaurent (-1) (by norm_num) MixedUpAdjointExamples.mixedCupPairing).coeff 2 = -1 ∧
    (signLaurent 1 (by norm_num) MixedUpAdjointExamples.mixedCupPairing).coeff 2 ≠ 0 ∧
    (signLaurent (-1) (by norm_num) MixedUpAdjointExamples.mixedCupPairing).coeff 2 ≠ 0 :=
  MixedUpAdjointExamples.odd_mixed_up_both_signs

example : sesquilinearForm oddDatum
    (algebraWord oddDatum 0 [(true, ()), (false, ())])
    (algebraWord oddDatum 0 [(true, ()), (true, ()), (false, ())]) = 0 :=
  MatchingEndpointSupportExamples.form_zero

example (R : List (TMove (Letter Unit))) :
    ¬ IsMatching₂ [(true, ()), (false, ())] [(true, ()), (true, ()), (false, ())] R :=
  MatchingEndpointSupportExamples.no_matching R

example : wt oddDatum.toSKM 7 [] = wt oddDatum.toSKM 7 [(true, ()), (false, ())] :=
  MatchingEndpointSupportExamples.cup_conservation

end NonVacuity.MixedFamilyCoefficients
