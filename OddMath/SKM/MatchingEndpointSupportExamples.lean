/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.MatchingEndpointSupport
import OddMath.SKM.PositiveFormCoefficientsExamples

/-! # Endpoint-support examples for BE2 Theorem 10.3 Claims 2–3 -/

noncomputable section
namespace OddMath.SKM.MatchingEndpointSupportExamples
open OddMath OddMath.SKM OddMath.CoveringQuantum
open UDot GenericTensor GenericVerma.MixedGram
open PositiveDecoratedFamilyCoefficientsExamples PositiveFormCoefficientsExamples
open StringDiagrams StringDiagrams.Chord

/-- Both test words contain upward and downward odd letters. -/
def a : List (Letter Unit) := [(true, ()), (false, ())]
def b : List (Letter Unit) := [(true, ()), (true, ()), (false, ())]

theorem endpoints_differ : wt oddDatum.toSKM 0 a ≠ wt oddDatum.toSKM 0 b := by
  norm_num [a, b, wt, sh, RootDatum.toSKM_α, oddDatum, RootDatum.α]

theorem no_matching (R : List (TMove (Letter Unit))) : ¬ IsMatching₂ a b R :=
  not_isMatching₂_of_weight_ne oddDatum.toSKM 0 endpoints_differ R

theorem form_zero :
    sesquilinearForm oddDatum (algebraWord oddDatum 0 a)
      (algebraWord oddDatum 0 b) = 0 :=
  sesquilinearForm_mixed_eq_zero_of_weight_ne oddDatum 0 a b endpoints_differ

/-- A signed identity is an inhabited matching, not a mismatch-only test. -/
theorem signed_identity : IsMatching₂ a a [] := ⟨trivial, rfl⟩

theorem signed_identity_conservation : wt oddDatum.toSKM 7 a = wt oddDatum.toSKM 7 a :=
  signed_identity.wt_eq oddDatum.toSKM 7

/-- A cup changes the boundary but preserves its endpoint. -/
theorem cup_matching : IsMatching₂ [] a [.mv (.cup 0 (true, ()))] := by
  constructor
  · change 0 ≤ 0 ∧ True
    decide
  · rfl

theorem cup_conservation : wt oddDatum.toSKM 7 [] = wt oddDatum.toSKM 7 a :=
  cup_matching.wt_eq oddDatum.toSKM 7

/-- The actual finite strand-labelled index, with its degree fibre and parity sum. -/
theorem labelled_fibre_zero
    (M : Set (List (TMove (Letter Unit)))) (hM : ∀ R ∈ M, IsMatching₂ a b R)
    (degree : (Σ R : {R // R ∈ M}, MatchingStrand a R.val → ℕ) → ℤ)
    (parity : (Σ R : {R // R ∈ M}, MatchingStrand a R.val → ℕ) → ZMod 2)
    (z : ℤ) (hf : {t | degree t = z}.Finite) (σ : ℤ) :
    ∑ t ∈ hf.toFinset, σ ^ (parity t).val = 0 :=
  matching_labelled_finite_sum_eq_zero_of_weight_ne oddDatum.toSKM 0 M hM endpoints_differ
    hf.toFinset (fun t => σ ^ (parity t).val)

theorem up_mismatch :
    sesquilinearForm oddDatum (algebraWord oddDatum 0 ((true, ()) :: a))
      (algebraWord oddDatum 0 a) = 0 ∧
    sesquilinearForm oddDatum (algebraWord oddDatum 0 a)
      (algebraWord oddDatum 0 ((false, ()) :: a)) = 0 := by
  apply sesquilinearForm_mixed_up_leftCons_mismatch
  norm_num [a, wt, sh, RootDatum.toSKM_α, oddDatum, RootDatum.α]

theorem down_mismatch :
    sesquilinearForm oddDatum (algebraWord oddDatum 0 ((false, ()) :: a))
      (algebraWord oddDatum 0 a) = 0 ∧
    sesquilinearForm oddDatum (algebraWord oddDatum 0 a)
      (algebraWord oddDatum 0 ((true, ()) :: a)) = 0 := by
  apply sesquilinearForm_mixed_down_leftCons_mismatch
  norm_num [a, wt, sh, RootDatum.toSKM_α, oddDatum, RootDatum.α]

end OddMath.SKM.MatchingEndpointSupportExamples
