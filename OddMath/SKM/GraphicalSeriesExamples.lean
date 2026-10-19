/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.GraphicalSeries
import OddMath.SKM.PositiveLabelledCoefficientsExamples

/-! # Populated graphical-series coefficients for BE2 Theorem 10.3

A cap in either orientation and the two repeated-colour positive matchings.
The latter use the independently serialized, reversed two-dot order. All family
and serialization hypotheses are discharged before either sign is specialized.
-/
noncomputable section
namespace OddMath.SKM.GraphicalSeriesExamples
open StringDiagrams StringDiagrams.Chord CoveringQuantum
open GraphicalSeries
open PositiveDecoratedFamilyCoefficientsExamples (oddDatum)
open scoped BigOperators LaurentSeries

namespace Cap

def boundary (ε : Bool) : List (Letter Unit) := [(ε, ()), (!ε, ())]
def representative : List (TMove (Letter Unit)) := [.cap 0]
def family : Set (List (TMove (Letter Unit))) := {representative}
def points (_ : family) (_ : ℕ) : ℕ × ℕ := (0, 1)

theorem matching (ε : Bool) : IsMatching₂ (boundary ε) [] representative := by
  cases ε <;>
    exact ⟨⟨⟨(2, _), (0, _), rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩

theorem family_matching (ε : Bool) : ∀ R ∈ family, IsMatching₂ (boundary ε) [] R := by
  intro R hR
  obtain rfl := Set.mem_singleton_iff.mp hR
  exact matching ε

theorem family_unique (ε : Bool) : ∀ R ∈ family, ∀ S ∈ family,
    Iso (pairing₂ (boundary ε) R) (pairing₂ (boundary ε) S) → R = S := by
  intro R hR S hS _
  exact (Set.mem_singleton_iff.mp hR).trans (Set.mem_singleton_iff.mp hS).symm

theorem ends (ε : Bool) : leftEnds₂ (boundary ε) representative = [0] := by
  have h (j : ℕ) : IsLeftEnd (pairing₂ (boundary ε) representative) j ↔ j = 0 := by
    constructor
    · intro hj
      have hb := hj.1
      change j < 2 at hb
      interval_cases j
      · rfl
      · apply False.elim
        apply hj.2
        refine ⟨0, by decide, ?_⟩
        cases ε <;> unfold Same idAt <;> decide
    · rintro rfl
      exact ⟨by cases ε <;> decide, by simp⟩
  unfold leftEnds₂
  simp only [show (pairing₂ (boundary ε) representative).length = 2 from rfl, h]
  decide

theorem points_valid (ε : Bool) (R : family) (j : ℕ)
    (hj : j ∈ leftEnds₂ (boundary ε) R.val) :
    OnStrand₂ (boundary ε) R.val j (points R j) := by
  have he := Set.mem_singleton_iff.mp R.property
  rw [he, ends] at hj
  obtain rfl := List.mem_singleton.mp hj
  rw [he]
  cases ε <;> unfold OnStrand₂ points <;> decide

def serializer (ε : Bool) (R : family) (c : MatchingStrand (boundary ε) R.val → ℕ) :
    List (DTMove Unit) :=
  (exists_decorates₂_of_bounded_points (boundary ε) R.val (points R)
    (points_valid ε R) (fun _ _ => Nat.zero_le _) c).choose

theorem serializer_valid (ε : Bool) (R : family)
    (c : MatchingStrand (boundary ε) R.val → ℕ) :
    Decorates₂ (boundary ε) R.val (points R) (strandCounts c) (serializer ε R c) :=
  (exists_decorates₂_of_bounded_points (boundary ε) R.val (points R)
    (points_valid ε R) (fun _ _ => Nat.zero_le _) c).choose_spec.1

abbrev Index (ε : Bool) := Σ R : family, MatchingStrand (boundary ε) R.val → ℕ
def oneDot (ε : Bool) : Index ε := ⟨⟨representative, Set.mem_singleton _⟩, fun _ => 1⟩

theorem oneDot_degree (ε : Bool) :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (dLay (boundary ε) (serializer ε (oneDot ε).1 (oneDot ε).2)) = 3 := by
  classical
  let j₀ : MatchingStrand (boundary ε) representative := ⟨0, by rw [ends]; simp⟩
  have hj (j : MatchingStrand (boundary ε) representative) : j = j₀ := by
    apply Subtype.ext
    have h := j.property
    simpa only [ends, List.mem_singleton] using h
  have hs (f : MatchingStrand (boundary ε) representative → ℤ) : ∑ j, f j = f j₀ := by
    apply Finset.sum_eq_single j₀
    · intro j _ hne
      exact (hne (hj j)).elim
    · simp
  have hd := (mixed_decorated_degree_parity oddDatum.toSKM oddDatum.skmSymmetrizer 0
    (matching ε) (points (oneDot ε).1) (points_valid ε (oneDot ε).1)
    (oneDot ε).2 _ (serializer_valid ε (oneDot ε).1 (oneDot ε).2)).1
  change _ = tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
    (tLay (boundary ε) representative) + ∑ j : MatchingStrand (boundary ε) representative,
      (1 : ℤ) * (2 * oddDatum.skmSymmetrizer.d
        (matchingStrandColour (boundary ε) representative j)) at hd
  rw [hs] at hd
  cases ε <;> exact hd

def fibre (ε : Bool) : Finset (Index ε) :=
  (mixed_labelled_degree_finite oddDatum.toSKM oddDatum.skmSymmetrizer 0
    (boundary ε) [] family (family_matching ε) (family_unique ε) points (points_valid ε)
    (serializer ε) (serializer_valid ε) 3).toFinset

theorem populated (ε : Bool) : oneDot ε ∈ fibre ε := by
  simpa only [fibre, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using oneDot_degree ε

/-- A nonzero-dot cap fibre, for each orientation and both signs. -/
theorem both_signs (ε : Bool) :
    (signLaurent 1 (by norm_num) (expression oddDatum 0 (boundary ε) [] family
      (family_matching ε) (family_unique ε))).coeff 3 =
      ∑ t ∈ fibre ε, (1 : ℚ) ^ (xpar oddDatum.toSKM 0
        (dLay (boundary ε) (serializer ε t.1 t.2))).val ∧
    (signLaurent (-1) (by norm_num) (expression oddDatum 0 (boundary ε) [] family
      (family_matching ε) (family_unique ε))).coeff 3 =
      ∑ t ∈ fibre ε, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0
        (dLay (boundary ε) (serializer ε t.1 t.2))).val := by
  constructor <;> exact expression_coeff oddDatum 0 (boundary ε) [] family
    (family_matching ε) (family_unique ε) points (points_valid ε)
    (serializer ε) (serializer_valid ε) _ (by norm_num) 3

end Cap

namespace TwoStrands
open PositiveDecoratedFamilyCoefficientsExamples
open PositiveLabelledCoefficientsExamples (Index points points_valid serializer serializer_valid)

def twoDots : Index := ⟨⟨[], by simp⟩, fun _ => 1⟩

theorem twoDots_degree : tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
    (dLay repeatedWord (serializer twoDots.1 twoDots.2)) = 4 := by
  rw [show serializer twoDots.1 twoDots.2 = [.dt 0, .dt 1] from
    PositiveLabelledCoefficientsExamples.noncanonical_order.1]
  rfl

def fibre : Finset Index :=
  (mixed_labelled_degree_finite oddDatum.toSKM oddDatum.skmSymmetrizer 0
    repeatedWord repeatedWord repeatedFamily (fun R hR => (family_matching R hR).1)
    family_unique points points_valid serializer serializer_valid 4).toFinset

theorem populated : twoDots ∈ fibre := by
  simpa only [fibre, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using twoDots_degree

/-- Both representatives, with reversed unit-dot order and both signs. -/
theorem both_signs :
    (signLaurent 1 (by norm_num) (expression oddDatum 0 repeatedWord repeatedWord repeatedFamily
      (fun R hR => (family_matching R hR).1) family_unique)).coeff 4 =
      ∑ t ∈ fibre, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 (dLay repeatedWord (serializer t.1 t.2))).val ∧
    (signLaurent (-1) (by norm_num) (expression oddDatum 0 repeatedWord repeatedWord
      repeatedFamily
      (fun R hR => (family_matching R hR).1) family_unique)).coeff 4 =
      ∑ t ∈ fibre, (-1 : ℚ) ^
        (xpar oddDatum.toSKM 0 (dLay repeatedWord (serializer t.1 t.2))).val := by
  constructor <;> exact expression_coeff oddDatum 0 repeatedWord repeatedWord repeatedFamily
    (fun R hR => (family_matching R hR).1) family_unique points points_valid
    serializer serializer_valid _ (by norm_num) 4

end TwoStrands
end OddMath.SKM.GraphicalSeriesExamples
