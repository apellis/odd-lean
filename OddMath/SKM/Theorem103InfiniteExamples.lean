/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.Theorem103
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-! # BE2 Theorem 10.3 with infinitely many non-bar-consistent colours

The original modified algebra on the infinite, non-bar-consistent Nat datum.
Both head orientations, both rational signs, and arbitrary external weights.
The upward-head word has the nested same-colour cap pattern in its first
boundary. All representatives, points and serializers are constructed here.
-/
noncomputable section
namespace OddMath.SKM.Theorem103InfiniteExamples
open StringDiagrams StringDiagrams.Chord CoveringQuantum
open CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.UDot.GenericVerma.MixedGram
open CoveringQuantum.UDot.VermaWeightExamples
open scoped BigOperators

/-- The concrete colour set is infinite and the datum is not bar consistent. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- A mixed boundary in both orientations; the true case is a nested cap word. -/
def boundary (ε : Bool) : List (Letter ℕ) :=
  [(ε, 1), (true, 0), (false, 0), (!ε, 1)]

def family (ε : Bool) : Set (List (TMove (Letter ℕ))) :=
  (exists_unique_matching_representatives (boundary ε) (boundary ε)).choose

theorem family_matching (ε : Bool) : ∀ R ∈ family ε,
    IsMatching₂ (boundary ε) (boundary ε) R ∧ StrictReduced₂ (boundary ε) R :=
  (exists_unique_matching_representatives (boundary ε) (boundary ε)).choose_spec.1

theorem family_unique (ε : Bool) : ∀ R ∈ family ε, ∀ S ∈ family ε,
    Iso (pairing₂ (boundary ε) R) (pairing₂ (boundary ε) S) → R = S :=
  (exists_unique_matching_representatives (boundary ε) (boundary ε)).choose_spec.2.1

theorem family_complete (ε : Bool) : ∀ R, IsMatching₂ (boundary ε) (boundary ε) R →
    StrictReduced₂ (boundary ε) R →
    ∃ S ∈ family ε, Iso (pairing₂ (boundary ε) S) (pairing₂ (boundary ε) R) :=
  (exists_unique_matching_representatives (boundary ε) (boundary ε)).choose_spec.2.2

/-- The identity matching witnesses that neither mixed family is empty. -/
theorem family_nonempty (ε : Bool) : (family ε).Nonempty := by
  have hm : IsMatching₂ (boundary ε) (boundary ε) [] := ⟨trivial, rfl⟩
  obtain ⟨R, hR, hr, _⟩ := exists_strictReduced_equiv hm
  obtain ⟨S, hS, _⟩ := family_complete ε R hR hr
  exact ⟨S, hS⟩

def points (ε : Bool) (R : family ε) : ℕ → ℕ × ℕ :=
  (matching_bounded_points (family_matching ε R R.property).1).choose

theorem points_valid (ε : Bool) (R : family ε) (j : ℕ)
    (hj : j ∈ leftEnds₂ (boundary ε) R.val) :
    (points ε R j).1 ≤ R.val.length ∧ OnStrand₂ (boundary ε) R.val j (points ε R j) :=
  (matching_bounded_points (family_matching ε R R.property).1).choose_spec j hj

def serializer (ε : Bool) (R : family ε)
    (c : MatchingStrand (boundary ε) R.val → ℕ) : List (DTMove ℕ) :=
  (exists_decorates₂_of_bounded_points (boundary ε) R.val (points ε R)
    (fun j hj => (points_valid ε R j hj).2)
    (fun j hj => (points_valid ε R j hj).1) c).choose

theorem serializer_valid (ε : Bool) (R : family ε)
    (c : MatchingStrand (boundary ε) R.val → ℕ) :
    Decorates₂ (boundary ε) R.val (points ε R) (strandCounts c) (serializer ε R c) :=
  (exists_decorates₂_of_bounded_points (boundary ε) R.val (points ε R)
    (fun j hj => (points_valid ε R j hj).2)
    (fun j hj => (points_valid ε R j hj).1) c).choose_spec.1

abbrev Index (ε : Bool) := Σ R : family ε, MatchingStrand (boundary ε) R.val → ℕ

def labelled (ε : Bool) : Index ε :=
  ⟨⟨(family_nonempty ε).choose, (family_nonempty ε).choose_spec⟩, fun _ => 1⟩

def degree (ε : Bool) (μ : ℕ →₀ ℤ) : ℤ :=
  tableDegree datum.toSKM datum.skmSymmetrizer μ
    (dLay (boundary ε) (serializer ε (labelled ε).1 (labelled ε).2))

def fibre (ε : Bool) (μ : ℕ →₀ ℤ) (z : ℤ) : Finset (Index ε) :=
  (mixed_labelled_degree_finite datum.toSKM datum.skmSymmetrizer μ
    (boundary ε) (boundary ε) (family ε) (fun R hR => (family_matching ε R hR).1)
    (family_unique ε) (points ε) (fun R j hj => (points_valid ε R j hj).2)
    (serializer ε) (serializer_valid ε) z).toFinset

/-- An actual all-one-labelled matching belongs to the full finite degree fibre.
No inference of nonzero total coefficient is made from this member. -/
theorem populated (ε : Bool) (μ : ℕ →₀ ℤ) : labelled ε ∈ fibre ε μ (degree ε μ) := by
  simp only [fibre, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, degree]

theorem coefficient (ε : Bool) (μ : ℕ →₀ ℤ) (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm datum
      (algebraWord datum μ (boundary ε))
      (algebraWord datum μ (boundary ε)))).coeff z =
      ∑ t ∈ fibre ε μ z, σ ^
        (xpar datum.toSKM μ (dLay (boundary ε) (serializer ε t.1 t.2))).val :=
  mixed_boundary_labelled_form_coeff datum μ
    (boundary ε) (boundary ε) (family ε) (family_matching ε) (family_complete ε)
    (family_unique ε) (points ε) (fun R j hj => (points_valid ε R j hj).2)
    (serializer ε) (serializer_valid ε) σ hσ z

/-- Both transported signs at every degree and weight, in either orientation. -/
theorem both_signs (ε : Bool) (μ : ℕ →₀ ℤ) (z : ℤ) :
    (signLaurent 1 (by norm_num) (sesquilinearForm datum
      (algebraWord datum μ (boundary ε))
      (algebraWord datum μ (boundary ε)))).coeff z =
      ∑ t ∈ fibre ε μ z, (1 : ℚ) ^
        (xpar datum.toSKM μ (dLay (boundary ε) (serializer ε t.1 t.2))).val ∧
    (signLaurent (-1) (by norm_num) (sesquilinearForm datum
      (algebraWord datum μ (boundary ε))
      (algebraWord datum μ (boundary ε)))).coeff z =
      ∑ t ∈ fibre ε μ z, (-1 : ℚ) ^
        (xpar datum.toSKM μ (dLay (boundary ε) (serializer ε t.1 t.2))).val :=
  ⟨coefficient ε μ 1 (by norm_num) z, coefficient ε μ (-1) (by norm_num) z⟩

/-- The covering-ring identity with independently chosen source families and
arbitrary weights, not merely equality after one sign specialization. -/
theorem graphical (ε : Bool) (ζ μ : ℕ →₀ ℤ) :
    sesquilinearForm datum
      (algebraWord datum ζ (boundary ε)) (algebraWord datum μ (boundary ε)) =
      (if ζ = μ then 1 else 0) * GraphicalSeries.expression datum ζ
        (boundary ε) (boundary ε) (family ε)
        (fun R hR => (family_matching ε R hR).1) (family_unique ε) :=
  theorem103 datum ζ μ (boundary ε) (boundary ε)
    (family ε) (family_matching ε) (family_complete ε) (family_unique ε)

/-- The full covering-ring identity at a negative external weight, with a
populated mixed matching family and no assumed form comparison. -/
theorem negative_weight_graphical (ε : Bool) :
    sesquilinearForm datum
      (algebraWord datum (Finsupp.single 0 (-3)) (boundary ε))
      (algebraWord datum (Finsupp.single 0 (-3)) (boundary ε)) =
        GraphicalSeries.expression datum (Finsupp.single 0 (-3))
          (boundary ε) (boundary ε) (family ε)
          (fun R hR => (family_matching ε R hR).1) (family_unique ε) := by
  simpa only [ite_true, one_mul] using
    graphical ε (Finsupp.single 0 (-3)) (Finsupp.single 0 (-3))

/-- Distinct actual external weights; the zero is derived from form blocks. -/
theorem unequal_weight_zero (ε : Bool) :
    sesquilinearForm datum
      (algebraWord datum 0 (boundary ε))
      (algebraWord datum (Finsupp.single 0 1) (boundary ε)) = 0 := by
  have h : (0 : ℕ →₀ ℤ) ≠ (Finsupp.single 0 1) := by
    intro he
    have := congrArg (fun f : ℕ →₀ ℤ => f 0) he
    norm_num at this
  simpa only [ite_eq_right h, zero_mul] using graphical ε 0 (Finsupp.single 0 1)

end OddMath.SKM.Theorem103InfiniteExamples
