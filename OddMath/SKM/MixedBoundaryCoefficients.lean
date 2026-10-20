/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.EmptyBoundaryCoefficients
import OddMath.SKM.Claim2Coefficients

/-! # Arbitrary second boundaries in BE2 Theorem 10.3

Induction on the physical second boundary composes Claims 2 and 3 with the
empty-boundary theorem. No reversal of mixed words is used.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove

private theorem dotPts_height_le {I : Type*} (ds : List (DTMove I)) :
    ∀ p ∈ dotPts ds, p.1 ≤ (tmoves ds).length := by
  induction ds with
  | nil => simp [dotPts]
  | cons d ds ih =>
    cases d with
    | tm m =>
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa only [tmoves, List.length_cons] using Nat.succ_le_succ (ih q hq)
    | dt j =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Nat.zero_le _
      · exact ih p hp

private structure BoundaryFamily {I : Type*} (a b : List (Letter I)) where
  members : Set (List (TMove (Letter I)))
  matching : ∀ R ∈ members, IsMatching₂ a b R ∧ StrictReduced₂ a R
  unique : ∀ R ∈ members, ∀ S ∈ members, Iso (pairing₂ a R) (pairing₂ a S) → R = S
  complete : ∀ R, IsMatching₂ a b R → StrictReduced₂ a R →
    ∃ S ∈ members, Iso (pairing₂ a S) (pairing₂ a R)
  points : members → ℕ → ℕ × ℕ
  onStrand : ∀ R j, j ∈ leftEnds₂ a R.val → OnStrand₂ a R.val j (points R j)
  serialize : ∀ R : members, (MatchingStrand a R.val → ℕ) → List (DTMove I)
  decorates : ∀ R c, Decorates₂ a R.val (points R) (strandCounts c) (serialize R c)

private theorem BoundaryFamily.exists {I : Type*} (a b : List (Letter I)) :
    Nonempty (BoundaryFamily a b) := by
  classical
  obtain ⟨M, hM, hu, hc⟩ := exists_unique_matching_representatives a b
  have hp (R : M) := matching_bounded_points (hM R R.property).1
  choose q hq using hp
  have hd (R : M) (c : MatchingStrand a R.val → ℕ) :=
    exists_decorates₂_of_bounded_points a R.val (q R)
      (fun j hj => (hq R j hj).2) (fun j hj => (hq R j hj).1) c
  choose τ hτ using hd
  exact ⟨⟨M, hM, hu, hc, q, fun R j hj => (hq R j hj).2,
    τ, fun R c => (hτ R c).1⟩⟩

private theorem BoundaryFamily.height {I : Type*} {a b : List (Letter I)}
    (F : BoundaryFamily a b) (R : F.members) (j : ℕ) (hj : j ∈ leftEnds₂ a R.val) :
    (F.points R j).1 ≤ R.val.length := by
  classical
  let c : MatchingStrand a R.val → ℕ := fun _ => 1
  have h := F.decorates R c
  have hp : F.points R j ∈ dotPts (F.serialize R c) := by
    apply h.2.mem_iff.mpr
    apply List.mem_flatMap.mpr
    exact ⟨j, hj, by simp [strandCounts, hj, c]⟩
  have hb := dotPts_height_le (F.serialize R c) _ hp
  rwa [h.1] at hb

open CoveringQuantum CoveringQuantum.Coefficients
open CoveringQuantum.UDot.GenericTensor CoveringQuantum.UDot.GenericVerma.MixedGram
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]

private def BoundaryFamily.coeff {a b : List (Letter I)} (F : BoundaryFamily a b)
    (D : RootDatum I X) (μ : X) (σ : ℚ) (z : ℤ) : ℚ :=
  ∑ t ∈ (mixed_labelled_degree_finite D.toSKM D.skmSymmetrizer μ a b F.members
    (fun R hR => (F.matching R hR).1) F.unique F.points F.onStrand
    F.serialize F.decorates z).toFinset,
    σ ^ (xpar D.toSKM μ (dLay a (F.serialize t.1 t.2))).val

private def BoundaryFamily.Correct {a b : List (Letter I)} (F : BoundaryFamily a b)
    (D : RootDatum I X) (μ : X) : Prop :=
  ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
    (signLaurent σ hσ (sesquilinearForm D
      (algebraWord D μ a) (algebraWord D μ b))).coeff z = F.coeff D μ σ z

private theorem BoundaryFamily.correct (D : RootDatum I X)
    (μ : X)
    (a b : List (Letter I)) (F : BoundaryFamily a b) : F.Correct D μ := by
  induction b generalizing a with
  | nil =>
    let G : CoefficientFamily a :=
      ⟨F.members, F.matching, F.unique, F.points, F.onStrand, F.serialize, F.decorates⟩
    exact fun σ hσ z => empty_boundary_labelled_form_coeff a G F.complete D μ σ hσ z
  | cons l b ih =>
    rcases l with ⟨ε, i⟩
    cases ε with
    | false =>
      obtain ⟨G⟩ := BoundaryFamily.exists ((true, i) :: a) b
      obtain ⟨E, hE⟩ := rightCup_labelled_form_coeff_iff (X := X)
        G.matching F.matching G.points F.points
        (fun R j hj => ⟨G.height R j hj, G.onStrand R j hj⟩)
        F.onStrand G.serialize F.serialize G.decorates F.decorates
        G.complete F.complete G.unique F.unique
      obtain ⟨hf, hg, _, _, hs⟩ := hE D μ
      intro σ hσ
      exact (hs σ hσ).mp (ih _ G σ hσ)
    | true =>
      obtain ⟨G⟩ := BoundaryFamily.exists ((false, i) :: a) b
      obtain ⟨E, hE⟩ := leftCup_labelled_form_coeff_iff (X := X)
        G.matching F.matching G.points F.points
        (fun R j hj => ⟨G.height R j hj, G.onStrand R j hj⟩)
        F.onStrand G.serialize F.serialize G.decorates F.decorates
        G.complete F.complete G.unique F.unique
      obtain ⟨hf, hg, _, _, hs⟩ := hE D μ
      intro σ hσ
      exact (hs σ hσ).mp (ih _ G σ hσ)

/-- Arbitrary-boundary coefficient comparison in BE2 Theorem 10.3.
Auxiliary families and height bounds are derived internally. Colours are
arbitrary and bar consistency is not required; covering coefficients are unchanged. -/
theorem mixed_boundary_labelled_form_coeff (D : RootDatum I X)
    (μ : X)
    (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R ∧ StrictReduced₂ a R)
    (hrep : ∀ R, IsMatching₂ a b R → StrictReduced₂ a R →
      ∃ S ∈ M, Iso (pairing₂ a S) (pairing₂ a R))
    (huniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S)
    (q : M → ℕ → ℕ × ℕ)
    (hq : ∀ R j, j ∈ leftEnds₂ a R.val → OnStrand₂ a R.val j (q R j))
    (τ : ∀ R : M, (MatchingStrand a R.val → ℕ) → List (DTMove I))
    (hτ : ∀ R c, Decorates₂ a R.val (q R) (strandCounts c) (τ R c))
    (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm D
      (algebraWord D μ a) (algebraWord D μ b))).coeff z =
      ∑ t ∈ (mixed_labelled_degree_finite D.toSKM D.skmSymmetrizer μ a b M
        (fun R hR => (hM R hR).1) huniq q hq τ hτ z).toFinset,
        σ ^ (xpar D.toSKM μ (dLay a (τ t.1 t.2))).val := by
  exact BoundaryFamily.correct D μ a b
    ⟨M, hM, huniq, hrep, q, hq, τ, hτ⟩ σ hσ z

end OddMath.SKM
