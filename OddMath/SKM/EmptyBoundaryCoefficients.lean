/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.MatchingFamilyChoice
import OddMath.SKM.Claim3Coefficients
import OddMath.SKM.Claim4Coefficients
import OddMath.SKM.PositiveLabelledCoefficients
import OddMath.CoveringQuantum.UDot.PositiveAdjointCoefficients
import OddMath.CoveringQuantum.UDot.TensorGram.MixedIntegration

/-! # Empty-boundary coefficients for arbitrary signed words

The empty-boundary induction in the proof of BE2, arXiv:1701.04133v2,
Theorem 10.3. Strong length induction and subsidiary up-before-down inversion
induction compose Claims 1, 3, 4 and 5. Auxiliary families are chosen internally;
all-count serializers force the bounded heights needed by Claim 3.

The headline has no shorter-word induction premise or auxiliary-family-existence
assumption. Colours are arbitrary and bar consistency is not assumed. The
additive-weight and purely-even covering-coefficient conventions are unchanged.
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

/-- All-count valid decoration bounds the height of every distinguished point.
No height assumption is added to the supplied family. -/
theorem CoefficientFamily.points_height_le {I : Type*} {A : List (Letter I)}
    (F : CoefficientFamily A) (R : F.members) (j : ℕ) (hj : j ∈ leftEnds₂ A R.val) :
    (F.points R j).1 ≤ R.val.length := by
  classical
  let c : MatchingStrand A R.val → ℕ := fun _ => 1
  have h := F.decorates R c
  have hp : F.points R j ∈ dotPts (F.serialize R c) := by
    apply h.2.mem_iff.mpr
    apply List.mem_flatMap.mpr
    refine ⟨j, hj, ?_⟩
    simp [strandCounts, hj, c]
  have hb := dotPts_height_le (F.serialize R c) _ hp
  rwa [h.1] at hb

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

private def BoundaryFamily.ofCoefficient {I : Type*} {a : List (Letter I)}
    (F : CoefficientFamily a) (hF : F.Complete) : BoundaryFamily a [] :=
  ⟨F.members, F.matching, F.unique, hF, F.points, F.onStrand, F.serialize, F.decorates⟩

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

private theorem positive_comparison (D : RootDatum I X)
    (μ : X)
    {m n : ℕ} (a : Fin m → I) (b : Fin n → I)
    (F : BoundaryFamily (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r))) : F.Correct D μ := by
  classical
  obtain ⟨L, hL, hm, hc⟩ := positive_labelled_family_form_coeff D μ a b
    F.members F.matching F.complete F.unique F.points F.onStrand F.serialize F.decorates
  intro σ hσ z
  obtain ⟨hf, he⟩ := hc σ hσ z
  have hd (t) := tableDegree_diagram D.toSKM D.skmSymmetrizer μ (L t) (hL t)
  simp only [hm] at hd
  rw [sesquilinearForm_positive_reverse] at he
  have ha : algebraWord D μ (List.ofFn fun r => (true, a r)) =
      UDot.positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (PreF.monomial Coefficients.Ring (List.ofFn a))) := by
    rw [show (List.ofFn fun r => (true, a r)) =
      (List.ofFn a).map (fun i => (true, i)) by simp [Function.comp_def]]
    exact (UDot.PositiveComparison.algebraWord_pos_eq D μ _).trans
      (UDot.NormalizedMixedComparison.word_positive D _ μ)
  have hb : algebraWord D μ (List.ofFn fun r => (true, b r)) =
      UDot.positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (PreF.monomial Coefficients.Ring (List.ofFn b))) := by
    rw [show (List.ofFn fun r => (true, b r)) =
      (List.ofFn b).map (fun i => (true, i)) by simp [Function.comp_def]]
    exact (UDot.PositiveComparison.algebraWord_pos_eq D μ _).trans
      (UDot.NormalizedMixedComparison.word_positive D _ μ)
  rw [ha, hb, ← he]
  unfold BoundaryFamily.coeff
  congr 1
  ext t
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hd]

private theorem sorted_comparison (D : RootDatum I X)
    (μ : X)
    (d u v : List I)
    (F : BoundaryFamily (d.map (fun i => (false, i)) ++ u.map (fun i => (true, i)))
      (v.map (fun i => (true, i)))) : F.Correct D μ := by
  induction d generalizing v with
  | nil =>
    have h := positive_comparison D μ u.get v.get
    have hu : (List.ofFn fun r => (true, u.get r)) = u.map (fun i => (true, i)) := by
      rw [show (List.ofFn fun r => (true, u.get r)) =
        (List.ofFn u.get).map (fun i => (true, i)) by simp]
      rw [List.ofFn_get]
    have hv : (List.ofFn fun r => (true, v.get r)) = v.map (fun i => (true, i)) := by
      rw [show (List.ofFn fun r => (true, v.get r)) =
        (List.ofFn v.get).map (fun i => (true, i)) by simp]
      rw [List.ofFn_get]
    rw [hu, hv] at h
    exact h F
  | cons i d ih =>
    obtain ⟨G⟩ := BoundaryFamily.exists
      (d.map (fun j => (false, j)) ++ u.map (fun j => (true, j)))
      ((i :: v).map (fun j => (true, j)))
    obtain ⟨E, hE⟩ := leftCup_labelled_form_coeff_iff (X := X)
      F.matching G.matching F.points G.points
      (fun R j hj => ⟨F.height R j hj, F.onStrand R j hj⟩)
      G.onStrand F.serialize G.serialize F.decorates G.decorates
      F.complete G.complete F.unique G.unique
    obtain ⟨hf, hg, _, _, hs⟩ := hE D μ
    intro σ hσ
    exact (hs σ hσ).mpr (ih (i :: v) G σ hσ)

private def downCount (a : List (Letter I)) : ℕ :=
  (a.filter fun l => !l.1).length

private def inversions : List (Letter I) → ℕ
  | [] => 0
  | x :: a => inversions a + if x.1 then downCount a else 0

omit [DecidableEq I] in
private theorem inversions_swap (a b : List (Letter I)) (i j : I) :
    inversions (a ++ (true, i) :: (false, j) :: b) =
      inversions (a ++ (false, j) :: (true, i) :: b) + 1 := by
  induction a with
  | nil => simp [inversions, downCount]; omega
  | cons x a ih =>
    have hd : downCount (a ++ (true, i) :: (false, j) :: b) =
        downCount (a ++ (false, j) :: (true, i) :: b) := by
      simp [downCount, List.filter_append]
    simp only [List.cons_append, inversions, hd, ih]
    omega

omit [DecidableEq I] in
private theorem sorted_or_interchange (a : List (Letter I)) :
    (∃ d u : List I, a = d.map (fun i => (false, i)) ++ u.map (fun i => (true, i))) ∨
      ∃ p s : List (Letter I), ∃ i j : I, a = p ++ (true, i) :: (false, j) :: s := by
  induction a with
  | nil => exact Or.inl ⟨[], [], rfl⟩
  | cons x a ih =>
    rcases ih with ⟨d, u, rfl⟩ | ⟨p, s, i, j, rfl⟩
    · rcases x with ⟨ε, i⟩
      cases ε with
      | false => exact Or.inl ⟨i :: d, u, rfl⟩
      | true =>
        cases d with
        | nil => exact Or.inl ⟨[], i :: u, rfl⟩
        | cons j d => exact Or.inr ⟨[], _, i, j, rfl⟩
    · exact Or.inr ⟨x :: p, s, i, j, rfl⟩

/-- The empty-boundary coefficient identity in the proof of BE2 Theorem 10.3.
Every complete source-shaped family is allowed. Auxiliary representatives,
points and serializers are chosen internally, and the shorter-word comparison
is discharged by strong length induction. Colours are arbitrary; no bar
consistency is required. Additive weights and covering coefficients are unchanged. -/
theorem empty_boundary_labelled_form_coeff (a : List (Letter I))
    (F : CoefficientFamily a) (hF : F.Complete)
    (D : RootDatum I X) (μ : X)
    (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm D
      (algebraWord D μ a) (algebraWord D μ []))).coeff z =
      F.coeff D.toSKM D.skmSymmetrizer μ σ z := by
  have H : ∀ n, ∀ a : List (Letter I), a.length = n →
      ∀ F : CoefficientFamily a, F.Complete →
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm D
        (algebraWord D μ a) (algebraWord D μ []))).coeff z =
        F.coeff D.toSKM D.skmSymmetrizer μ σ z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have J : ∀ k, ∀ a : List (Letter I), a.length = n → inversions a = k →
          ∀ F : CoefficientFamily a, F.Complete →
          ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
          (signLaurent σ hσ (sesquilinearForm D
            (algebraWord D μ a) (algebraWord D μ []))).coeff z =
            F.coeff D.toSKM D.skmSymmetrizer μ σ z := by
        intro k
        induction k using Nat.strong_induction_on with
        | h k jk =>
          intro a ha hk F hF
          rcases sorted_or_interchange a with ⟨d, u, rfl⟩ | ⟨p, s, i, j, rfl⟩
          · exact sorted_comparison D μ d u [] (BoundaryFamily.ofCoefficient F hF)
          · obtain ⟨G, hG⟩ := exists_complete_coefficientFamily (p ++ (false, j) :: (true, i) :: s)
            have hg := jk _ (by have := inversions_swap p s i j; omega)
              (p ++ (false, j) :: (true, i) :: s) (by simpa using ha) rfl G hG
            by_cases hij : i = j
            · subst j
              obtain ⟨K, hK⟩ := exists_complete_coefficientFamily (p ++ s)
              have hshort : (p ++ s).length < n := by
                simp only [List.length_append, List.length_cons] at ha ⊢
                omega
              have hh := ih _ hshort (p ++ s) rfl K hK
              exact (same_boundary_labelled_form_coeff_iff F G K hF hG hK D μ
                (fun τ hτ v => (hh τ hτ v).symm)).mpr hg
            · obtain ⟨E, hE⟩ := opposite_boundary_labelled_form_coeff_iff (X := X)
                hij F.matching G.matching F.points G.points F.onStrand G.onStrand
                F.serialize G.serialize F.decorates G.decorates hF hG F.unique G.unique
              obtain ⟨hf, hh, _, _, hs⟩ := hE D μ
              intro τ hτ
              exact (hs τ hτ).mpr (hg τ hτ)
      intro a ha
      exact J (inversions a) a ha rfl
  exact H a.length a rfl F hF σ hσ z

end OddMath.SKM
