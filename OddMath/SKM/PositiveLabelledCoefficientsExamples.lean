/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.PositiveLabelledCoefficients
import OddMath.SKM.PositiveFormCoefficientsExamples
/-!
# Examples for positive strand-labelled coefficients

The one-odd-root datum gives complete identity/transposition representatives.
A serializer reverses the two unit dots on the identity, so the coefficient consumer
is not limited to the canonical dot order. It computes both signs with one ordinary
realization and one negative-degree fiber. A separate application constructs its
serializer from bounded strand points and computes both signs on that shared fiber.
Empty boundaries are also exercised.
-/

noncomputable section
namespace OddMath.SKM.PositiveLabelledCoefficientsExamples
open StringDiagrams StringDiagrams.Chord
open PositiveDecoratedFamilyCoefficientsExamples PositiveFormCoefficientsExamples
open DTMove
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Top positions for the identity and transposition representatives. -/
def position (R : List (TMove (Letter Unit))) (j : ℕ) : ℕ :=
  if R = [] then 1 - j else j

def points (R : {R // R ∈ repeatedFamily}) (j : ℕ) : ℕ × ℕ :=
  (R.val.length, position R.val j)

private theorem identity_leftEnds : leftEnds₂ repeatedWord [] = [0, 1] := by
  have hh (x : ℕ) : IsLeftEnd (pairing₂ repeatedWord []) x ↔ x < 2 :=
    mem_leftEnds₂.symm.trans (positive_mem_leftEnds₂
      (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) (family_matching [] (by simp)).1 x)
  unfold leftEnds₂
  simp only [show (pairing₂ repeatedWord []).length = 4 from rfl, hh]
  decide

theorem points_valid : ∀ R j, j ∈ leftEnds₂ repeatedWord R.val →
    OnStrand₂ repeatedWord R.val j (points R j) := by
  intro R j hj
  have hj' : j < 2 := (positive_mem_leftEnds₂ (fun _ : Fin 2 => ())
    (fun _ : Fin 2 => ()) (family_matching R R.property).1 j).mp hj
  have hR : R.val = [] ∨ R.val = [.mv (.cross 0)] := R.property
  rcases hR with hR | hR
  · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simp only [points, hR, position]
      change 1 < 2 ∧ 0 = 0
      decide
    · simp only [points, hR, position]
      change 0 < 2 ∧ 2 = 2
      decide
  · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simp only [points, hR, position, List.cons_ne_nil, ite_false]
      change 0 < 2 ∧ 0 = 0
      decide
    · simp only [points, hR, position, List.cons_ne_nil, ite_false]
      change 1 < 2 ∧ 2 = 2
      decide

/-- Reverse the two dots for the identity with unit labels; use top order otherwise. -/
def serializer (R : {R // R ∈ repeatedFamily}) (c : MatchingStrand repeatedWord R.val → ℕ) :
    List (DTMove Unit) :=
  if R.val = [] ∧ c = fun _ => 1 then [.dt 0, .dt 1]
  else topDotMoves repeatedWord R.val (fun j => position R.val j.val) c

theorem serializer_valid (R : {R // R ∈ repeatedFamily})
    (c : MatchingStrand repeatedWord R.val → ℕ) :
    Decorates₂ repeatedWord R.val (points R) (strandCounts c) (serializer R c) := by
  unfold serializer
  split_ifs with h
  · rcases h with ⟨hR, rfl⟩
    constructor
    · change [] = R.val
      exact hR.symm
    · simp only [points, hR, identity_leftEnds, List.flatMap_cons, List.flatMap_nil]
      simp only [strandCounts, hR, identity_leftEnds, List.mem_cons, List.not_mem_nil,
        or_false, List.append_nil,
        position, List.length_nil]
      change List.Perm [(0, 0), (0, 1)] [(0, 1), (0, 0)]
      exact List.Perm.swap _ _ []
  · have ht := topDotMoves_decorates repeatedWord R.val (fun j => position R.val j.val) c
    refine ⟨ht.1, ht.2.trans ?_⟩
    apply List.Perm.of_eq
    apply List.flatMap_congr
    intro j hj
    simp [points, strandPosition, hj]

abbrev Index := Σ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val → ℕ

/-- One shared ordinary realization computes both sign specializations at every degree. -/
theorem repeated_family :
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain repeatedWord (L t) repeatedWord),
      (∀ t, (L t).map ofL = dLay repeatedWord (serializer t.1 t.2)) ∧
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
        ∃ hf : Set.Finite {t : Index |
          Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
            (mkD oddDatum.toSKM 0 (L t) (hL t)) = z},
          (∑ t ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0
            (dLay repeatedWord (serializer t.1 t.2))).val) = (repeatedForm σ hσ 2).coeff z :=
  positive_labelled_family_form_coeff oddDatum 0
    (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) repeatedFamily
    family_matching family_coverage family_unique points points_valid serializer serializer_valid

/-- The selected unit-labelled identity uses the opposite dot order to `topDotMoves`. -/
theorem noncanonical_order :
    let R : {R // R ∈ repeatedFamily} := ⟨[], by simp⟩
    serializer R (fun _ => 1) = [.dt 0, .dt 1] ∧
      topDotMoves repeatedWord R.val (fun j => position R.val j.val) (fun _ => 1) =
        [.dt 1, .dt 0] := by
  constructor
  · simp [serializer]
  · simp [topDotMoves, identity_leftEnds, strandCounts, strandPosition, position]

/-- Both signs use the same realization and the same negative-degree fiber. -/
theorem repeated_signs :
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain repeatedWord (L t) repeatedWord),
      (∀ t, (L t).map ofL = dLay repeatedWord (serializer t.1 t.2)) ∧
      ∃ hf : Set.Finite {t : Index |
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
          (mkD oddDatum.toSKM 0 (L t) (hL t)) = -2},
        (∑ t ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (serializer t.1 t.2))).val) = 1 ∧
        (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (serializer t.1 t.2))).val) = -1 := by
  obtain ⟨L, hL, hm, hc⟩ := repeated_family
  obtain ⟨hf, hplus⟩ := hc 1 (by norm_num) (-2)
  obtain ⟨hf', hminus⟩ := hc (-1) (by norm_num) (-2)
  exact ⟨L, hL, hm, hf, hplus.trans (repeated_negative_coeff 1 (by norm_num)).1,
    hminus.trans (repeated_negative_coeff (-1) (by norm_num)).1⟩

abbrev EmptyIndex := Σ R : {R : List (TMove (Letter Unit)) // R ∈ ({[]} : Set _)},
  MatchingStrand [] R.val → ℕ

/-- Empty boundaries give a unit coefficient in degree zero for each sign. -/
theorem empty_family :
    ∃ (L : EmptyIndex → List (LayerData Unit)) (hL : ∀ t, SChain [] (L t) []),
      (∀ t, (L t).map ofL = dLay [] []) ∧
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
        ∃ hf : Set.Finite {t : EmptyIndex |
          Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
            (mkD oddDatum.toSKM 0 (L t) (hL t)) = z},
          (∑ _t ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0 (dLay [] [])).val) =
            (repeatedForm σ hσ 0).coeff z ∧
          (∑ _t ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0 (dLay [] [])).val) =
            if z = 0 then 1 else 0 := by
  let a : Fin 0 → Unit := fun _ => ()
  have hm : IsMatching₂ [] ([] : List (Letter Unit)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ ([] : List (Letter Unit)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨L, hL, hmap, hc⟩ := positive_labelled_family_form_coeff oddDatum
    0 a a {[]}
    (by intro R hR; obtain rfl := Set.mem_singleton_iff.mp hR; exact ⟨hm, hr⟩)
    (by
      intro R hR _
      refine ⟨[], Set.mem_singleton _, ?_⟩
      have hs := hR.pairing_properties.2.2
      have he : pairing₂ [] R = [] := by simpa using hs
      change Iso [] (pairing₂ [] R)
      rw [he]
      exact Iso.refl _)
    (by intro R hR S hS _
        exact (Set.mem_singleton_iff.mp hR).trans (Set.mem_singleton_iff.mp hS).symm)
    (fun _ _ => (0, 0))
    (by intro R j hj; have hR := Set.mem_singleton_iff.mp R.property
        have hl : leftEnds₂ (List.ofFn fun r => (true, a r)) R.val = [] := by rw [hR]; rfl
        simp only [hl, List.not_mem_nil] at hj)
    (fun _ _ => [])
    (by
      intro R c
      have hR := Set.mem_singleton_iff.mp R.property
      constructor
      · exact hR.symm
      · have hl : leftEnds₂ (List.ofFn fun r => (true, a r)) R.val = [] := by rw [hR]; rfl
        simp only [dotPts, hl, List.flatMap_nil]
        exact List.Perm.refl [])
  refine ⟨L, hL, hmap, ?_⟩
  intro σ hσ z
  obtain ⟨hf, h⟩ := hc σ hσ z
  exact ⟨hf, h, h.trans (PositiveFormCoefficientsExamples.empty_coeff σ hσ z)⟩

/-- These distinguished points have the maximum permitted height. -/
theorem points_bounded : ∀ R j, j ∈ leftEnds₂ repeatedWord R.val →
    (points R j).1 ≤ R.val.length := by
  intro R j _
  exact le_rfl

/-- Bounded points alone construct a shared serializer and ordinary realization. -/
theorem bounded_repeated_family :
    ∃ (τ : ∀ R : {R // R ∈ repeatedFamily},
        (MatchingStrand repeatedWord R.val → ℕ) → List (DTMove Unit)),
      (∀ R c, Decorates₂ repeatedWord R.val (points R) (strandCounts c) (τ R c)) ∧
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain repeatedWord (L t) repeatedWord),
      (∀ t, (L t).map ofL = dLay repeatedWord (τ t.1 t.2)) ∧
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
        ∃ hf : Set.Finite {t : Index |
          Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
            (mkD oddDatum.toSKM 0 (L t) (hL t)) = z},
          (∑ t ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0
            (dLay repeatedWord (τ t.1 t.2))).val) = (repeatedForm σ hσ 2).coeff z :=
  positive_bounded_points_family_form_coeff oddDatum 0
    (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) repeatedFamily
    family_matching family_coverage family_unique points points_valid points_bounded

/-- Both signs on one degree minus two fiber of the constructed serializer. -/
theorem bounded_repeated_signs :
    ∃ (τ : ∀ R : {R // R ∈ repeatedFamily},
        (MatchingStrand repeatedWord R.val → ℕ) → List (DTMove Unit)),
      (∀ R c, Decorates₂ repeatedWord R.val (points R) (strandCounts c) (τ R c)) ∧
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain repeatedWord (L t) repeatedWord),
      (∀ t, (L t).map ofL = dLay repeatedWord (τ t.1 t.2)) ∧
      ∃ hf : Set.Finite {t : Index |
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
          (mkD oddDatum.toSKM 0 (L t) (hL t)) = -2},
        (∑ t ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (τ t.1 t.2))).val) = 1 ∧
        (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (τ t.1 t.2))).val) = -1 := by
  obtain ⟨τ, hτ, L, hL, hm, hc⟩ := bounded_repeated_family
  obtain ⟨hf, hplus⟩ := hc 1 (by norm_num) (-2)
  obtain ⟨hf', hminus⟩ := hc (-1) (by norm_num) (-2)
  exact ⟨τ, hτ, L, hL, hm, hf, hplus.trans (repeated_negative_coeff 1 (by norm_num)).1,
    hminus.trans (repeated_negative_coeff (-1) (by norm_num)).1⟩

end OddMath.SKM.PositiveLabelledCoefficientsExamples
