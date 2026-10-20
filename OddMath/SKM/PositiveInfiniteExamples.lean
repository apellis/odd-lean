/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.PositiveLabelledCoefficients
import OddMath.SKM.MatchingFamilyChoice
import OddMath.CoveringQuantum.UDot.WordCoefficientExamples

/-!
# Positive families on infinitely many colours

The positive case of BE2, arXiv:1701.04133v2, Theorem 10.3, Claim 1 applies to
`VermaWeightExamples.datum`, without bar consistency. The physical boundaries
have repeated and distinct colours and a negative common right weight. Complete
unique representatives and bounded points are obtained from the existing matching
existence results; the coefficient theorem constructs the serializer and ordinary
realizations before all signs and integer degrees. A populated degree fiber is
exhibited without asserting that its parity-weighted sum is nonzero.
-/

noncomputable section
namespace OddMath.SKM.PositiveInfiniteExamples
open StringDiagrams StringDiagrams.Chord CoveringQuantum CoveringQuantum.UDot
open GenericTensor VermaWeightExamples TriangularRepresentationExamples WordCoefficientExamples
open scoped BigOperators

/-- Infinite colours, failure of bar consistency, and negative right weight. -/
theorem datum_properties : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent ∧
    datum.h 0 baseWeight = -3 :=
  ⟨infinite_colours, not_barConsistent, negative_right_weight⟩

/-- Physical lower boundary, before reversal in the modified-algebra input. -/
abbrev lower : List (Letter ℕ) := List.ofFn fun r => (true, sourceColours r)

/-- Physical upper boundary, in a different colour order. -/
abbrev upper : List (Letter ℕ) := List.ofFn fun r => (true, targetColours r)

/-- Both nonempty boundaries contain repeated zero and distinct one. -/
theorem boundaries : lower = [(true, 0), (true, 0), (true, 1)] ∧
    upper = [(true, 0), (true, 1), (true, 0)] := by decide

/-- One strict representative of every realized pairing, chosen without form data. -/
def representatives : Set (List (TMove (Letter ℕ))) :=
  (exists_unique_matching_representatives lower upper).choose

/-- Every chosen representative is a strictly reduced matching. -/
theorem matching : ∀ R ∈ representatives, IsMatching₂ lower upper R ∧
    StrictReduced₂ lower R :=
  (exists_unique_matching_representatives lower upper).choose_spec.1

/-- Pairing classes have unique chosen representatives. -/
theorem unique : ∀ R ∈ representatives, ∀ S ∈ representatives,
    Iso (pairing₂ lower R) (pairing₂ lower S) → R = S :=
  (exists_unique_matching_representatives lower upper).choose_spec.2.1

/-- All strictly reduced matchings are covered. -/
theorem coverage : ∀ R, IsMatching₂ lower upper R → StrictReduced₂ lower R →
    ∃ S ∈ representatives, Iso (pairing₂ lower S) (pairing₂ lower R) :=
  (exists_unique_matching_representatives lower upper).choose_spec.2.2

/-- Distinguished points supplied by the matching existence theorem. -/
def points (R : {R // R ∈ representatives}) : ℕ → ℕ × ℕ :=
  (matching_bounded_points (matching R R.property).1).choose

/-- Every distinguished point lies on its specified strand. -/
theorem points_valid (R : {R // R ∈ representatives}) (j : ℕ)
    (hj : j ∈ leftEnds₂ lower R.val) : OnStrand₂ lower R.val j (points R j) :=
  ((matching_bounded_points (matching R R.property).1).choose_spec j hj).2

/-- Every chosen height is bounded by the representative length. -/
theorem points_bounded (R : {R // R ∈ representatives}) (j : ℕ)
    (hj : j ∈ leftEnds₂ lower R.val) : (points R j).1 ≤ R.val.length :=
  ((matching_bounded_points (matching R R.property).1).choose_spec j hj).1

/-- The original strand-label index, with no reference to the form. -/
abbrev Index := Σ R : {R // R ∈ representatives}, MatchingStrand lower R.val → ℕ

/-- The colour-preserving transposition supplies an inhabited representative family. -/
theorem index_nonempty : Nonempty Index := by
  obtain ⟨E, -⟩ := positive_representatives_equiv sourceColours targetColours
    representatives matching coverage unique
  have hw : ∀ r, sourceColours r = targetColours (Equiv.swap 1 2 r) := by decide
  let R := E.symm ⟨Equiv.swap 1 2, hw⟩
  exact ⟨⟨R, fun _ => 1⟩⟩

/-- The constructed serializer and ordinary layers work for every sign and degree. -/
theorem bounded_family :
    ∃ τ : ∀ R : {R // R ∈ representatives},
        (MatchingStrand lower R.val → ℕ) → List (DTMove ℕ),
      (∀ R c, Decorates₂ lower R.val (points R) (strandCounts c) (τ R c)) ∧
    ∃ (L : Index → List (LayerData ℕ)) (hL : ∀ t, SChain lower (L t) upper),
      (∀ t, (L t).map ofL = dLay lower (τ t.1 t.2)) ∧
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
        ∃ hf : Set.Finite {t : Index |
          Diagram.degree (gdeg datum.toSKM datum.skmSymmetrizer)
            (mkD datum.toSKM baseWeight (L t) (hL t)) = z},
          (∑ t ∈ hf.toFinset, σ ^ (xpar datum.toSKM baseWeight
            (dLay lower (τ t.1 t.2))).val) =
              (signLaurent σ hσ (sesquilinearForm datum sourceInput targetInput)).coeff z :=
  positive_bounded_points_family_form_coeff datum baseWeight sourceColours targetColours
    representatives matching coverage unique points points_valid points_bounded

/-- A populated finite fiber of these realizations satisfies the original coefficient
identity for both signs. Population alone does not assert a nonzero coefficient. -/
theorem populated_fiber :
    ∃ τ : ∀ R : {R // R ∈ representatives},
        (MatchingStrand lower R.val → ℕ) → List (DTMove ℕ),
      (∀ R c, Decorates₂ lower R.val (points R) (strandCounts c) (τ R c)) ∧
    ∃ (L : Index → List (LayerData ℕ)) (hL : ∀ t, SChain lower (L t) upper),
      (∀ t, (L t).map ofL = dLay lower (τ t.1 t.2)) ∧
    ∃ (z : ℤ) (hf : Set.Finite {t : Index |
      Diagram.degree (gdeg datum.toSKM datum.skmSymmetrizer)
        (mkD datum.toSKM baseWeight (L t) (hL t)) = z}),
      hf.toFinset.Nonempty ∧ ∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
        (∑ t ∈ hf.toFinset, σ ^ (xpar datum.toSKM baseWeight
          (dLay lower (τ t.1 t.2))).val) =
            (signLaurent σ hσ (sesquilinearForm datum sourceInput targetInput)).coeff z := by
  classical
  obtain ⟨τ, hτ, L, hL, hm, hc⟩ := bounded_family
  obtain ⟨t⟩ := index_nonempty
  let z := Diagram.degree (gdeg datum.toSKM datum.skmSymmetrizer)
    (mkD datum.toSKM baseWeight (L t) (hL t))
  obtain ⟨hf, -⟩ := hc 1 (by norm_num) z
  refine ⟨τ, hτ, L, hL, hm, z, hf, ⟨t, hf.mem_toFinset.mpr rfl⟩, ?_⟩
  intro σ hσ
  obtain ⟨hf', heq⟩ := hc σ hσ z
  exact heq

/-- The shorter positive input has two strands at the same negative right weight. -/
def shortInput : modified datum Coefficients.q Coefficients.pi :=
  positiveHalf datum Coefficients.q Coefficients.pi baseWeight
    (datum.toSerreF Coefficients.q Coefficients.pi
      (PreF.monomial Coefficients.Ring (List.ofFn (fun r : Fin 2 => r.val)).reverse))

/-- Unequal nonempty lengths give zero at every integer degree and either sign. -/
theorem unequal_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm datum sourceInput shortInput)).coeff z = 0 := by
  rw [sourceInput, shortInput, sesquilinearForm_positive_words_eq_zero_of_length_ne
    datum baseWeight sourceColours (fun r : Fin 2 => r.val) (by decide), map_zero]
  simp

/-- Unequal positive boundaries have no representative labels. -/
abbrev UnequalIndex := Σ R : {R : List (TMove (Letter ℕ)) // R ∈ (∅ : Set _)},
  MatchingStrand lower R.val → ℕ

/-- The unequal-length graphical family itself computes the zero coefficients;
its serializer and ordinary realizations still precede signs and integer degrees. -/
theorem unequal_family :
    ∃ τ : ∀ R : {R : List (TMove (Letter ℕ)) // R ∈ (∅ : Set _)},
        (MatchingStrand lower R.val → ℕ) → List (DTMove ℕ),
      (∀ R c, Decorates₂ lower R.val (fun _ => (0, 0)) (strandCounts c) (τ R c)) ∧
    ∃ (L : UnequalIndex → List (LayerData ℕ))
      (hL : ∀ t, SChain lower (L t) (List.ofFn fun r : Fin 2 => (true, r.val))),
      (∀ t, (L t).map ofL = dLay lower (τ t.1 t.2)) ∧
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
        ∃ hf : Set.Finite {t : UnequalIndex |
          Diagram.degree (gdeg datum.toSKM datum.skmSymmetrizer)
            (mkD datum.toSKM baseWeight (L t) (hL t)) = z},
          (∑ t ∈ hf.toFinset, σ ^ (xpar datum.toSKM baseWeight
            (dLay lower (τ t.1 t.2))).val) =
              (signLaurent σ hσ (sesquilinearForm datum sourceInput shortInput)).coeff z ∧
          (∑ t ∈ hf.toFinset, σ ^ (xpar datum.toSKM baseWeight
            (dLay lower (τ t.1 t.2))).val) = 0 := by
  obtain ⟨τ, hτ, L, hL, hm, hc⟩ := positive_bounded_points_family_form_coeff
    datum baseWeight sourceColours (fun r : Fin 2 => r.val) ∅ (by simp)
    (by intro R hR _; have h := hR.positive_length_eq sourceColours (fun r : Fin 2 => r.val)
        omega)
    (by simp) (fun _ _ => (0, 0))
    (by intro R; exact (Set.notMem_empty R.val R.property).elim)
    (by intro R; exact (Set.notMem_empty R.val R.property).elim)
  refine ⟨τ, hτ, L, hL, hm, ?_⟩
  intro σ hσ z
  obtain ⟨hf, heq⟩ := hc σ hσ z
  exact ⟨hf, heq, heq.trans (unequal_coeff σ hσ z)⟩

end OddMath.SKM.PositiveInfiniteExamples
