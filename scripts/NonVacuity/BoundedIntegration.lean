import OddMath

/-! Non-vacuity checks in `BoundedIntegrationNonVacuity`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace BoundedIntegrationNonVacuity
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveLabelledCoefficientsExamples
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open OddMath.SKM.DTMove
open scoped BigOperators
attribute [local instance] Classical.propDecidable

example :
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

example :
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

example : ∃ ds : List (DTMove Unit),
    Decorates₂ [(true, ())] [] (fun _ => (0, 0))
      (strandCounts fun _ : MatchingStrand [(true, ())] [] => 3) ds ∧
    DOk₂ [(true, ())] ds :=
  BoundedPointSerializationExamples.identity_boundary

example : ∃ ds : List (DTMove Unit),
    tmoves ds = [.mv (.cross 0), .mv (.cross 1)] ∧
    (dotPts ds).Perm [(2, 1), (0, 2), (1, 0), (0, 1), (2, 1)] :=
  BoundedPointSerializationExamples.unsorted_boundaries

example : ∃ ds : List (DTMove Unit),
    Decorates₂ (List.ofFn fun _ : Fin 3 => (true, ()))
      [.mv (.cross 0), .mv (.cross 1)]
      (fun j => (1, if j = 0 then 2 else if j = 1 then 0 else 1))
      (strandCounts fun j : MatchingStrand (List.ofFn fun _ : Fin 3 => (true, ()))
        [.mv (.cross 0), .mv (.cross 1)] => j.val + 1) ds ∧
    DOk₂ (List.ofFn fun _ : Fin 3 => (true, ())) ds :=
  BoundedPointSerializationExamples.interior_counts

end BoundedIntegrationNonVacuity
