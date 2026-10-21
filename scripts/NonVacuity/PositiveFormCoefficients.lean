import OddMath

/-! Non-vacuity checks in `OddMath.SKM.PositiveFormCoefficientsNonVacuity`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace OddMath.SKM.PositiveFormCoefficientsNonVacuity
open CoveringQuantum StringDiagrams StringDiagrams.Chord
open PositiveDecoratedFamilyCoefficientsExamples PositiveFormCoefficientsExamples
open scoped BigOperators

example :
    ∃ p : ∀ R : {R : List (TMove (Letter Unit)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val ≃ Fin 0,
      (∀ R (j : MatchingStrand [] R.val),
        OnStrand₂ [] R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ [] ({[]} : Set _)
         (fun R c => topDotMoves [] R (topPositionExtension {[]} p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain [] (L D) []),
         (∀ D, (L D).map ofL = D.val) ∧
         ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = z},
           (∑ D ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm 1 (by norm_num) 0).coeff z ∧
           (∑ D ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             if z = 0 then 1 else 0) :=
  empty_family 1 (by norm_num)

example :
    ∃ p : ∀ R : {R : List (TMove (Letter Unit)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val ≃ Fin 0,
      (∀ R (j : MatchingStrand [] R.val),
        OnStrand₂ [] R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ [] ({[]} : Set _)
         (fun R c => topDotMoves [] R (topPositionExtension {[]} p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain [] (L D) []),
         (∀ D, (L D).map ofL = D.val) ∧
         ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = z},
           (∑ D ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm (-1) (by norm_num) 0).coeff z ∧
           (∑ D ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             if z = 0 then 1 else 0) :=
  empty_family (-1) (by norm_num)

example :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ repeatedWord repeatedFamily
         (fun R c => topDotMoves repeatedWord R
           (topPositionExtension repeatedFamily p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain repeatedWord (L D) repeatedWord),
         (∀ D, (L D).map ofL = D.val) ∧
         ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = -2},
           (∑ D ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm 1 (by norm_num) 2).coeff (-2) ∧
           (∑ D ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) = 1) :=
  repeated_family 1 (by norm_num)

example :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ repeatedWord repeatedFamily
         (fun R c => topDotMoves repeatedWord R
           (topPositionExtension repeatedFamily p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain repeatedWord (L D) repeatedWord),
         (∀ D, (L D).map ofL = D.val) ∧
         ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = -2},
           (∑ D ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm (-1) (by norm_num) 2).coeff (-2) ∧
           (∑ D ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) = (-1)) :=
  repeated_family (-1) (by norm_num)

example (z : ℤ) : (repeatedForm 1 (by norm_num) 0).coeff z = if z = 0 then 1 else 0 :=
  PositiveFormCoefficientsExamples.empty_coeff 1 (by norm_num) z
example (z : ℤ) : (repeatedForm (-1) (by norm_num) 0).coeff z = if z = 0 then 1 else 0 :=
  PositiveFormCoefficientsExamples.empty_coeff (-1) (by norm_num) z
example : (repeatedForm 1 (by norm_num) 2).coeff (-2) = 1 ∧
    (repeatedForm 1 (by norm_num) 2).coeff (-3) = 0 := repeated_negative_coeff 1 (by norm_num)
example : (repeatedForm (-1) (by norm_num) 2).coeff (-2) = -1 ∧
    (repeatedForm (-1) (by norm_num) 2).coeff (-3) = 0 := repeated_negative_coeff (-1) (by norm_num)

end OddMath.SKM.PositiveFormCoefficientsNonVacuity
