/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMixedBraidEquation
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedBraid

/-! # The corrected braid field of the selected probe Rouquier data

Brundan–Ellis (1.9): decode the whole-weight polynomial braid as the
literal dotted Rouquier relation, retaining the chosen induction, crossing
and dot maps and the original scalar coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u v w r
section Decode
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (obj : X → B)
  (E : ∀ (i : I) {x y : X}, x + D.α i = y → (obj x ⟶ obj y))
  (dot : ∀ (i : I) {x y : X} (h : x + D.α i = y), End (E i h))
  (dot_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    dot i h ∈ parity (R := k) _ _ (D.parity i))
  (cross : ∀ (i j : I) {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    E j h₁ ≫ E i h₂ ⟶ E i h₃ ≫ E j h₄)
  (cross_mem : ∀ (i j : I) {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    cross i j h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _ (D.parity i * D.parity j))
  (i j : I) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "F₁" => E i hab
local notation "F₂" => E j hbc
local notation "F₃" => E i hcd
local notation "a₀" => E i hab ◁ cross i j hbc hcd hbe hed
local notation "a₁" => Iso.inv (associator (E i hab) (E i hbe) (E j hed)) ≫
  cross i i hab hbe hab hbe ▷ E j hed ≫
  Iso.hom (associator (E i hab) (E i hbe) (E j hed))
local notation "a₂" => E i hab ◁ cross j i hbe hed hbc hcd
local notation "b₀" => Iso.inv (associator (E i hab) (E j hbc) (E i hcd)) ≫
  cross j i hab hbc haf hfc ▷ E i hcd ≫
  Iso.hom (associator (E j haf) (E i hfc) (E i hcd))
local notation "b₁" => E j haf ◁ cross i i hfc hcd hfc hcd
local notation "b₂" => Iso.inv (associator (E j haf) (E i hfc) (E i hcd)) ≫
  cross i j haf hfc hab hbc ▷ E i hcd ≫
  Iso.hom (associator (E i hab) (E j hbc) (E i hcd))

private theorem mixedBraid_of_generators
    (h : a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End (F₁ ≫ F₂ ≫ F₃)) D Sc i j
        (dot i hab ▷ (F₂ ≫ F₃)) (F₁ ◁ (dot j hbc ▷ F₃)) (F₁ ◁ F₂ ◁ dot i hcd)) :
    rouquierMixedBraidEquation D Sc
      { obj := obj, E := E, dot := dot, dot_mem := dot_mem,
        cross := cross, cross_mem := cross_mem } i j hab haf hbc hbe hfc hcd hed := by
  exact rouquierMixedBraidEquation_of_polynomial D Sc _ i j hab haf hbc hbe hfc hcd hed h
end Decode

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Sc'" => parameterTwist D Sc
local notation "F₀" => probeOldE D Sc' m i Λ hab ≫ probeOldE D Sc' m j Λ hbc ≫ probeOldE D Sc' m i Λ hcd
local notation "a₀" => probeOldWeightCrossSuffix D Sc' m i j i Λ hab hbc hbe hcd hed
local notation "a₁" => probeOldWeightCrossPrefix D Sc' m j i i Λ hab hab hbe hbe hed
local notation "a₂" => probeOldWeightCrossSuffix D Sc' m j i i Λ hab hbe hbc hed hcd
local notation "b₀" => probeOldWeightCrossPrefix D Sc' m i j i Λ hab haf hbc hfc hcd
local notation "b₁" => probeOldWeightCrossSuffix D Sc' m i i j Λ haf hfc hfc hcd hcd
local notation "b₂" => probeOldWeightCrossPrefix D Sc' m i i j Λ haf hab hfc hbc hcd
local notation "x₀" => probeOldWeightTripleFirstDot D Sc' m i j i Λ hab hbc hcd
local notation "x₁" => probeOldWeightTripleMiddleDot D Sc' m i j i Λ hab hbc hcd
local notation "x₂" => probeOldWeightTripleLastDot D Sc' m i j i Λ hab hbc hcd

private theorem probeMixedBraidField_of_polynomial
    (h : a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial D Sc (R := End F₀) i j x₀ x₁ x₂) :
    rouquierMixedBraidEquation D Sc (probeOldRouquierData D Sc' m Λ) i j
      hab haf hbc hbe hfc hcd hed := by
  dsimp only [probeOldWeightCrossPrefix, probeOldWeightCrossSuffix,
    probeOldWeightTripleFirstDot, probeOldWeightTripleMiddleDot,
    probeOldWeightTripleLastDot] at h
  exact mixedBraid_of_generators D Sc
    (probeOldWeightSpace D Sc' m Λ)
    (fun i _ _ h => probeOldE D Sc' m i Λ h)
    (fun i _ _ h => probeOldActionDot D Sc' m i Λ h)
    (fun i _ _ h => probeOldActionDot_mem D Sc' m i Λ h)
    (fun i j _ _ _ _ h₁ h₂ h₃ h₄ => probeOldActionCross D Sc' m Λ i j h₁ h₂ h₃ h₄)
    (fun i j _ _ _ _ h₁ h₂ h₃ h₄ => probeOldActionCross_mem D Sc' m Λ i j h₁ h₂ h₃ h₄)
    i j hab haf hbc hbe hfc hcd hed h

/-- The prescribed probe generators satisfy the literal corrected braid field.
The coefficients are `Sc`; the acting category uses `parameterTwist D Sc`. -/
theorem probeOldRouquierData_braidEq (hne : i ≠ j) :
    rouquierMixedBraidEquation D Sc (probeOldRouquierData D Sc' m Λ) i j
      hab haf hbc hbe hfc hcd hed := by
  exact probeMixedBraidField_of_polynomial D Sc m i j Λ hab haf hbc hbe hfc hcd hed
    (probeOldActionCross_mixedBraid D Sc m i j Λ hab haf hbc hbe hfc hcd hed hne)

end OddMath.QuiverHecke
