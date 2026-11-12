import OddMath.QuiverHecke.CyclotomicAction.ELVTripleCorrectionWhiskering

/-! # The dotted mixed braid equation of Rouquier data

Brundan--Ellis (1.9). Keep the exact RouquierMulticolour.braidEq formula
as one generic proposition before specializing large selected functors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (R : SKM.RouquierData (k := k) (B := B) D) (i j : I) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)

/-- Exactly the repeated-outer dotted equation in RouquierMulticolour,
with the prescribed associators, crossing maps and dot powers. -/
def rouquierMixedBraidEquation : Prop :=
    R.E i hab ◁ R.cross i j hbc hcd hbe hed ≫
        Iso.inv (associator (R.E i hab) (R.E i hbe) (R.E j hed)) ≫
        R.cross i i hab hbe hab hbe ▷ R.E j hed ≫
        Iso.hom (associator (R.E i hab) (R.E i hbe) (R.E j hed)) ≫
        R.E i hab ◁ R.cross j i hbe hed hbc hcd -
      (Iso.inv (associator (R.E i hab) (R.E j hbc) (R.E i hcd)) ≫
        R.cross j i hab hbc haf hfc ▷ R.E i hcd ≫
        Iso.hom (associator (R.E j haf) (R.E i hfc) (R.E i hcd)) ≫
        R.E j haf ◁ R.cross i i hfc hcd hfc hcd ≫
        Iso.inv (associator (R.E j haf) (R.E i hfc) (R.E i hcd)) ≫
        R.cross i j haf hfc hab hbc ▷ R.E i hcd ≫
        Iso.hom (associator (R.E i hab) (R.E j hbc) (R.E i hcd))) =
      ∑ s ∈ Finset.range (D.dn i j),
        (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (SKM.rouquierPower (R.dot i hab) s ▷ (R.E j hbc ≫ R.E i hcd) ≫
            R.E i hab ◁ R.E j hbc ◁ SKM.rouquierPower (R.dot i hcd) (D.dn i j - 1 - s)) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
        (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (SKM.rouquierPower (R.dot i hab) s ▷ (R.E j hbc ≫ R.E i hcd) ≫
            R.E i hab ◁ (SKM.rouquierPower (R.dot j hbc) q ▷ R.E i hcd) ≫
            R.E i hab ◁ R.E j hbc ◁ SKM.rouquierPower (R.dot i hcd) (p - 1 - s))

local notation "F₁" => R.E i hab
local notation "F₂" => R.E j hbc
local notation "F₃" => R.E i hcd
local notation "a₀" => R.E i hab ◁ R.cross i j hbc hcd hbe hed
local notation "a₁" => Iso.inv (associator (R.E i hab) (R.E i hbe) (R.E j hed)) ≫
  R.cross i i hab hbe hab hbe ▷ R.E j hed ≫
  Iso.hom (associator (R.E i hab) (R.E i hbe) (R.E j hed))
local notation "a₂" => R.E i hab ◁ R.cross j i hbe hed hbc hcd
local notation "b₀" => Iso.inv (associator (R.E i hab) (R.E j hbc) (R.E i hcd)) ≫
  R.cross j i hab hbc haf hfc ▷ R.E i hcd ≫
  Iso.hom (associator (R.E j haf) (R.E i hfc) (R.E i hcd))
local notation "b₁" => R.E j haf ◁ R.cross i i hfc hcd hfc hcd
local notation "b₂" => Iso.inv (associator (R.E j haf) (R.E i hfc) (R.E i hcd)) ≫
  R.cross i j haf hfc hab hbc ▷ R.E i hcd ≫
  Iso.hom (associator (R.E i hab) (R.E j hbc) (R.E i hcd))

/-- The ordered polynomial form implies the literal dotted braid field.
This conversion is made before any selected large action is substituted. -/
theorem rouquierMixedBraidEquation_of_polynomial
    (h : a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End (F₁ ≫ F₂ ≫ F₃)) D Sc i j
        (R.dot i hab ▷ (F₂ ≫ F₃)) (F₁ ◁ (R.dot j hbc ▷ F₃)) (F₁ ◁ F₂ ◁ R.dot i hcd)) :
    rouquierMixedBraidEquation D Sc R i j hab haf hbc hbe hfc hcd hed := by
  have hp := tripleDotCorrectionPolynomial_whiskers D Sc i j F₁ F₂ F₃
    (R.dot i hab) (R.dot j hbc) (R.dot i hcd)
  have hh := h.trans hp
  simpa only [rouquierMixedBraidEquation, Category.assoc] using hh

end OddMath.QuiverHecke.ELVOld
