import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierFamily
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadraticRelation
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDistinctSlideRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraidRelation
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedRelation
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossMate

/-! # The multicolour relations of the selected original-weight family

Brundan--Ellis Definition 1.5, (1.7)–(1.9), (1.12). Assemble all seven
multicolour fields from the prescribed induction/restriction, adjunction,
dots and crossings. The acting scalar family is parameterTwist Sc while
the presentation parameters remain Sc.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r
section Field
variable {k : Type u} [CommRing k] {B : Type v} [BicategoryStruct.{w,r} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (T : SKM.RouquierFamily (k := k) (B := B) D)

/-- Decode the named dotted equation while the family is abstract; the
closed chosen action is substituted only after this conversion. -/
private theorem braidEq_field
    (h : ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
      (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
      (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
      (hed : e + D.α j = d),
      rouquierMixedBraidEquation D Sc T.toRouquierData i j hab haf hbc hbe hfc hcd hed)
: ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
    (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
    (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
    (hed : e + D.α j = d),
    T.E i hab ◁ T.cross i j hbc hcd hbe hed ≫
        (associator (T.E i hab) (T.E i hbe) (T.E j hed)).inv ≫
        T.cross i i hab hbe hab hbe ▷ T.E j hed ≫
        (associator (T.E i hab) (T.E i hbe) (T.E j hed)).hom ≫
        T.E i hab ◁ T.cross j i hbe hed hbc hcd -
      ((associator (T.E i hab) (T.E j hbc) (T.E i hcd)).inv ≫
        T.cross j i hab hbc haf hfc ▷ T.E i hcd ≫
        (associator (T.E j haf) (T.E i hfc) (T.E i hcd)).hom ≫
        T.E j haf ◁ T.cross i i hfc hcd hfc hcd ≫
        (associator (T.E j haf) (T.E i hfc) (T.E i hcd)).inv ≫
        T.cross i j haf hfc hab hbc ▷ T.E i hcd ≫
        (associator (T.E i hab) (T.E j hbc) (T.E i hcd)).hom) =
      ∑ s ∈ Finset.range (D.dn i j),
        (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (SKM.rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
            T.E i hab ◁ T.E j hbc ◁ SKM.rouquierPower (T.dot i hcd) (D.dn i j - 1 - s)) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
        (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (SKM.rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
            T.E i hab ◁ (SKM.rouquierPower (T.dot j hbc) q ▷ T.E i hcd) ≫
            T.E i hab ◁ T.E j hbc ◁ SKM.rouquierPower (T.dot i hcd) (p - 1 - s)) := by
  intro i j hij a b c d e f hab haf hbc hbe hfc hcd hed
  exact h i j hij hab haf hbc hbe hfc hcd hed
end Field

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
local notation "Sc'" => parameterTwist D Sc

/-- The chosen weight family satisfies every multicolour relation of the
original-Sc presentation. The cutoff is the stated highest-weight pairing. No factor-action,
local-inverse or generator-compatibility premise is required. -/
theorem elvRouquierMulticolour :
    SKM.RouquierMulticolour
      (elvRouquierFamily D Sc' cutoff bound Λ hcutoff) Sc := by
  refine {
    quadZero := ?_
    quadNe := ?_
    slideLeft := ?_
    slideRight := ?_
    braid := ?_
    braidEq := ?_
    invNe := ?_ }
  · intro i j hij hd a b c d h₁ h₂ h₃ h₄
    exact elvActionCross_quadZero D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij hd
  · intro i j hij hd a b c d h₁ h₂ h₃ h₄
    exact elvActionCross_quadNe D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij hd
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact elvActionCross_slideLeft_distinct D Sc' cutoff bound i j Λ h₁ h₂ h₃ h₄ hij
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact elvActionCross_slideRight_distinct D Sc' cutoff bound i j Λ h₁ h₂ h₃ h₄ hij
  · intro i j l hb a bl bj bi clj cli cji d hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃
    change rouquierMulticolourBraidEquation D (elvRouquierData D Sc' cutoff bound Λ)
      i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃
    exact elvRouquierData_multicolour_braid D Sc' cutoff bound i j l Λ
      hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ hb
  · apply braidEq_field D Sc (elvRouquierFamily D Sc' cutoff bound Λ hcutoff)
    intro i j hij a b c d e f hab haf hbc hbe hfc hcd hed
    exact elvRouquierData_braidEq D Sc cutoff bound i j Λ hab haf hbc hbe hfc hcd hed hij
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact elvActionCrossMate_isIso D Sc' cutoff bound i j Λ h₁ h₂ h₃ h₄ hij

end OddMath.QuiverHecke.ELVOld
