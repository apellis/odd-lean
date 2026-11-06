import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierFamily
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuadraticFields
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSlideFields
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightGeneralBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedBraidField
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMateInverse

/-! # The multicolour relations of the chosen OLD probe family

Brundan–Ellis Definition 1.5, (1.7)–(1.9), (1.12): assemble all seven
fields for the prescribed scalar-evaluated probe family. The acting
scalar family is parameterTwist Sc; the presentation parameters remain
Sc. No action, local inverse or generator comparison is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
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
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (Λ : X) (hcutoff : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
local notation "Sc'" => parameterTwist D Sc

/-- All multicolour fields hold for the chosen OLD probe family and original parameters. -/
theorem probeOldRouquierMulticolour :
    SKM.RouquierMulticolour (probeOldRouquierFamily D Sc' m Λ hcutoff) Sc := by
  refine {
    quadZero := ?_
    quadNe := ?_
    slideLeft := ?_
    slideRight := ?_
    braid := ?_
    braidEq := ?_
    invNe := ?_ }
  · intro i j hij hd a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_quadZero D Sc m i j Λ h₁ h₂ h₃ h₄ hij hd
  · intro i j hij hd a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_quadNe D Sc m i j Λ h₁ h₂ h₃ h₄ hij hd
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_slideLeft D Sc m i j Λ h₁ h₂ h₃ h₄ hij
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_slideRight D Sc m i j Λ h₁ h₂ h₃ h₄ hij
  · intro i j l hb a bl bj bi clj cli cji d hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃
    change rouquierMulticolourBraidEquation D (probeOldRouquierData D Sc' m Λ)
      i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃
    exact probeOldRouquierData_generalBraid D Sc m i j l Λ
      hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ hb
  · apply braidEq_field D Sc (probeOldRouquierFamily D Sc' m Λ hcutoff)
    intro i j hij a b c d e f hab haf hbc hbe hfc hcd hed
    exact probeOldRouquierData_braidEq D Sc m i j Λ hab haf hbc hbe hfc hcd hed hij
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact probeOldRouquierData_invNe D Sc' m i j Λ h₁ h₂ h₃ h₄ hij

end OddMath.QuiverHecke
