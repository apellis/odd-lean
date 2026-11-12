import OddMath.SKM.RouquierMulticolour
import OddMath.SKM.RouquierMateSectors

/-!
# Dot-power slides for the actual distinct crossings

The two distinct-colour relations (1.8), iterated without changing the
crossing. These are the dot transports in the finite-column reduction
of Brundan–Ellis, Lemma 7.1.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace RouquierMulticolour
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  {T : RouquierFamily (k := k) (B := B) D} {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) (i j : I) (hne : i ≠ j)
  {a b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
  (h₃ : a + D.α i = c) (h₄ : c + D.α j = d)

include M hne in
/-- Iterated left dot slide, retaining the exact inherited crossing. -/
theorem slideLeft_power (n : ℕ) :
    T.E j h₁ ◁ rouquierPower (T.dot i h₂) n ≫ T.cross i j h₁ h₂ h₃ h₄ =
      zsign k (D.parity i * D.parity j) ^ n •
        (T.cross i j h₁ h₂ h₃ h₄ ≫ rouquierPower (T.dot i h₃) n ▷ T.E j h₄) := by
  induction n with
  | zero => simp only [rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
      TwoSupercategory.id_whiskerRight (R := k), Category.id_comp, Category.comp_id,
      pow_zero, one_smul]
  | succ n ih =>
    rw [rouquierPower_succ, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
      M.slideLeft i j hne h₁ h₂ h₃ h₄, Linear.comp_smul, ← Category.assoc, ih,
      Linear.smul_comp, Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
      ← rouquierPower_succ, smul_smul, ← pow_succ']

end RouquierMulticolour
end OddMath.SKM
