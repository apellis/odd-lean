import OddMath.SKM.RouquierRectangularDottedUnit
import OddMath.SKM.RouquierDistinctPowerSlide
import OddMath.SKM.RouquierLeftCupCap
import OddMath.SKM.Calculus

/-!
# The actual distinct dotted unit reduction

Brundan–Ellis, Lemma 7.1: the dotted cup slides past the prescribed
sideways crossing with both Koszul signs cancelled. All dot-slide
hypotheses are discharged by the actual multicolour relation.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

private theorem dottedUnit_sign (p q : ZMod 2) (n : ℕ) :
    sign k (((n : ZMod 2) * p) * (p * q)) = zsign k (p * q) ^ n := by
  rw [← zsign_natCast_mul]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    rcases parity_eq_zero_or_one (n : ZMod 2) with hn | hn <;> simp [hn, sign, zsign]

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) (i j : I) (hne : i ≠ j)
  {a b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
  (h₃ : a + D.α i = c) (h₄ : c + D.α j = d)

include M hne in
/-- The prescribed distinct mate transports every dotted right cup.
There is no cap or cyclicity premise. -/
theorem distinctCrossMate_dottedUnit (n : ℕ) :
    (leftUnitor (T.E j h₁)).inv ≫
      ((T.adj i h₃).unit ≫ rouquierPower (T.dot i h₃) n ▷ T.F i h₃) ▷ T.E j h₁ ≫
      (associator (T.E i h₃) (T.F i h₃) (T.E j h₁)).hom ≫
      T.E i h₃ ◁ crossMate (T.adj i h₃) (T.adj i h₂) (T.cross i j h₁ h₂ h₃ h₄) =
    (rightUnitor (T.E j h₁)).inv ≫
      T.E j h₁ ◁ ((T.adj i h₂).unit ≫ rouquierPower (T.dot i h₂) n ▷ T.F i h₂) ≫
      (associator (T.E j h₁) (T.E i h₂) (T.F i h₂)).inv ≫
      T.cross i j h₁ h₂ h₃ h₄ ▷ T.F i h₂ ≫
      (associator (T.E i h₃) (T.E j h₄) (T.F i h₂)).hom := by
  apply crossMate_pitchfork_unit_dotted (T.adj i h₃) (T.adj i h₂)
    (T.E j h₁) (T.E j h₄) (T.cross i j h₁ h₂ h₃ h₄)
    (rouquierPower (T.dot i h₃) n) (rouquierPower (T.dot i h₂) n)
    (rouquierPower_mem (T.dot_mem i h₃) n) (T.cross_mem i j h₁ h₂ h₃ h₄)
  rw [koszulSign_smul (R := k), dottedUnit_sign]
  exact M.slideLeft_power i j hne h₁ h₂ h₃ h₄ n

end RouquierFamily
end OddMath.SKM
