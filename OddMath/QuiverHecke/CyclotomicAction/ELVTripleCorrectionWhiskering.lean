import OddMath.QuiverHecke.CyclotomicAction.ELVTripleCorrectionPolynomial
import OddMath.SKM.RouquierMateSectors
import OddMath.SKM.RouquierCoupled

/-! # The ordered correction as dotted whiskerings

Brundan--Ellis (1.9). The noncommutative three-position polynomial is
exactly the prescribed dotted correction, in every two-supercategory.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c d : B} (F : a ⟶ b) (G : b ⟶ c) (H : c ⟶ d)
  (x : End F) (y : End G) (z : End H)

/-- The exact correction sum of the Rouquier multicolour braid field,
with every dot power in its prescribed position and order. -/
theorem tripleDotCorrectionPolynomial_whiskers :
    tripleDotCorrectionPolynomial (R := End (F ≫ G ≫ H)) D Sc i j
      (x ▷ (G ≫ H)) (F ◁ (y ▷ H)) (F ◁ G ◁ z) =
    ∑ s ∈ Finset.range (D.dn i j),
      (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
        (SKM.rouquierPower x s ▷ (G ≫ H) ≫ F ◁ G ◁ SKM.rouquierPower z (D.dn i j - 1 - s)) +
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
      (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
        (SKM.rouquierPower x s ▷ (G ≫ H) ≫ F ◁ (SKM.rouquierPower y q ▷ H) ≫
          F ◁ G ◁ SKM.rouquierPower z (p - 1 - s)) := by
  have hX (n : ℕ) := SKM.whiskerRight_rouquierPower (k := k) (B := B) x (G ≫ H) n
  have hY (n : ℕ) : (show End (F ≫ G ≫ H) from F ◁ (y ▷ H)) ^ n =
      F ◁ (SKM.rouquierPower y n ▷ H) := by
    rw [SKM.whiskerLeft_rouquierPower (k := k), SKM.rouquierPower_eq_pow, SKM.whiskerRight_rouquierPower (k := k)]
  have hZ (n : ℕ) : (show End (F ≫ G ≫ H) from F ◁ G ◁ z) ^ n =
      F ◁ G ◁ SKM.rouquierPower z n := by
    rw [SKM.whiskerLeft_rouquierPower (k := k), SKM.rouquierPower_eq_pow, SKM.whiskerLeft_rouquierPower (k := k)]
  simp only [tripleDotCorrectionPolynomial, tripleDotCorrectionSum, pow_zero, mul_one]
  simp_rw [hX, hY, hZ]
  simp only [End.mul_def]

end OddMath.QuiverHecke.ELVOld
