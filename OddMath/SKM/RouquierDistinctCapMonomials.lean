import OddMath.SKM.RouquierDistinctMixedBraid
import OddMath.SKM.RouquierRectangularMonomials
import OddMath.SKM.RouquierInverseRelations

/-!
# Cap coefficients of the distinct mixed-braid monomials

Brundan–Ellis, Lemma 7.1: the separated dotted terms in Lemma 3.3's
mixed-braid correction meet the inverse-defined left cap in the exact
boundary Kronecker coefficient. This uses only the prescribed right
adjunctions, the actual dot powers, and the local inverse relations.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (i j : I)
  {a b c d f : X} (hab : a + D.α i = b) (hbc : b + D.α j = c)
  (hcd : c + D.α i = d)
local notation "Eab" => T.E i hab
local notation "Ebc" => T.E j hbc
local notation "Ecd" => T.E i hcd
local notation "Fab" => T.F i hab
local notation "Fcd" => T.F i hcd

/-- The exact ordered monomial is a dotted cap, middle dot power, and
dotted cup under the same outer mate used by the mixed braid. -/
theorem distinctMixedBraidOuterMate_monomial (s q n : ℕ) :
    T.distinctMixedBraidOuterMate i j hab hbc hcd
      (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
        Eab ◁ (rouquierPower (T.dot j hbc) q ▷ Ecd) ≫
        Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) n) =
    (Fab ◁ rouquierPower (T.dot i hab) s ≫ (T.adj i hab).counit) ▷ Ebc ≫
      (leftUnitor Ebc).hom ≫ rouquierPower (T.dot j hbc) q ≫
      (rightUnitor Ebc).inv ≫ Ebc ◁ ((T.adj i hcd).unit ≫
        rouquierPower (T.dot i hcd) n ▷ Fcd) := by
  rw [T.distinctMixedBraidOuterMate_apply]
  have h := rectangularMate_separated Ebc (T.adj i hab) (T.adj i hcd)
    (rouquierPower (T.dot i hab) s) (rouquierPower (T.dot j hbc) q)
    (rouquierPower (T.dot i hcd) n)
  have hn := TwoSupercategory.associator_naturality_left (R := k)
    (rouquierPower (T.dot i hab) s) Ebc Ecd
  simpa only [TwoSupercategory.whiskerLeft_comp (R := k), reassoc_of% hn] using h

/-- Capping a separated monomial gives its precise boundary coefficient
through the entire negative-height window. -/
theorem distinctMixedBraidOuterMate_monomial_cap (hfc : f + D.α i = c)
    (hh : D.h i c < 0) (s q n : ℕ) (hn : n < (-D.h i c).toNat) :
    T.distinctMixedBraidOuterMate i j hab hbc hcd
      (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
        Eab ◁ (rouquierPower (T.dot j hbc) q ▷ Ecd) ≫
        Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) n) ≫
      Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom =
    if n = (-D.h i c - 1).toNat then
      (Fab ◁ rouquierPower (T.dot i hab) s ≫ (T.adj i hab).counit) ▷ Ebc ≫
        (leftUnitor Ebc).hom ≫ rouquierPower (T.dot j hbc) q
    else 0 := by
  rw [T.distinctMixedBraidOuterMate_monomial i j hab hbc hcd]
  simp only [Category.assoc]
  have hw := congrArg (fun z => Ebc ◁ z) ((T.loc i hfc hcd).cupD_capL hh hn)
  rw [TwoSupercategory.whiskerLeft_comp (R := k)] at hw
  change Ebc ◁ ((T.adj i hcd).unit ≫ rouquierPower (T.dot i hcd) n ▷ Fcd) ≫
      Ebc ◁ (T.loc i hfc hcd).capL =
    Ebc ◁ (if n = (-D.h i c - 1).toNat then 𝟙 _ else 0) at hw
  rw [reassoc_of% hw]
  split_ifs
  · rw [TwoSupercategory.whiskerLeft_id (R := k)]
    simp only [Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  · rw [TwoSupercategory.whiskerLeft_zero (R := k)]
    simp only [Limits.zero_comp, Limits.comp_zero]

end RouquierFamily
end OddMath.SKM
