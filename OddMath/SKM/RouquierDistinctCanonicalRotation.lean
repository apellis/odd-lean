import OddMath.SKM.RouquierDistinctCapColumnReduction
import OddMath.SKM.RouquierDistinctCapInverseChart
import OddMath.SKM.RouquierDistinctLeftRotation
import OddMath.SKM.RouquierFTriangle

/-!
# Canonical rotation from the exact raw cap identity

The inverse-defined cap identity is transported to the canonical
normalized left adjunctions using their explicit scalar units. The
right mate and its inverse remain the prescribed maps throughout.
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
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c d : X} (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d)

/-- The raw cap identity gives invertibility of the actual canonical
left mate, with no replacement of its crossing, cup, cap or inverse. -/
theorem leftCrossMate_isIso_of_raw_cap (u : kˣ)
    (hraw : T.distinctCapLeft hi hj hij hji (sub_add_cancel c (D.α i)) =
      (u : k) • T.distinctCapRight M hne (sub_add_cancel a (D.α i)) hi hj hij hji) :
    IsIso (leftCrossMate (T.leftAdjoints.adjL i hi) (T.leftAdjoints.adjL i hji)
      (T.cross j i hi hij hj hji)) := by
  have := M.invNe i j hne hj hji hi hij
  let s := crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)
  have hs : s ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
    crossMate_mem (T.adj i hi) (T.adj i hji) _ _ _ (T.cross_mem i j hj hji hi hij)
  have hl : inv s ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
    inv_mem (asIso s) hs
  let q : kˣ := (T.leftAdjScalar i c)⁻¹ * u * T.leftAdjScalar i a
  apply leftCrossMate_isIso_of_cap_pitchfork
    (T.leftAdjoints.adjL i hi) (T.leftAdjoints.adjL i hji)
    (T.cross j i hi hij hj hji) (inv s) s hl q
    (IsIso.inv_hom_id s) (IsIso.hom_inv_id s)
  rw [T.distinctCapRight_eq_inverseMate M hne (sub_add_cancel a (D.α i)) hi hj hij hji] at hraw
  have hr := congrArg (fun z => (associator (T.E i hi) (T.E j hij) (T.F i hji)).inv ≫ z) hraw
  simp only [distinctCapLeft, Linear.comp_smul, Iso.inv_hom_id_assoc] at hr
  change (associator (T.E i hi) (T.E j hij) (T.F i hji)).inv ≫
      T.cross j i hi hij hj hji ▷ T.F i hji ≫
      (associator (T.E j hj) (T.E i hji) (T.F i hji)).hom ≫
      T.E j hj ◁ ((↑((T.leftAdjScalar i c)⁻¹) : k) • T.leftCap i hji) ≫
      (rightUnitor (T.E j hj)).hom =
    (q : k) • (T.E i hi ◁ inv s ≫
      (associator (T.E i hi) (T.F i hi) (T.E j hj)).inv ≫
      ((↑((T.leftAdjScalar i a)⁻¹) : k) • T.leftCap i hi) ▷ T.E j hj ≫
      (leftUnitor (T.E j hj)).hom)
  simp only [TwoSupercategory.whiskerLeft_smul (R := k),
    TwoSupercategory.smul_whiskerRight (R := k), Linear.smul_comp, Linear.comp_smul,
    smul_smul]
  rw [show (associator (T.E i hi) (T.E j hij) (T.F i hji)).inv ≫
      T.cross j i hi hij hj hji ▷ T.F i hji ≫
      (associator (T.E j hj) (T.E i hji) (T.F i hji)).hom ≫
      T.E j hj ◁ T.leftCap i hji ≫ (rightUnitor (T.E j hj)).hom =
      (u : k) • (T.E i hi ◁ inv s ≫
        (associator (T.E i hi) (T.F i hi) (T.E j hj)).inv ≫
        T.leftCap i hi ▷ T.E j hj ≫ (leftUnitor (T.E j hj)).hom) from hr,
    smul_smul]
  congr 1
  simp only [q, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]

end RouquierFamily
end OddMath.SKM
