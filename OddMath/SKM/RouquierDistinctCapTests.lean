import OddMath.SKM.RouquierDistinctCapDetection
import OddMath.SKM.RouquierInverseRelations
import OddMath.SKM.RouquierDistinctMixedBraid

/-!
# The inverse-crossing side of the distinct cap tests

Brundan–Ellis, Lemma 7.1: the right-hand cap word cancels the prescribed
distinct sideways crossing before applying the inverse-defined local
cap. Its principal test vanishes at negative height; its finite cup
columns are exactly the boundary Kronecker coefficients. The left-hand
crossing-cap tests are not assumed or proved here.
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
  {a₀ a b c d : X} (h₀ : a₀ + D.α i = a)
  (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d)

/-- The inverse of the specified sideways source chart, followed by the
raw inverse-defined cap. This retains the exact map tested by Lemma 7.1. -/
def distinctCapRight : (T.E i hi ≫ T.E j hij) ≫ T.F i hji ⟶ T.E j hj := by
  letI := T.distinctCapSource_isIso M hne hi hj hij hji
  exact inv (T.distinctCapSource hi hj hij hji) ≫
    (T.loc i h₀ hi).capL ▷ T.E j hj ≫ (leftUnitor (T.E j hj)).hom

/-- Undoing the prescribed chart leaves exactly the local cap. -/
theorem distinctCapSource_right :
    T.distinctCapSource hi hj hij hji ≫ T.distinctCapRight M hne h₀ hi hj hij hji =
      (T.loc i h₀ hi).capL ▷ T.E j hj ≫ (leftUnitor (T.E j hj)).hom := by
  have := T.distinctCapSource_isIso M hne hi hj hij hji
  unfold distinctCapRight
  rw [IsIso.hom_inv_id_assoc]

/-- The principal right-hand test of Lemma 7.1 at strictly negative height. -/
theorem distinctCapRight_principal_of_neg (hh : D.h i a < 0) :
    (T.loc i h₀ hi).sig ▷ T.E j hj ≫ T.distinctCapSource hi hj hij hji ≫
      T.distinctCapRight M hne h₀ hi hj hij hji = 0 := by
  rw [T.distinctCapSource_right M hne h₀ hi hj hij hji,
    ← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
    (T.loc i h₀ hi).sig_capL hh, TwoSupercategory.zero_whiskerRight (R := k),
    Limits.zero_comp]

/-- Every finite right-hand cup-column test is the raw boundary
Kronecker coefficient. No scalar or cap compatibility is assumed. -/
theorem distinctCapRight_column_of_neg (hh : D.h i a < 0) (n : ℕ)
    (hn : n < (-D.h i a).toNat) :
    (T.loc i h₀ hi).cupD n ▷ T.E j hj ≫ T.distinctCapSource hi hj hij hji ≫
      T.distinctCapRight M hne h₀ hi hj hij hji =
    if n = (-D.h i a - 1).toNat then (leftUnitor (T.E j hj)).hom else 0 := by
  rw [T.distinctCapSource_right M hne h₀ hi hj hij hji,
    ← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
    (T.loc i h₀ hi).cupD_capL hh hn]
  split_ifs
  · rw [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
  · rw [TwoSupercategory.zero_whiskerRight (R := k), Limits.zero_comp]

/-- The second mixed-braid word vanishes after the negative-height cap
on its final equal-colour mate. This is the vanishing term in the
principal left-hand cap test of Lemma 7.1. -/
theorem distinctMixedBraidRight_cap_of_neg {f : X}
    (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
    (hfc : f + D.α i = c) (hcd : c + D.α i = d) (hh : D.h i c < 0) :
    T.distinctMixedBraidRight i j hab haf hbc hfc hcd ≫
      T.E j hbc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor (T.E j hbc)).hom = 0 := by
  have hc : crossMate (T.adj i hfc) (T.adj i hcd)
      (T.cross i i hfc hcd hfc hcd) ≫ (T.loc i hfc hcd).capL = 0 := by
    rw [crossMate_eq_rouquierMate]
    exact (T.loc i hfc hcd).sig_capL hh
  have hw := congrArg (fun z => T.E j hbc ◁ z) hc
  rw [TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_zero (R := k)] at hw
  unfold distinctMixedBraidRight
  simp only [Category.assoc]
  rw [reassoc_of% hw]
  simp only [Limits.zero_comp, Limits.comp_zero]

end RouquierFamily
end OddMath.SKM
