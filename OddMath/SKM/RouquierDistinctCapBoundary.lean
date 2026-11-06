import OddMath.SKM.RouquierDistinctMixedBraid
import OddMath.SKM.RouquierCurl

/-! # Zero-height principal cap tests

The height-zero boundary in Brundan–Ellis Lemma 7.1, `pf_a`.
The equal-colour mate followed by the raw left cap becomes the prescribed
right counit. For disconnected colours the correction sum is empty and
the rectangular cap pitchfork and quadratic relation evaluate the test.
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
  (T : RouquierFamily (k := k) (B := B) D)

/-- The raw zero-height cap boundary has no normalization scalar. -/
theorem sig_capL_of_zero {i : I} {a b c : X}
    (hab : a + D.α i = b) (hbc : b + D.α i = c) (hh : D.h i b = 0) :
    (T.loc i hab hbc).sig ≫ (T.loc i hab hbc).capL = (T.adj i hab).counit := by
  have h := (T.loc i hab hbc).sig_powComp_capL_of_le (n := 0) (by omega)
  simpa only [hh, neg_zero, Nat.cast_zero, ↓reduceIte, rouquierPower_zero,
    TwoSupercategory.id_whiskerRight (R := k), Category.id_comp] using h

variable {Sc : Scalars D k} (M : RouquierMulticolour T Sc)
  {i j : I} (hne : i ≠ j) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)

include M hne in
/-- The second mixed word at zero shifted height for disconnected colours. -/
theorem distinctMixedBraidRight_cap_of_zero_disconnected
    (hh : D.h i c = 0) (hd : D.d i j = 0) :
    T.distinctMixedBraidRight i j hab haf hbc hfc hcd ≫
      T.E j hbc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor (T.E j hbc)).hom =
    (Sc.t i j : k) • ((T.adj i hab).counit ▷ T.E j hbc ≫
      (leftUnitor (T.E j hbc)).hom) := by
  have hc : crossMate (T.adj i hfc) (T.adj i hcd)
      (T.cross i i hfc hcd hfc hcd) ≫ (T.loc i hfc hcd).capL =
      (T.adj i hfc).counit := by
    rw [crossMate_eq_rouquierMate]
    exact T.sig_capL_of_zero hfc hcd hh
  have hw := congrArg (fun z => T.E j hbc ◁ z) hc
  rw [TwoSupercategory.whiskerLeft_comp (R := k)] at hw
  unfold distinctMixedBraidRight
  simp only [Category.assoc]
  rw [reassoc_of% hw]
  rw [crossMate_pitchfork_cap]
  simp only [Iso.inv_hom_id_assoc]
  rw [← reassoc_of% (TwoSupercategory.whiskerLeft_comp (R := k) (T.F i hab)
      (T.cross j i hab hbc haf hfc) (T.cross i j haf hfc hab hbc)),
    M.quadZero j i hne.symm ((D.d_eq_zero_iff i j).mp hd) hab hbc haf hfc]
  simp only [TwoSupercategory.whiskerLeft_smul (R := k),
    TwoSupercategory.whiskerLeft_id (R := k), Linear.comp_smul, Linear.smul_comp,
    Category.id_comp, Iso.hom_inv_id_assoc]
  rw [Sc.t_symm_of_d_eq_zero i j hd]

include M hne haf in
/-- The correction vanishes for disconnected colours, so the same
zero-height cap value is the first mixed word's principal test. -/
theorem distinctMixedBraidLeft_cap_of_zero_disconnected
    (hh : D.h i c = 0) (hd : D.d i j = 0) :
    T.distinctMixedBraidLeft i j hab hbc hbe hcd hed ≫
      T.E j hbc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor (T.E j hbc)).hom =
    (Sc.t i j : k) • ((T.adj i hab).counit ▷ T.E j hbc ≫
      (leftUnitor (T.E j hbc)).hom) := by
  have hn : D.dn i j = 0 := by have := D.dn_cast hne; omega
  have hb := T.distinctMixedBraid_correction i j hab haf hbc hbe hfc hcd hed M hne
  simp only [hn, Finset.range_zero, Finset.sum_empty, add_zero] at hb
  rw [sub_eq_zero] at hb
  rw [hb]
  exact T.distinctMixedBraidRight_cap_of_zero_disconnected M hne hab haf hbc hfc hcd hh hd
end RouquierFamily
end OddMath.SKM
