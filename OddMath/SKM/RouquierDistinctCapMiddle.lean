import OddMath.SKM.RouquierDistinctConnectedCapBoundary

/-! # The intermediate-height distinct cap window

Brundan–Ellis Lemma 7.1 (7.3), for `0 < h_i(b) < d_ij`.
Precomposition by the inverse-defined equal-colour left mate kills the
low source powers. The shifted left cap kills high source powers; only
the boundary exponent survives. Raw caps retain the height-parity sign.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Eab" => T.E i hab
local notation "Ebc" => T.E j hbc
local notation "Ecd" => T.E i hcd
local notation "Fab" => T.F i hab

/-- Low source powers are killed by the prescribed left mate,
independently of the middle and final dot exponents. -/
theorem distinctMixedBraidOuterMate_source_zero (hh : 0 ≤ D.h i b)
    (s q n : ℕ) (hs : s < (D.h i b).toNat) :
    (T.loc i hab hbe).sigL ▷ Ebc ≫ T.distinctMixedBraidOuterMate i j hab hbc hcd
      (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
        Eab ◁ (rouquierPower (T.dot j hbc) q ▷ Ecd) ≫
        Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) n) = 0 := by
  rw [T.distinctMixedBraidOuterMate_monomial i j hab hbc hcd]
  change (T.loc i hab hbe).sigL ▷ Ebc ≫ (T.loc i hab hbe).capD s ▷ Ebc ≫ _ = 0
  rw [← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
    (T.loc i hab hbe).sigL_capD hh hs, TwoSupercategory.zero_whiskerRight (R := k), Limits.zero_comp]

include hne in
/-- After both cap tests only the exact intermediate source exponent
survives among leading correction monomials. -/
theorem distinctMixedBraidOuterMate_middle_leading
    (h0 : 0 < D.h i b) (h1 : D.h i b < D.d i j)
    (s : ℕ) (hs : s < D.dn i j) :
    -((T.loc i hab hbe).sigL ▷ Ebc ≫ T.distinctMixedBraidOuterMate i j hab hbc hcd
      (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
        Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (D.dn i j - 1 - s)) ≫
      Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom) =
    if s = (D.h i b).toNat then (T.loc i hab hbe).capL ▷ Ebc ≫ (leftUnitor Ebc).hom else 0 := by
  have hw : D.h i c = D.h i b - D.d i j := by rw [← hbc]; simp [Datum.d, map_add]
  have hd := D.dn_cast hne
  have hh : (↑((D.h i b).toNat) : ℤ) = D.h i b := Int.toNat_of_nonneg h0.le
  have hc : D.h i c < 0 := by omega
  by_cases hlow : s < (D.h i b).toNat
  · have hz := T.distinctMixedBraidOuterMate_source_zero hab hbc hbe hcd h0.le s 0
      (D.dn i j - 1 - s) hlow
    simp only [rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k),
      TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp] at hz
    rw [← Category.assoc, ← Category.assoc, hz, Limits.zero_comp, Limits.zero_comp,
      neg_zero, ite_eq_right (by omega)]
  · have hz := T.distinctMixedBraidOuterMate_monomial_cap i j hab hbc hcd hfc hc s 0
      (D.dn i j - 1 - s) (by omega)
    simp only [rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k),
      TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id] at hz
    rw [hz]
    by_cases heq : s = (D.h i b).toNat
    · subst s
      rw [ite_eq_left (by omega), ite_eq_left rfl]
      change -((T.loc i hab hbe).sigL ▷ Ebc ≫ (T.loc i hab hbe).capD (D.h i b).toNat ▷ Ebc ≫
        (leftUnitor Ebc).hom) = _
      rw [← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
        ← Preadditive.neg_comp, ← TwoSupercategory.neg_whiskerRight (R := k)]
      rw [(T.loc i hab hbe).capL_of_nonneg h0.le]
    · rw [ite_eq_right (by omega), Limits.comp_zero, neg_zero, ite_eq_right heq]

include hne in
/-- Every interior correction is killed at one of its two endpoints
in the intermediate positive-height window. -/
theorem distinctMixedBraidOuterMate_middle_interior
    (h0 : 0 < D.h i b) (h1 : D.h i b < D.d i j)
    (p q s : ℕ) (hp : 0 < p ∧ p < D.dn i j) (hs : s < p) :
    (T.loc i hab hbe).sigL ▷ Ebc ≫ T.distinctMixedBraidOuterMate i j hab hbc hcd
      (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
        Eab ◁ (rouquierPower (T.dot j hbc) q ▷ Ecd) ≫
        Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (p - 1 - s)) ≫
      Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom = 0 := by
  have hw : D.h i c = D.h i b - D.d i j := by rw [← hbc]; simp [Datum.d, map_add]
  have hd := D.dn_cast hne
  have hh : (↑((D.h i b).toNat) : ℤ) = D.h i b := Int.toNat_of_nonneg h0.le
  have hc : D.h i c < 0 := by omega
  by_cases hlow : s < (D.h i b).toNat
  · rw [← Category.assoc, ← Category.assoc,
      T.distinctMixedBraidOuterMate_source_zero hab hbc hbe hcd h0.le s q (p - 1 - s) hlow,
      Limits.zero_comp, Limits.zero_comp]
  · rw [T.distinctMixedBraidOuterMate_monomial_cap i j hab hbc hcd hfc hc s q
      (p - 1 - s) (by omega), ite_eq_right (by omega), Limits.comp_zero]

include M hne haf in
/-- The raw cap-window identity (7.3), before converting to the source's
normalized left cap. Its height-parity coefficient is retained. -/
theorem distinctMixedBraidLeft_cap_middle
    (h0 : 0 < D.h i b) (h1 : D.h i b < D.d i j) :
    -((T.loc i hab hbe).sigL ▷ Ebc ≫ T.distinctMixedBraidLeft i j hab hbc hbe hcd hed ≫
      Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom) =
    (zsign k (D.parity i * (D.h i b).toNat) * (Sc.t i j : k)) •
      ((T.loc i hab hbe).capL ▷ Ebc ≫ (leftUnitor Ebc).hom) := by
  have hw : D.h i c = D.h i b - D.d i j := by rw [← hbc]; simp [Datum.d, map_add]
  have hd := D.dn_cast hne
  have hc : D.h i c < 0 := by omega
  have hn : (D.h i b).toNat < D.dn i j := by omega
  have hb := congrArg (fun z => -((T.loc i hab hbe).sigL ▷ Ebc ≫ z ≫ Ebc ◁ (T.loc i hfc hcd).capL ≫
      (rightUnitor Ebc).hom))
    (T.distinctMixedBraid_correction i j hab haf hbc hbe hfc hcd hed M hne)
  simp only [Preadditive.sub_comp,
    T.distinctMixedBraidRight_cap_of_neg hab haf hbc hfc hcd hc, sub_zero] at hb
  rw [hb]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
    Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul, neg_add_rev,
    ← Finset.sum_neg_distrib, ← smul_neg]
  have hi : (∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
      ∑ s ∈ Finset.range p,
        (zsign k (D.parity i * s) * Sc.s i j p q) •
          -((T.loc i hab hbe).sigL ▷ Ebc ≫ T.distinctMixedBraidOuterMate i j hab hbc hcd
            (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
              Eab ◁ (rouquierPower (T.dot j hbc) q ▷ Ecd) ≫
              Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (p - 1 - s)) ≫
            Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q _
    apply Finset.sum_eq_zero
    intro s hs
    rw [T.distinctMixedBraidOuterMate_middle_interior hne hab hbc hbe hfc hcd h0 h1
      p q s (Finset.mem_Ioo.mp hp) (Finset.mem_range.mp hs), neg_zero, smul_zero]
  rw [hi, zero_add]
  rw [Finset.sum_eq_single (D.h i b).toNat]
  · rw [T.distinctMixedBraidOuterMate_middle_leading hne hab hbc hbe hfc hcd h0 h1 _ hn,
      ite_eq_left rfl]
  · intro s hs hsne
    rw [T.distinctMixedBraidOuterMate_middle_leading hne hab hbc hbe hfc hcd h0 h1 _
      (Finset.mem_range.mp hs), ite_eq_right hsne, smul_zero]
  · intro hs
    exact False.elim (hs (Finset.mem_range.mpr hn))
end RouquierFamily
end OddMath.SKM
