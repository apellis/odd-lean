import OddMath.SKM.RouquierDistinctCapBoundary
import OddMath.SKM.RouquierDistinctCapTests
import OddMath.SKM.RouquierDistinctCapMonomials

/-! # Connected zero-height cap boundary

Brundan–Ellis Lemma 7.1, `pf_a`, at height zero. Among the bent
correction monomials only the leading term with zero source dots
survives, with coefficient exactly `t_ij`.
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

include M hne haf in
/-- The connected height-zero principal test retains the prescribed
nonzero leading parameter and no interior correction terms. -/
theorem distinctMixedBraidLeft_cap_of_zero_connected
    (hh : D.h i b = 0) (hd : D.d i j ≠ 0) :
    T.distinctMixedBraidLeft i j hab hbc hbe hcd hed ≫
      Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom =
    (Sc.t i j : k) • ((T.adj i hab).counit ▷ Ebc ≫ (leftUnitor Ebc).hom) := by
  have hdn := D.dn_cast hne
  have hdpos : 0 < D.dn i j := by have := D.d_nonneg hne; omega
  have hc : D.h i c = -(D.dn i j : ℤ) := by
    rw [← hbc, Datum.h, map_add]
    change D.h i b + D.h i (D.α j) = _
    rw [hh, zero_add]
    rw [hdn, Datum.d, neg_neg]
  have hcneg : D.h i c < 0 := by omega
  have hcount : (-D.h i c).toNat = D.dn i j := by rw [hc, neg_neg, Int.toNat_natCast]
  have hlast : (-D.h i c - 1).toNat = D.dn i j - 1 := by omega
  have heval (s q n : ℕ) (hn : n < D.dn i j) :=
    T.distinctMixedBraidOuterMate_monomial_cap i j hab hbc hcd hfc hcneg s q n
      (by rwa [hcount])
  have hleading (s : ℕ) (hs : s < D.dn i j) :
      T.distinctMixedBraidOuterMate i j hab hbc hcd
        (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
          Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (D.dn i j - 1 - s)) ≫
        Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom =
      if s = 0 then (T.adj i hab).counit ▷ Ebc ≫ (leftUnitor Ebc).hom else 0 := by
    have hz := heval s 0 (D.dn i j - 1 - s) (by omega)
    rw [hlast] at hz
    by_cases hs0 : s = 0
    · subst s
      simpa only [Nat.sub_zero, ↓reduceIte, rouquierPower_zero,
        TwoSupercategory.id_whiskerRight (R := k),
        TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id] using hz
    · have hn : D.dn i j - 1 - s ≠ D.dn i j - 1 := by omega
      simpa only [ite_eq_right hn, ite_eq_right hs0, rouquierPower_zero,
        TwoSupercategory.id_whiskerRight (R := k),
        TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp] using hz
  have hb := congrArg (fun z => z ≫ Ebc ◁ (T.loc i hfc hcd).capL ≫
      (rightUnitor Ebc).hom)
    (T.distinctMixedBraid_correction i j hab haf hbc hbe hfc hcd hed M hne)
  simp only [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.sum_comp,
    Linear.smul_comp] at hb
  rw [T.distinctMixedBraidRight_cap_of_neg hab haf hbc hfc hcd hcneg, sub_zero] at hb
  rw [hb]
  have hinterior : (∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
      ∑ s ∈ Finset.range p,
      (zsign k (D.parity i * s) * Sc.s i j p q) •
        (T.distinctMixedBraidOuterMate i j hab hbc hcd
          (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
            Eab ◁ (rouquierPower (T.dot j hbc) q ▷ Ecd) ≫
            Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (p - 1 - s)) ≫
          Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    apply Finset.sum_eq_zero
    intro s hs
    have hp' := Finset.mem_Ioo.mp hp
    have hs' := Finset.mem_range.mp hs
    rw [heval s q (p - 1 - s) (by omega), hlast, ite_eq_right (by omega), smul_zero]
  rw [hinterior, add_zero]
  rw [Finset.sum_eq_single 0]
  · rw [hleading 0 hdpos, ite_eq_left rfl, Nat.cast_zero, mul_zero, zsign, ite_eq_right (by decide), one_mul]
  · intro s hs hs0
    rw [hleading s (Finset.mem_range.mp hs), ite_eq_right hs0, smul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hdpos))

include M hne haf in
/-- The complete raw principal cap value at height zero, including both
connected and disconnected distinct colours. -/
theorem distinctMixedBraidLeft_cap_of_zero (hh : D.h i b = 0) :
    T.distinctMixedBraidLeft i j hab hbc hbe hcd hed ≫
      Ebc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor Ebc).hom =
    (Sc.t i j : k) • ((T.adj i hab).counit ▷ Ebc ≫ (leftUnitor Ebc).hom) := by
  by_cases hd : D.d i j = 0
  · have hc : D.h i c = 0 := by
      rw [← hbc, Datum.h, map_add]
      change D.h i b + D.h i (D.α j) = 0
      rw [hh, zero_add]
      simpa only [Datum.d, neg_eq_zero] using hd
    exact T.distinctMixedBraidLeft_cap_of_zero_disconnected M hne
      hab haf hbc hbe hfc hcd hed hc hd
  · exact T.distinctMixedBraidLeft_cap_of_zero_connected M hne
      hab haf hbc hbe hfc hcd hed hh hd

/-- The inverse-crossing side of the same principal test reduces to
the unscaled right counit at height zero. -/
theorem distinctCapRight_principal_of_zero (hh : D.h i b = 0) :
    (T.loc i hab hbe).sig ▷ Ebc ≫ T.distinctCapSource hbe hbc hed hcd ≫
      T.distinctCapRight M hne hab hbe hbc hed hcd =
    (T.adj i hab).counit ▷ Ebc ≫ (leftUnitor Ebc).hom := by
  rw [T.distinctCapSource_right M hne hab hbe hbc hed hcd,
    ← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
    T.sig_capL_of_zero hab hbe hh]

end RouquierFamily
end OddMath.SKM
