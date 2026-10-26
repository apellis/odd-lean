import OddMath.SKM.RouquierInverseRelations
import OddMath.SKM.RouquierMateSectors

/-!
# Signed dot slides through the rightward crossing

This ports `RouqLoc.powComp_sig` (`Categorification/TwoRep/RouqGrass.lean`, Brundan
(2.3) iterated), `cupL_powComp_sig` (Brundan (3.14)) and the two finite expansions of
Corollary 3.5, (3.18) (`sig_capL_expansion`, `cupL_sig_expansion`, from
`Categorification/TwoRep/RouqCurl.lean`) to super Rouquier data. Its downstream
consumer is the zigzag obligation `RouquierFamily.LeftZigzags` of
`RouquierLeftCupCap.lean`.

With `s = (-1)^p` the slide of the mate reads `X σ = s σ Y - s ε η`
(diagrammatic order, `X = F ◁ x₁`, `Y = x₂ ▷ F`), so `m` dots pass with
`X^m σ = s^m σ Y^m - ∑_{j<m} s^(m-j) X^j ε η Y^(m-1-j)`. In the even case `s = 1` and
this is Brundan's formula. The expansions (3.18) are sign-free: they follow from the
inverse-matrix relations alone.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

namespace SuperRouquierLoc
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {p : ZMod 2} {h : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- One dot through the rightward crossing. -/
theorem dot_sig :
    F₁ ◁ x₁ ≫ L.sig = koszulSign p p • (L.sig ≫ x₂ ▷ F₂) -
      koszulSign p p • (L.capD 0 ≫ L.cupD 0) := by
  have hs := L.mate_slide
  have h0 : L.capD 0 ≫ L.cupD 0 = A₁.counit ≫ A₂.unit := by
    simp only [capD, cupD, rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
      TwoSupercategory.id_whiskerRight (R := k), Category.id_comp, Category.comp_id]
  rw [h0, ← hs, sig, smul_sub, smul_smul, koszulSign_mul_self, one_smul]
  abel

theorem cupD_succ (n : ℕ) : L.cupD n ≫ x₂ ▷ F₂ = L.cupD (n + 1) := by
  rw [cupD, Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k)]
  rfl

/-- `m` dots through the rightward crossing, with Koszul signs. -/
theorem powComp_sig (m : ℕ) :
    F₁ ◁ rouquierPower x₁ m ≫ L.sig =
      (koszulSign p p ^ m) • (L.sig ≫ rouquierPower x₂ m ▷ F₂) -
        ∑ j ∈ Finset.range m,
          (koszulSign p p ^ (m - j)) • (L.capD j ≫ L.cupD (m - 1 - j)) := by
  induction m with
  | zero =>
    simp only [rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
      TwoSupercategory.id_whiskerRight (R := k), Category.id_comp, Category.comp_id,
      pow_zero, one_smul, Finset.range_zero, Finset.sum_empty, sub_zero]
  | succ m ih =>
    rw [rouquierPower_succ, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
      L.dot_sig, Preadditive.comp_sub, Preadditive.comp_zsmul, Preadditive.comp_zsmul,
      ← Category.assoc, ih, Preadditive.sub_comp, Preadditive.sum_comp,
      Preadditive.zsmul_comp, Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
      ← rouquierPower_succ, Finset.sum_range_succ]
    have hlast : F₁ ◁ rouquierPower x₁ m ≫ L.capD 0 ≫ L.cupD 0 =
        L.capD m ≫ L.cupD (m + 1 - 1 - m) := by
      rw [show m + 1 - 1 - m = 0 by omega, ← Category.assoc]
      congr 1
      simp only [capD, rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
        Category.id_comp]
    have hsum : ∑ j ∈ Finset.range m,
        (koszulSign p p ^ (m - j)) • (L.capD j ≫ L.cupD (m - 1 - j)) ≫ x₂ ▷ F₂ =
        ∑ j ∈ Finset.range m,
          (koszulSign p p ^ (m - j)) • (L.capD j ≫ L.cupD (m + 1 - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [Category.assoc, L.cupD_succ, show m - 1 - j + 1 = m + 1 - 1 - j by omega]
    simp only [Preadditive.zsmul_comp] at hsum ⊢
    rw [hsum, hlast, smul_sub, Finset.smul_sum]
    simp only [smul_smul]
    have hidx : ∀ j ∈ Finset.range m,
        (koszulSign p p * koszulSign p p ^ (m - j)) • (L.capD j ≫ L.cupD (m + 1 - 1 - j)) =
          (koszulSign p p ^ (m + 1 - j)) • (L.capD j ≫ L.cupD (m + 1 - 1 - j)) := by
      intro j hj
      have := Finset.mem_range.mp hj
      rw [← pow_succ', show m - j + 1 = m + 1 - j by omega]
    rw [Finset.sum_congr rfl hidx, show m + 1 - m = 1 by omega, pow_one, ← pow_succ']
    abel

/-- Brundan (3.14): a leftward cup with fewer than `h` dots is killed by the crossing. -/
theorem cupL_powComp_sig (hh : 0 < h) {m : ℕ} (hm : m < h.toNat) :
    L.cupL ≫ F₁ ◁ rouquierPower x₁ m ≫ L.sig = 0 := by
  rw [L.powComp_sig, Preadditive.comp_sub, Preadditive.comp_zsmul, ← Category.assoc,
    cupL_sig hh, Limits.zero_comp, smul_zero, zero_sub, Preadditive.comp_sum, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [Preadditive.comp_zsmul, ← Category.assoc, cupL_capD hh (by omega), ite_eq_right (by omega),
    Limits.zero_comp, smul_zero]

omit [TwoSupercategory k B] in
theorem cw_of_neg_of_gt {k : ℤ} (hk : k < 0) (hk' : -h - 1 < k) :
    L.cw k = -(L.cupN (-k - 1).toNat ≫ L.capD h.toNat) := by
  rw [cw, ite_eq_right (not_le.mpr hk), ite_eq_left hk']

omit [TwoSupercategory k B] in
theorem cw_of_neg_of_eq {k : ℤ} (hk : k < 0) (hk' : k = -h - 1) : L.cw k = 𝟙 _ := by
  rw [cw, ite_eq_right (not_le.mpr hk), ite_eq_right (by omega), ite_eq_left hk']

omit [TwoSupercategory k B] in
theorem ccw_of_neg_of_gt {k : ℤ} (hk : k < 0) (hk' : h - 1 < k) :
    L.ccw k = -(L.cupD (-h).toNat ≫ L.capN (-k - 1).toNat) := by
  rw [ccw, ite_eq_right (not_le.mpr hk), ite_eq_left hk']

omit [TwoSupercategory k B] in
theorem ccw_of_neg_of_eq {k : ℤ} (hk : k < 0) (hk' : k = h - 1) : L.ccw k = 𝟙 _ := by
  rw [ccw, ite_eq_right (not_le.mpr hk), ite_eq_right (by omega), ite_eq_left hk']

omit [TwoSupercategory k B] in
/-- Brundan, Corollary 3.5, (3.18), first identity. -/
theorem sig_capL_expansion :
    L.sig ≫ L.capL = ∑ n ∈ Finset.range (h + 1).toNat, L.capD n ≫ L.cw (-(n : ℤ) - 1) := by
  rcases lt_or_ge h 0 with hh | hh
  · rw [sig_capL hh, Int.toNat_of_nonpos (by omega : h + 1 ≤ 0)]
    simp
  · have hN : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh
    rw [capL_of_nonneg hh, Preadditive.comp_neg, ← Category.assoc,
      sig_sigL_of_nonneg hh, Preadditive.sub_comp, Preadditive.sum_comp, Category.id_comp,
      show (h + 1).toNat = h.toNat + 1 by omega, Finset.sum_range_succ,
      show -(h.toNat : ℤ) - 1 = -h - 1 by omega,
      L.cw_of_neg_of_eq (by omega) rfl, Category.comp_id]
    have hs : ∑ n ∈ Finset.range h.toNat, L.capD n ≫ L.cw (-(n : ℤ) - 1) =
        -(∑ n ∈ Finset.range h.toNat, (L.capD n ≫ L.cupN n) ≫ L.capD h.toNat) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_range.mp hn
      rw [L.cw_of_neg_of_gt (by omega) (by omega),
        show -(-(n : ℤ) - 1) - 1 = n by ring, Int.toNat_natCast,
        Preadditive.comp_neg, Category.assoc]
    rw [hs]
    abel

omit [TwoSupercategory k B] in
/-- Brundan, Corollary 3.5, (3.18), second identity. -/
theorem cupL_sig_expansion :
    L.cupL ≫ L.sig = -(∑ n ∈ Finset.range (-h + 1).toNat, L.ccw (-(n : ℤ) - 1) ≫ L.cupD n) := by
  rcases lt_or_ge 0 h with hh | hh
  · rw [cupL_sig hh, Int.toNat_of_nonpos (by omega : -h + 1 ≤ 0)]
    simp
  · have hN : ((-h).toNat : ℤ) = -h := Int.toNat_of_nonneg (by omega)
    rw [cupL_of_nonpos hh, Category.assoc, sigL_sig_of_nonpos hh, Preadditive.comp_sub,
      Preadditive.comp_sum, Category.comp_id,
      show (-h + 1).toNat = (-h).toNat + 1 by omega, Finset.sum_range_succ,
      show -((-h).toNat : ℤ) - 1 = h - 1 by omega,
      L.ccw_of_neg_of_eq (by omega) rfl, Category.id_comp]
    have hs : ∑ n ∈ Finset.range (-h).toNat, L.ccw (-(n : ℤ) - 1) ≫ L.cupD n =
        -(∑ n ∈ Finset.range (-h).toNat, L.cupD (-h).toNat ≫ L.capN n ≫ L.cupD n) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_range.mp hn
      rw [L.ccw_of_neg_of_gt (by omega) (by omega),
        show -(-(n : ℤ) - 1) - 1 = n by ring, Int.toNat_natCast,
        Preadditive.neg_comp, Category.assoc]
    rw [hs]
    abel

end SuperRouquierLoc
end OddMath.SKM
