import OddMath.SKM.RouquierLeftCupCap

/-!
# Inverse-matrix relations of super Rouquier data

This ports Brundan, *On the definition of Kac–Moody 2-category*, Lemma 3.1
((3.3), (3.5)–(3.9)), from `Categorification/TwoRep/RouqSl2.lean` (section `Lemma31`)
to super Rouquier data. The identities are formal consequences of the two inverse
matrices of the mate `σ : F E → E F`, so no Koszul sign enters. They are the first
inputs of the zigzag obligation `RouquierFamily.LeftZigzags` of
`RouquierLeftCupCap.lean`, its downstream consumer.

The counter-clockwise and clockwise bubbles `ccw`, `cw` with `k ∈ ℤ` dots use the
even formulas for negative `k`. Only the inverse-matrix values (`ccw_self`, `ccw_of_lt`,
`cw_self`, `cw_of_lt`) are proved here; no infinite Grassmannian relation is claimed.
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

/-- The rightward crossing `σ : F E → E F`, the mate of the crossing. -/
def sig (_L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h) : F₁ ≫ E₁ ⟶ E₂ ≫ F₂ :=
  rouquierMate A₁ A₂ t

/-- The counter-clockwise bubble with `k ∈ ℤ` dots. -/
def ccw (k : ℤ) : 𝟙 b ⟶ 𝟙 b :=
  if 0 ≤ k then L.cupL ≫ L.capD k.toNat
  else if h - 1 < k then -(L.cupD (-h).toNat ≫ L.capN (-k - 1).toNat)
  else if k = h - 1 then 𝟙 _ else 0

/-- The clockwise bubble with `k ∈ ℤ` dots. -/
def cw (k : ℤ) : 𝟙 b ⟶ 𝟙 b :=
  if 0 ≤ k then L.cupD k.toNat ≫ L.capL
  else if -h - 1 < k then -(L.cupN (-k - 1).toNat ≫ L.capD h.toNat)
  else if k = -h - 1 then 𝟙 _ else 0

variable {L}

omit [TwoSupercategory k B] in
theorem sigL_of_nonneg (hh : 0 ≤ h) : L.sigL = -(L.invPos hh).f' := by
  rw [sigL, dite_eq_left hh]

omit [TwoSupercategory k B] in
theorem sigL_of_nonpos (hh : h ≤ 0) : L.sigL = -(L.invNeg hh).f' := by
  rw [sigL]
  split_ifs with h'
  · congr 1
    calc (L.invPos h').f' = (L.invPos h').f' ≫ (L.sig ≫ (L.invNeg hh).f') := by
          rw [sig, (L.invNeg hh).ff, Category.comp_id]
      _ = ((L.invPos h').f' ≫ L.sig) ≫ (L.invNeg hh).f' := (Category.assoc _ _ _).symm
      _ = (L.invNeg hh).f' := by rw [sig, (L.invPos h').ff, Category.id_comp]
  · rfl

omit [TwoSupercategory k B] in
theorem cupN_of_nonneg (hh : 0 ≤ h) (n : ℕ) : L.cupN n = (L.invPos hh).g' n := by
  rw [cupN, dite_eq_left hh]

omit [TwoSupercategory k B] in
theorem cupN_of_neg (hh : h < 0) (n : ℕ) : L.cupN n = 0 := by
  rw [cupN, dite_eq_right (not_le.mpr hh)]

omit [TwoSupercategory k B] in
theorem capN_of_nonpos (hh : h ≤ 0) (n : ℕ) : L.capN n = (L.invNeg hh).g' n := by
  rw [capN, dite_eq_left hh]

omit [TwoSupercategory k B] in
theorem capN_of_pos (hh : 0 < h) (n : ℕ) : L.capN n = 0 := by
  rw [capN, dite_eq_right (not_le.mpr hh)]

omit [TwoSupercategory k B] in
/-- Brundan (3.3): for `h > 0` the leftward cup is the last dotted inverse cup. -/
theorem cupL_of_pos (hh : 0 < h) : L.cupL = L.cupN (h - 1).toNat := by
  rw [cupL, ite_eq_left hh]

omit [TwoSupercategory k B] in
theorem cupL_of_nonpos (hh : h ≤ 0) : L.cupL = L.cupD (-h).toNat ≫ L.sigL := by
  rw [cupL, ite_eq_right (not_lt.mpr hh)]

omit [TwoSupercategory k B] in
/-- Brundan (3.3): for `h < 0` the leftward cap is the last dotted inverse cap. -/
theorem capL_of_neg (hh : h < 0) : L.capL = L.capN (-h - 1).toNat := by
  rw [capL, ite_eq_left hh]

omit [TwoSupercategory k B] in
theorem capL_of_nonneg (hh : 0 ≤ h) : L.capL = -(L.sigL ≫ L.capD h.toNat) := by
  rw [capL, ite_eq_right (not_lt.mpr hh)]

omit [TwoSupercategory k B] in
theorem ccw_of_nonneg {k : ℤ} (hk : 0 ≤ k) : L.ccw k = L.cupL ≫ L.capD k.toNat := by
  rw [ccw, ite_eq_left hk]

omit [TwoSupercategory k B] in
theorem ccw_of_neg_of_lt {k : ℤ} (hk : k < 0) (hk' : k < h - 1) : L.ccw k = 0 := by
  rw [ccw, ite_eq_right (not_le.mpr hk), ite_eq_right (by omega), ite_eq_right (by omega)]

omit [TwoSupercategory k B] in
theorem cw_of_nonneg {k : ℤ} (hk : 0 ≤ k) : L.cw k = L.cupD k.toNat ≫ L.capL := by
  rw [cw, ite_eq_left hk]

omit [TwoSupercategory k B] in
theorem cw_of_neg_of_lt {k : ℤ} (hk : k < 0) (hk' : k < -h - 1) : L.cw k = 0 := by
  rw [cw, ite_eq_right (not_le.mpr hk), ite_eq_right (by omega), ite_eq_right (by omega)]

omit [TwoSupercategory k B] in
/-- Brundan (3.5), `h ≥ 0`. -/
theorem sig_sigL_of_nonneg (hh : 0 ≤ h) :
    L.sig ≫ L.sigL = ∑ n ∈ Finset.range h.toNat, L.capD n ≫ L.cupN n - 𝟙 _ := by
  have hs : ∑ n ∈ Finset.range h.toNat, L.capD n ≫ L.cupN n =
      ∑ n ∈ Finset.range h.toNat, L.capD n ≫ (L.invPos hh).g' n :=
    Finset.sum_congr rfl fun n _ => by rw [cupN_of_nonneg hh]
  rw [hs, sigL_of_nonneg hh, Preadditive.comp_neg, sig, ← (L.invPos hh).total]
  simp only [capD]
  abel

omit [TwoSupercategory k B] in
theorem sigL_sig_of_nonneg (hh : 0 ≤ h) : L.sigL ≫ L.sig = -𝟙 _ := by
  rw [sigL_of_nonneg hh, Preadditive.neg_comp, sig, (L.invPos hh).ff]

omit [TwoSupercategory k B] in
/-- Brundan (3.5), `h ≤ 0`. -/
theorem sigL_sig_of_nonpos (hh : h ≤ 0) :
    L.sigL ≫ L.sig = ∑ n ∈ Finset.range (-h).toNat, L.capN n ≫ L.cupD n - 𝟙 _ := by
  have hs : ∑ n ∈ Finset.range (-h).toNat, L.capN n ≫ L.cupD n =
      ∑ n ∈ Finset.range (-h).toNat, (L.invNeg hh).g' n ≫ L.cupD n :=
    Finset.sum_congr rfl fun n _ => by rw [capN_of_nonpos hh]
  rw [hs, sigL_of_nonpos hh, Preadditive.neg_comp, sig, ← (L.invNeg hh).total]
  simp only [cupD]
  abel

omit [TwoSupercategory k B] in
theorem sig_sigL_of_nonpos (hh : h ≤ 0) : L.sig ≫ L.sigL = -𝟙 _ := by
  rw [sigL_of_nonpos hh, Preadditive.comp_neg, sig, (L.invNeg hh).ff]

omit [TwoSupercategory k B] in
/-- Brundan (3.6). -/
theorem cupN_sig (hh : 0 ≤ h) {n : ℕ} (hn : n < h.toNat) : L.cupN n ≫ L.sig = 0 := by
  rw [cupN_of_nonneg hh, sig, (L.invPos hh).gf n hn]

omit [TwoSupercategory k B] in
theorem sigL_capD (hh : 0 ≤ h) {n : ℕ} (hn : n < h.toNat) : L.sigL ≫ L.capD n = 0 := by
  rw [sigL_of_nonneg hh, Preadditive.neg_comp, capD, (L.invPos hh).fg n hn, neg_zero]

omit [TwoSupercategory k B] in
theorem cupN_capD (hh : 0 ≤ h) {m n : ℕ} (hm : m < h.toNat) (hn : n < h.toNat) :
    L.cupN m ≫ L.capD n = if m = n then 𝟙 _ else 0 := by
  rw [cupN_of_nonneg hh, capD, (L.invPos hh).gg m n hm hn]

omit [TwoSupercategory k B] in
theorem cupL_sig (hh : 0 < h) : L.cupL ≫ L.sig = 0 := by
  rw [cupL_of_pos hh, cupN_sig hh.le (by omega)]

omit [TwoSupercategory k B] in
/-- Brundan (3.6): the counter-clockwise bubble with `n < h` dots is `δ_{n, h-1}`. -/
theorem cupL_capD (hh : 0 < h) {n : ℕ} (hn : n < h.toNat) :
    L.cupL ≫ L.capD n = if (h - 1).toNat = n then 𝟙 _ else 0 := by
  rw [cupL_of_pos hh, cupN_capD hh.le (by omega) hn]

omit [TwoSupercategory k B] in
/-- Brundan (3.7). -/
theorem sig_capN (hh : h ≤ 0) {n : ℕ} (hn : n < (-h).toNat) : L.sig ≫ L.capN n = 0 := by
  rw [capN_of_nonpos hh, sig, (L.invNeg hh).fg n hn]

omit [TwoSupercategory k B] in
theorem cupD_sigL (hh : h ≤ 0) {n : ℕ} (hn : n < (-h).toNat) : L.cupD n ≫ L.sigL = 0 := by
  rw [sigL_of_nonpos hh, Preadditive.comp_neg, cupD, (L.invNeg hh).gf n hn, neg_zero]

omit [TwoSupercategory k B] in
theorem cupD_capN (hh : h ≤ 0) {m n : ℕ} (hm : m < (-h).toNat) (hn : n < (-h).toNat) :
    L.cupD m ≫ L.capN n = if m = n then 𝟙 _ else 0 := by
  rw [capN_of_nonpos hh, cupD, (L.invNeg hh).gg m n hm hn]

omit [TwoSupercategory k B] in
theorem sig_capL (hh : h < 0) : L.sig ≫ L.capL = 0 := by
  rw [capL_of_neg hh, sig_capN hh.le (by omega)]

omit [TwoSupercategory k B] in
/-- Brundan (3.7): the clockwise bubble with `n < -h` dots is `δ_{n, -h-1}`. -/
theorem cupD_capL (hh : h < 0) {n : ℕ} (hn : n < (-h).toNat) :
    L.cupD n ≫ L.capL = if n = (-h - 1).toNat then 𝟙 _ else 0 := by
  rw [capL_of_neg hh, cupD_capN hh.le hn (by omega)]

omit [TwoSupercategory k B] in
/-- Brundan (3.6), (3.8). -/
theorem ccw_of_lt (hh : 0 < h) {k : ℤ} (hk : k < h - 1) : L.ccw k = 0 := by
  rcases lt_or_ge k 0 with hk0 | hk0
  · exact ccw_of_neg_of_lt hk0 hk
  · rw [ccw_of_nonneg hk0, cupL_capD hh (by omega), ite_eq_right (by omega)]

omit [TwoSupercategory k B] in
theorem ccw_self (hh : 0 < h) : L.ccw (h - 1) = 𝟙 _ := by
  rw [ccw_of_nonneg (by omega), cupL_capD hh (by omega), ite_eq_left rfl]

omit [TwoSupercategory k B] in
/-- Brundan (3.7), (3.9). -/
theorem cw_of_lt (hh : h < 0) {k : ℤ} (hk : k < -h - 1) : L.cw k = 0 := by
  rcases lt_or_ge k 0 with hk0 | hk0
  · exact cw_of_neg_of_lt hk0 hk
  · rw [cw_of_nonneg hk0, cupD_capL hh (by omega), ite_eq_right (by omega)]

omit [TwoSupercategory k B] in
theorem cw_self (hh : h < 0) : L.cw (-h - 1) = 𝟙 _ := by
  rw [cw_of_nonneg (by omega), cupD_capL hh (by omega), ite_eq_left rfl]

end SuperRouquierLoc
end OddMath.SKM
