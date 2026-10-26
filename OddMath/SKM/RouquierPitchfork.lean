import OddMath.SKM.RouquierCurl
import OddMath.SKM.RouquierMixedMate

/-!
# Signed curl inputs for leftward pitchforks

These are direct super counterparts of the curl calculations used in Brundan,
*On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Lemma 4.2.
The downstream target is the E-strand left-adjunction triangle. Composition is
bottom to top; the dot and crossing have parity `p`, and `s = (-1)^p`.
No opposite category or mirror identification is used.
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

/-- Moving dots onto the cup does not change below-boundary vanishing. -/
theorem curlEG_cupD_zero {n : ℕ} (hn : (n : ℤ) < -h) :
    curlEG (L.cupD n) L.capL t = 0 := by
  have hh : h < 0 := by omega
  have hb : curlEG A₂.unit L.capL t = 0 := by
    have := L.curlEG_dotted (n := 0) (by omega)
    simpa [TwoSupercategory.id_whiskerRight (R := k), show h ≠ 0 by omega] using this
  rw [cupD, ← curlEG_whiskerLeft_comp (k := k), L.powComp_tau, curlEG_add (k := k),
    curlEG_zsmul (k := k), curlEG_comp_whiskerRight _ L.capL_mem _ (rouquierPower_mem L.dot₁_mem _),
    hb, Limits.zero_comp, smul_zero, smul_zero, zero_add, curlEG_sum (k := k)]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [curlEG_zsmul (k := k), curlEG_comp_whiskerRight _ L.capL_mem _
    (rouquierPower_mem L.dot₁_mem _), curlEG_whiskerLeft (k := k)]
  have hc : A₂.unit ≫ rouquierPower x₂ j ▷ F₂ ≫ L.capL = 0 := by
    have hc := L.cupD_capL hh (n := j) (by omega)
    rw [ite_eq_right (by omega)] at hc
    simpa only [cupD, Category.assoc] using hc
  rw [hc, TwoSupercategory.whiskerLeft_zero (R := k)]
  simp

/-- Moving dots onto the right cap preserves vanishing below the positive boundary. -/
theorem curlG_capD_zero {n : ℕ} (hn : (n : ℤ) < h) :
    curlG L.cupL (L.capD n) t = 0 := by
  have hh : 0 < h := by omega
  have hb : curlG L.cupL A₁.counit t = 0 := by
    have := L.curlG_dotted (n := 0) (by omega)
    simpa [TwoSupercategory.whiskerLeft_id (R := k), show h ≠ 0 by omega,
      show (0 : ℤ) ≠ h by omega] using this
  rw [capD, ← curlG_comp_whiskerRight (k := k), L.tau_powComp,
    curlG_sub (k := k), curlG_zsmul (k := k),
    curlG_whiskerLeft_comp L.cupL_mem _ _ (rouquierPower_mem L.dot₂_mem _),
    hb, Limits.comp_zero, smul_zero, smul_zero, zero_sub, curlG_sum (k := k)]
  rw [Finset.sum_eq_zero]
  · exact neg_zero
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [curlG_zsmul (k := k),
      curlG_whiskerLeft_comp L.cupL_mem _ _ (rouquierPower_mem L.dot₂_mem _),
      curlG_whiskerRight (k := k)]
    have hc := L.cupL_capD hh (n := n - 1 - j) (by omega)
    rw [ite_eq_right (by omega)] at hc
    rw [show L.cupL ≫ F₁ ◁ rouquierPower x₁ (n - 1 - j) ≫ A₁.counit = 0 by
      simpa only [capD, Category.assoc] using hc,
      TwoSupercategory.zero_whiskerRight (R := k)]
    simp

/-- The positive double curl is supported exactly at its boundary degree.
The factor from the positive one-crossing curl is retained, including height zero. -/
theorem curlG_double_dotted (hh : 0 ≤ h) (hsq : t ≫ t = 0) {n : ℕ}
    (hn0 : 0 < n) (hn : (n : ℤ) ≤ h + 1) :
    curlG L.cupL A₁.counit (t ≫ E₁ ◁ rouquierPower x₂ n ≫ t) =
      if (n : ℤ) = h + 1 then
        -((koszulSign p p ^ (n - 1) * (if h = 0 then 1 else koszulSign p p)) • 𝟙 E₂)
      else 0 := by
  rw [L.powComp_tau, Preadditive.comp_add, Preadditive.comp_zsmul,
    ← Category.assoc, hsq, Limits.zero_comp, smul_zero, zero_add,
    Preadditive.comp_sum, curlG_sum (k := k)]
  have ht : ∀ j ∈ Finset.range n, curlG L.cupL A₁.counit
      (t ≫ ((koszulSign p p ^ (n - 1 - j)) •
        (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ (n - 1 - j) ▷ E₂))) =
      if (n : ℤ) = h + 1 ∧ j = 0 then
        -((koszulSign p p ^ (n - 1) * (if h = 0 then 1 else koszulSign p p)) • 𝟙 E₂)
      else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [Preadditive.comp_zsmul, curlG_zsmul (k := k), ← Category.assoc,
      curlG_comp_whiskerRight (k := k)]
    change (koszulSign p p ^ (n - 1 - j)) •
      curlG L.cupL (L.capD (n - 1 - j)) (t ≫ E₁ ◁ rouquierPower x₂ j) = _
    rw [curlG_comp_whiskerLeft _ (L.capD_mem _) _ (rouquierPower_mem L.dot₂_mem _)]
    by_cases he : (n : ℤ) = h + 1 ∧ j = 0
    · rcases he with ⟨he, rfl⟩
      rw [show n - 1 - 0 = h.toNat by omega, L.curlG_capD_self hh]
      simp [he, show h.toNat = n - 1 by omega, smul_smul]
    · rw [L.curlG_capD_zero (by omega), Limits.zero_comp, smul_zero, smul_zero,
        ite_eq_right he]
  rw [Finset.sum_congr rfl ht]
  by_cases he : (n : ℤ) = h + 1
  · simp [he, hn0]
  · simp [he]

include L in
/-- Iterated right slide, with the ordered powers kept on their original strands. -/
theorem powComp_right_tau (n : ℕ) :
    rouquierPower x₁ n ▷ E₂ ≫ t = (koszulSign p p ^ n) • (t ≫ E₁ ◁ rouquierPower x₂ n) -
      ∑ j ∈ Finset.range n, (koszulSign p p ^ (n - j)) •
        (rouquierPower x₁ j ▷ E₂ ≫ E₁ ◁ rouquierPower x₂ (n - 1 - j)) := by
  have hs : x₁ ▷ E₂ ≫ t = koszulSign p p • (t ≫ E₁ ◁ x₂) - koszulSign p p • 𝟙 _ := by
    rw [← L.slide_right, smul_sub, smul_smul, koszulSign_mul_self, one_smul]
    abel
  induction n with
  | zero => simp [TwoSupercategory.id_whiskerRight (R := k), TwoSupercategory.whiskerLeft_id (R := k)]
  | succ n ih =>
    rw [rouquierPower_succ, TwoSupercategory.comp_whiskerRight (R := k), Category.assoc, hs,
      Preadditive.comp_sub, Preadditive.comp_zsmul, Preadditive.comp_zsmul,
      Category.comp_id, ← Category.assoc, ih, Preadditive.sub_comp,
      Preadditive.zsmul_comp, Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k),
      ← rouquierPower_succ, Preadditive.sum_comp, smul_sub, smul_smul, ← pow_succ',
      Finset.sum_range_succ, Finset.smul_sum]
    have hsum : ∑ j ∈ Finset.range n, koszulSign p p •
        (((koszulSign p p ^ (n - j)) •
          (rouquierPower x₁ j ▷ E₂ ≫ E₁ ◁ rouquierPower x₂ (n - 1 - j))) ≫ E₁ ◁ x₂) =
        ∑ j ∈ Finset.range n, (koszulSign p p ^ (n + 1 - j)) •
          (rouquierPower x₁ j ▷ E₂ ≫ E₁ ◁ rouquierPower x₂ (n + 1 - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [Preadditive.zsmul_comp, Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k),
        ← rouquierPower_succ, smul_smul, ← pow_succ',
        show n - j + 1 = n + 1 - j by omega, show n - 1 - j + 1 = n + 1 - 1 - j by omega]
    rw [hsum, show n + 1 - n = 1 by omega, show n + 1 - 1 - n = 0 by omega,
      pow_one, rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
    abel

/-- A closed double crossing at the boundary has coefficient `-s^n`.
Below the boundary it vanishes. This is the signed input to the cap-swap identity. -/
theorem curlEG_double_dotted (hsq : t ≫ t = 0) {n : ℕ}
    (hn0 : 0 < n) (hn : (n : ℤ) ≤ 1 - h) :
    curlEG A₂.unit L.capL (t ≫ rouquierPower x₁ n ▷ E₂ ≫ t) =
      if (n : ℤ) = 1 - h then -((koszulSign p p ^ n) • 𝟙 E₁) else 0 := by
  rw [L.powComp_right_tau, Preadditive.comp_sub, Preadditive.comp_zsmul,
    ← Category.assoc, hsq, Limits.zero_comp, smul_zero, zero_sub,
    Preadditive.comp_sum, curlEG_neg (k := k), curlEG_sum (k := k)]
  have ht : ∀ j ∈ Finset.range n, curlEG A₂.unit L.capL
      (t ≫ ((koszulSign p p ^ (n - j)) •
        (rouquierPower x₁ j ▷ E₂ ≫ E₁ ◁ rouquierPower x₂ (n - 1 - j)))) =
      if (n : ℤ) = 1 - h ∧ j = 0 then (koszulSign p p ^ n) • 𝟙 E₁ else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [Preadditive.comp_zsmul, curlEG_zsmul (k := k),
      TwoSupercategory.super_interchange (R := k)
        (rouquierPower_mem L.dot₁_mem j) (rouquierPower_mem L.dot₂_mem (n - 1 - j)),
      Preadditive.comp_zsmul, curlEG_zsmul (k := k), ← Category.assoc,
      curlEG_comp_whiskerRight _ L.capL_mem _ (rouquierPower_mem L.dot₁_mem j),
      curlEG_comp_whiskerLeft (k := k), L.curlEG_dotted (by omega)]
    have heq : (↑(n - 1 - j) : ℤ) = -h ↔ (n : ℤ) = 1 - h ∧ j = 0 := by omega
    simp only [heq]
    by_cases hc : (n : ℤ) = 1 - h ∧ j = 0
    · rcases hc with ⟨hc, rfl⟩
      simp [hc]
    · simp [hc]
  rw [Finset.sum_congr rfl ht]
  by_cases heq : (n : ℤ) = 1 - h
  · simp [heq, hn0]
  · simp [heq]

/-- The cap composite in the left-cap pitchfork calculation. The rightward
crossing is followed by the upward crossing, then the inverse-defined left cap. -/
def capCross : (E₁ ≫ F₁) ≫ E₁ ⟶ E₁ :=
  (associator E₁ F₁ E₁).hom ≫ E₁ ◁ L.sig ≫ (associator E₁ E₂ F₂).inv ≫ t ▷ F₂ ≫
    (associator E₁ E₂ F₂).hom ≫ E₁ ◁ L.capL ≫ (rightUnitor E₁).hom

omit [TwoSupercategory k B] in
/-- The rightward crossing has the parity of the upward crossing. -/
theorem sig_mem : L.sig ∈ parity (R := k) _ _ p := by
  rcases le_total 0 h with hh | hh
  · exact (L.invPos hh).f_mem
  · exact (L.invNeg hh).f_mem

/-- Closing the input of the cap composite gives a double crossing. The
right-adjunction unit is even, so this closure introduces no Koszul sign. -/
theorem unit_capCross :
    (leftUnitor E₁).inv ≫ A₁.unit ▷ E₁ ≫ L.capCross =
      curlEG A₂.unit L.capL (t ≫ t) := by
  unfold capCross
  rw [reassoc_of% L.unit_sig_pitchfork]
  simp only [curlEG, TwoSupercategory.comp_whiskerRight (R := k), Category.assoc,
    Iso.hom_inv_id_assoc]

/-- The undotted cup component of the cap-swap calculation vanishes by the
nilHecke square relation, in either parity and without a height restriction. -/
theorem unit_capCross_zero (hsq : t ≫ t = 0) :
    (leftUnitor E₁).inv ≫ A₁.unit ▷ E₁ ≫ L.capCross = 0 := by
  rw [L.unit_capCross, hsq, curlEG_zero (k := k)]

/-- Moving a homogeneous dot power past the rightward crossing contributes
`(-1)^(n p²)`. This factor must be retained before using the double-curl value. -/
theorem dottedUnit_capCross (n : ℕ) :
    (leftUnitor E₁).inv ≫ (A₁.unit ≫ rouquierPower x₁ n ▷ F₁) ▷ E₁ ≫ L.capCross =
      koszulSign ((n : ZMod 2) * p) p •
        curlEG A₂.unit L.capL (t ≫ rouquierPower x₁ n ▷ E₂ ≫ t) := by
  unfold capCross
  rw [TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Category.assoc]
  rw [TwoSupercategory.associator_naturality_left_assoc (R := k)]
  rw [reassoc_of% (TwoSupercategory.super_interchange (R := k)
    (rouquierPower_mem L.dot₁_mem n) L.sig_mem)]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  rw [TwoSupercategory.associator_inv_naturality_left_assoc (R := k)]
  rw [reassoc_of% L.unit_sig_pitchfork]
  simp only [curlEG, TwoSupercategory.comp_whiskerRight (R := k), Category.assoc,
    Iso.hom_inv_id_assoc]

/-- The dotted cup component has boundary value `-1`, in both parities.
The interchange factor `s^n` cancels the `s^n` in the double-curl value. -/
theorem dottedUnit_capCross_boundary (hsq : t ≫ t = 0) {n : ℕ}
    (hn0 : 0 < n) (hn : (n : ℤ) ≤ 1 - h) :
    (leftUnitor E₁).inv ≫ (A₁.unit ≫ rouquierPower x₁ n ▷ F₁) ▷ E₁ ≫ L.capCross =
      if (n : ℤ) = 1 - h then -𝟙 E₁ else 0 := by
  have hs : ∀ m : ℕ, koszulSign ((m : ZMod 2) * p) p = koszulSign p p ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        koszulSign_add_left, ih, pow_succ]
  rw [L.dottedUnit_capCross, L.curlEG_double_dotted hsq hn0 hn, hs]
  split_ifs
  · rw [smul_neg, smul_smul, ← mul_pow, koszulSign_mul_self, one_pow, one_smul]
  · rw [smul_zero]

omit [TwoSupercategory k B] in
/-- At heights at most one the capped crossing has only its two lowest terms.
The coefficients are unchanged in odd parity. -/
theorem sig_capL_low (hh : h ≤ 1) :
    L.sig ≫ L.capL = L.capD 0 ≫ L.cw (-1) + if h = 1 then L.capD 1 else 0 := by
  rcases lt_trichotomy h 0 with hn | hz | hp
  · rw [L.sig_capL hn, L.cw_of_neg_of_lt (by omega) (by omega),
      Limits.comp_zero, ite_eq_right (by omega), add_zero]
  · subst h
    rw [L.sig_capL_expansion]
    change (∑ n ∈ Finset.range 1, L.capD n ≫ L.cw (-(n : ℤ) - 1)) =
      L.capD 0 ≫ L.cw (-1) + 0
    rw [Finset.sum_range_one, add_zero]
    rfl
  · have heq : h = 1 := by omega
    subst h
    rw [L.sig_capL_expansion]
    change (∑ n ∈ Finset.range 2, L.capD n ≫ L.cw (-(n : ℤ) - 1)) =
      L.capD 0 ≫ L.cw (-1) + L.capD 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.cast_zero, Nat.cast_one]
    have hc : L.cw (-1 - 1) = 𝟙 _ := L.cw_of_neg_of_eq (by omega) (by omega)
    rw [hc, Category.comp_id]
    rfl
/-- Closing the rightward crossing with a dotted right cap retains the sign
from interchanging its crossing and the open-strand dot power. -/
theorem sig_capD_closed (n : ℕ) :
    L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ (F₂ ◁ rouquierPower x₂ n ≫ A₂.counit) ≫ (rightUnitor E₂).hom =
    koszulSign p ((n : ZMod 2) * p) •
      ((associator F₁ E₁ E₂).hom ≫ F₁ ◁ (E₁ ◁ rouquierPower x₂ n ≫ t) ≫
        (associator F₁ E₁ E₂).inv ≫ A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom) := by
  rw [TwoSupercategory.whiskerLeft_comp (R := k)]
  simp only [Category.assoc]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k),
    TwoSupercategory.super_interchange_assoc (R := k) L.sig_mem
      (rouquierPower_mem L.dot₂_mem n)]
  rw [L.sig_counit_pitchfork]
  rw [TwoSupercategory.associator_naturality_right_assoc (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k)]
  simp only [Category.assoc]
/-- Closing a dotted cap after the additional upward crossing. -/
theorem cross_sig_capD_closed (n : ℕ) :
    (associator F₁ E₁ E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫
      L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
        E₂ ◁ (F₂ ◁ rouquierPower x₂ n ≫ A₂.counit) ≫ (rightUnitor E₂).hom =
    koszulSign p ((n : ZMod 2) * p) •
      ((associator F₁ E₁ E₂).hom ≫ F₁ ◁ (t ≫ E₁ ◁ rouquierPower x₂ n ≫ t) ≫
        (associator F₁ E₁ E₂).inv ≫ A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom) := by
  rw [L.sig_capD_closed]
  simp only [Preadditive.comp_zsmul, TwoSupercategory.whiskerLeft_comp (R := k),
    Category.assoc, Iso.inv_hom_id_assoc]

include L in
omit [TwoSupercategory k B] in
/-- The one-dot sandwich reduces to the crossing in either parity. -/
theorem tau_dot_tau_left (hsq : t ≫ t = 0) : t ≫ E₁ ◁ x₂ ≫ t = t := by
  have hs := congrArg (fun z => t ≫ z) L.slide_left
  simp only [Preadditive.comp_sub, Preadditive.comp_zsmul, Category.comp_id,
    ← Category.assoc, hsq, Limits.zero_comp, smul_zero, sub_zero] at hs
  simpa only [Category.assoc] using hs

/-- The one-dot capped double-crossing has coefficient `(-1)^p`.
This sign comes from the dotted-cap interchange, not from the upward sandwich. -/
theorem cross_sig_capD_one (hsq : t ≫ t = 0) :
    (associator F₁ E₁ E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫
      L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
        E₂ ◁ (F₂ ◁ x₂ ≫ A₂.counit) ≫ (rightUnitor E₂).hom =
    koszulSign p p • (L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom) := by
  have hc := L.cross_sig_capD_closed 1
  simp only [rouquierPower_succ, rouquierPower_zero, Category.id_comp,
    Nat.cast_one, one_mul] at hc
  rw [L.tau_dot_tau_left hsq, ← L.sig_counit_pitchfork] at hc
  exact hc
/-- The zero-dot capped double-crossing vanishes by the upward square relation. -/
theorem cross_sig_capD_zero (hsq : t ≫ t = 0) :
    (associator F₁ E₁ E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫
      L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
        E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom = 0 := by
  have hc := L.cross_sig_capD_closed 0
  simpa only [rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
    Category.id_comp, hsq, TwoSupercategory.whiskerLeft_zero (R := k),
    Limits.zero_comp, Limits.comp_zero, smul_zero] using hc

/-- The negative augmented inverse detects equality after right whiskering.
Only its total inverse equation is used; no target morphism is assumed. -/
theorem whiskerRight_hom_ext_of_nonpos (hh : h ≤ 0) {d : B} (G : b ⟶ d)
    {H : b ⟶ d} (f g : (E₂ ≫ F₂) ≫ G ⟶ H)
    (hf : L.sig ▷ G ≫ f = L.sig ▷ G ≫ g)
    (hg : ∀ n, n < (-h).toNat → L.cupD n ▷ G ≫ f = L.cupD n ▷ G ≫ g) : f = g := by
  let I := L.invNeg hh
  have ht (z : (E₂ ≫ F₂) ≫ G ⟶ H) :
      I.f' ▷ G ≫ (L.sig ▷ G ≫ z) +
        ∑ n ∈ Finset.range (-h).toNat, I.g' n ▷ G ≫ (L.cupD n ▷ G ≫ z) = z := by
    have hs := map_sum (AddMonoidHom.mk' (fun η : E₂ ≫ F₂ ⟶ E₂ ≫ F₂ => η ▷ G)
      fun η θ => TwoSupercategory.add_whiskerRight (R := k) η θ G)
      (fun n => I.g' n ≫ (A₂.unit ≫ rouquierPower x₂ n ▷ F₂)) (Finset.range (-h).toNat)
    have he := congrArg (fun q => q ▷ G ≫ z) I.total
    change (∑ n ∈ Finset.range (-h).toNat, I.g' n ≫ (A₂.unit ≫ rouquierPower x₂ n ▷ F₂)) ▷ G =
      ∑ n ∈ Finset.range (-h).toNat, (I.g' n ≫ (A₂.unit ≫ rouquierPower x₂ n ▷ F₂)) ▷ G at hs
    simpa only [TwoSupercategory.add_whiskerRight (R := k),
      hs, TwoSupercategory.comp_whiskerRight (R := k),
      TwoSupercategory.id_whiskerRight (R := k), Preadditive.add_comp,
      Preadditive.sum_comp, Category.assoc, Category.id_comp, sig, cupD] using he
  calc
    f = I.f' ▷ G ≫ (L.sig ▷ G ≫ f) +
        ∑ n ∈ Finset.range (-h).toNat, I.g' n ▷ G ≫ (L.cupD n ▷ G ≫ f) := (ht f).symm
    _ = I.f' ▷ G ≫ (L.sig ▷ G ≫ g) +
        ∑ n ∈ Finset.range (-h).toNat, I.g' n ▷ G ≫ (L.cupD n ▷ G ≫ g) := by
      rw [hf]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [hg n (Finset.mem_range.mp hn)]
    _ = g := ht g

/-- The negative augmented inverse also detects equality after left whiskering. -/
theorem whiskerLeft_hom_ext_of_nonpos (hh : h ≤ 0) {d : B} (G : d ⟶ b)
    {H : d ⟶ b} (f g : G ≫ (E₂ ≫ F₂) ⟶ H)
    (hf : G ◁ L.sig ≫ f = G ◁ L.sig ≫ g)
    (hg : ∀ n, n < (-h).toNat → G ◁ L.cupD n ≫ f = G ◁ L.cupD n ≫ g) : f = g := by
  let I := L.invNeg hh
  have ht (z : G ≫ (E₂ ≫ F₂) ⟶ H) :
      G ◁ I.f' ≫ (G ◁ L.sig ≫ z) +
        ∑ n ∈ Finset.range (-h).toNat, G ◁ I.g' n ≫ (G ◁ L.cupD n ≫ z) = z := by
    have hs := map_sum (AddMonoidHom.mk' (fun η : E₂ ≫ F₂ ⟶ E₂ ≫ F₂ => G ◁ η)
      fun η θ => TwoSupercategory.whiskerLeft_add (R := k) G η θ)
      (fun n => I.g' n ≫ (A₂.unit ≫ rouquierPower x₂ n ▷ F₂)) (Finset.range (-h).toNat)
    have he := congrArg (fun q => G ◁ q ≫ z) I.total
    change G ◁ (∑ n ∈ Finset.range (-h).toNat, I.g' n ≫ (A₂.unit ≫ rouquierPower x₂ n ▷ F₂)) =
      ∑ n ∈ Finset.range (-h).toNat, G ◁ (I.g' n ≫ (A₂.unit ≫ rouquierPower x₂ n ▷ F₂)) at hs
    simpa only [TwoSupercategory.whiskerLeft_add (R := k),
      hs, TwoSupercategory.whiskerLeft_comp (R := k),
      TwoSupercategory.whiskerLeft_id (R := k), Preadditive.add_comp,
      Preadditive.sum_comp, Category.assoc, Category.id_comp, sig, cupD] using he
  calc
    f = G ◁ I.f' ≫ (G ◁ L.sig ≫ f) +
        ∑ n ∈ Finset.range (-h).toNat, G ◁ I.g' n ≫ (G ◁ L.cupD n ≫ f) := (ht f).symm
    _ = G ◁ I.f' ≫ (G ◁ L.sig ≫ g) +
        ∑ n ∈ Finset.range (-h).toNat, G ◁ I.g' n ≫ (G ◁ L.cupD n ≫ g) := by
      rw [hf]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [hg n (Finset.mem_range.mp hn)]
    _ = g := ht g

/-- The positive augmented inverse detects maps into a left-whiskered `FE`. -/
theorem whiskerLeft_hom_ext_of_nonneg (hh : 0 ≤ h) {d : B} (G : d ⟶ b)
    {H : d ⟶ b} (f g : H ⟶ G ≫ (F₁ ≫ E₁))
    (hf : f ≫ G ◁ L.sig = g ≫ G ◁ L.sig)
    (hg : ∀ n, n < h.toNat → f ≫ G ◁ L.capD n = g ≫ G ◁ L.capD n) : f = g := by
  let I := L.invPos hh
  have ht (z : H ⟶ G ≫ (F₁ ≫ E₁)) :
      (z ≫ G ◁ L.sig) ≫ G ◁ I.f' +
        ∑ n ∈ Finset.range h.toNat, (z ≫ G ◁ L.capD n) ≫ G ◁ I.g' n = z := by
    have hs := map_sum (AddMonoidHom.mk' (fun η : F₁ ≫ E₁ ⟶ F₁ ≫ E₁ => G ◁ η)
      fun η θ => TwoSupercategory.whiskerLeft_add (R := k) G η θ)
      (fun n => F₁ ◁ rouquierPower x₁ n ≫ A₁.counit ≫ I.g' n) (Finset.range h.toNat)
    have he := congrArg (fun q => z ≫ G ◁ q) I.total
    change G ◁ (∑ n ∈ Finset.range h.toNat, F₁ ◁ rouquierPower x₁ n ≫ A₁.counit ≫ I.g' n) =
      ∑ n ∈ Finset.range h.toNat, G ◁ (F₁ ◁ rouquierPower x₁ n ≫ A₁.counit ≫ I.g' n) at hs
    simpa only [TwoSupercategory.whiskerLeft_add (R := k), hs,
      TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.whiskerLeft_id (R := k),
      Preadditive.comp_add, Preadditive.comp_sum, Category.assoc, Category.comp_id, sig, capD] using he
  calc
    f = (f ≫ G ◁ L.sig) ≫ G ◁ I.f' +
        ∑ n ∈ Finset.range h.toNat, (f ≫ G ◁ L.capD n) ≫ G ◁ I.g' n := (ht f).symm
    _ = (g ≫ G ◁ L.sig) ≫ G ◁ I.f' +
        ∑ n ∈ Finset.range h.toNat, (g ≫ G ◁ L.capD n) ≫ G ◁ I.g' n := by
      rw [hf]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [hg n (Finset.mem_range.mp hn)]
    _ = g := ht g

/-- The positive augmented inverse detects maps into a right-whiskered `FE`. -/
theorem whiskerRight_hom_ext_of_nonneg (hh : 0 ≤ h) {d : B} (G : b ⟶ d)
    {H : b ⟶ d} (f g : H ⟶ (F₁ ≫ E₁) ≫ G)
    (hf : f ≫ L.sig ▷ G = g ≫ L.sig ▷ G)
    (hg : ∀ n, n < h.toNat → f ≫ L.capD n ▷ G = g ≫ L.capD n ▷ G) : f = g := by
  let I := L.invPos hh
  have ht (z : H ⟶ (F₁ ≫ E₁) ≫ G) :
      (z ≫ L.sig ▷ G) ≫ I.f' ▷ G +
        ∑ n ∈ Finset.range h.toNat, (z ≫ L.capD n ▷ G) ≫ I.g' n ▷ G = z := by
    have hs := map_sum (AddMonoidHom.mk' (fun η : F₁ ≫ E₁ ⟶ F₁ ≫ E₁ => η ▷ G)
      fun η θ => TwoSupercategory.add_whiskerRight (R := k) η θ G)
      (fun n => F₁ ◁ rouquierPower x₁ n ≫ A₁.counit ≫ I.g' n) (Finset.range h.toNat)
    have he := congrArg (fun q => z ≫ q ▷ G) I.total
    change (∑ n ∈ Finset.range h.toNat, F₁ ◁ rouquierPower x₁ n ≫ A₁.counit ≫ I.g' n) ▷ G =
      ∑ n ∈ Finset.range h.toNat, (F₁ ◁ rouquierPower x₁ n ≫ A₁.counit ≫ I.g' n) ▷ G at hs
    simpa only [TwoSupercategory.add_whiskerRight (R := k), hs,
      TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.id_whiskerRight (R := k),
      Preadditive.comp_add, Preadditive.comp_sum, Category.assoc, Category.comp_id, sig, capD] using he
  calc
    f = (f ≫ L.sig ▷ G) ≫ I.f' ▷ G +
        ∑ n ∈ Finset.range h.toNat, (f ≫ L.capD n ▷ G) ≫ I.g' n ▷ G := (ht f).symm
    _ = (g ≫ L.sig ▷ G) ≫ I.f' ▷ G +
        ∑ n ∈ Finset.range h.toNat, (g ≫ L.capD n ▷ G) ≫ I.g' n ▷ G := by
      rw [hf]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [hg n (Finset.mem_range.mp hn)]
    _ = g := ht g

/-- The cup-side double crossing, with its actual inverse-defined left cup. -/
def cupCross : E₂ ⟶ E₂ ≫ (F₂ ≫ E₂) :=
  (leftUnitor E₂).inv ≫ L.cupL ▷ E₂ ≫ (associator F₁ E₁ E₂).hom ≫
    F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫ L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom

/-- All dotted-cap components of the cup-side double crossing are signed double curls. -/
theorem cupCross_capD (n : ℕ) :
    L.cupCross ≫ E₂ ◁ (F₂ ◁ rouquierPower x₂ n ≫ A₂.counit) ≫ (rightUnitor E₂).hom =
      koszulSign p ((n : ZMod 2) * p) •
        curlG L.cupL A₁.counit (t ≫ E₁ ◁ rouquierPower x₂ n ≫ t) := by
  unfold cupCross
  simp only [Category.assoc]
  rw [L.cross_sig_capD_closed]
  simp only [curlG, Preadditive.comp_zsmul]

/-- The dotted-cap components have coefficient `-s` at height zero and `-1`
at positive height. These coefficients are forced before extracting the cup swap. -/
theorem cupCross_capD_boundary (hh : 0 ≤ h) (hsq : t ≫ t = 0) {n : ℕ}
    (hn : (n : ℤ) ≤ h + 1) :
    L.cupCross ≫ E₂ ◁ (F₂ ◁ rouquierPower x₂ n ≫ A₂.counit) ≫ (rightUnitor E₂).hom =
      if (n : ℤ) = h + 1 then -((if h = 0 then koszulSign p p else 1) • 𝟙 E₂) else 0 := by
  rw [L.cupCross_capD]
  by_cases hn0 : n = 0
  · subst n
    simp [TwoSupercategory.whiskerLeft_id (R := k), hsq, curlG_zero (k := k),
      show (0 : ℤ) ≠ h + 1 by omega]
  · rw [L.curlG_double_dotted hh hsq (by omega) hn]
    by_cases he : (n : ℤ) = h + 1
    · rw [ite_eq_left he, ite_eq_left he, smul_neg, smul_smul]
      have hs : ∀ m : ℕ, koszulSign p ((m : ZMod 2) * p) = koszulSign p p ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
            koszulSign_add_right, ih, pow_succ]
      have hs2 : koszulSign p p ^ n * koszulSign p p ^ (n - 1) = koszulSign p p := by
        rw [show koszulSign p p ^ n = koszulSign p p ^ (n - 1) * koszulSign p p by
          rw [← pow_succ]; congr 1; omega,
          mul_right_comm, ← mul_pow, koszulSign_mul_self, one_pow, one_mul]
      rw [hs, ← mul_assoc, hs2]
      split_ifs <;> simp [koszulSign_mul_self]
    · rw [ite_eq_right he, ite_eq_right he, smul_zero]

section Adjacent
variable {d : B} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  {A₃ : SuperAdjunction (k := k) E₃ F₃} {x₃ : E₃ ⟶ E₃}
  {t₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃} {h' : ℤ}
  (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ p h')

/-- The crossing component of the positive cup swap vanishes. -/
theorem cupCross_sig_of_nonneg (hh : 0 ≤ h) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    L.cupCross ≫ E₂ ◁ U.sig = 0 := by
  have hb := rouquierMate_mixed_braid A₁ A₂ A₃ L.cross_mem U.cross_mem hB
  have hc := congrArg (fun z => (leftUnitor E₂).inv ≫ L.cupL ▷ E₂ ≫ z) hb
  simp only [sig, cupCross, Category.assoc] at hc ⊢
  rw [hc]
  rw [← Category.assoc (L.cupL ▷ E₂) (rouquierMate A₁ A₂ t ▷ E₂),
    ← TwoSupercategory.comp_whiskerRight (R := k)]
  change (leftUnitor E₂).inv ≫ (L.cupL ≫ L.sig) ▷ E₂ ≫ _ = 0
  rcases eq_or_lt_of_le hh with hz | hp
  · have hz' : h = 0 := hz.symm
    have hu : L.cupL ≫ L.sig = -A₂.unit := by
      have h0 := L.cupL_powComp_sig_of_le (n := 0) hh
      simpa [hz', TwoSupercategory.whiskerLeft_id (R := k)] using h0
    rw [hu, TwoSupercategory.neg_whiskerRight (R := k), Preadditive.neg_comp,
      Preadditive.comp_neg]
    change -((leftUnitor E₂).inv ≫ A₂.unit ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ U.sig ≫ (associator E₂ E₃ F₃).inv ≫ t₂₃ ▷ F₃ ≫
      (associator E₂ E₃ F₃).hom) = 0
    rw [reassoc_of% U.unit_sig_pitchfork]
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc (t₂₃ ▷ F₃) (t₂₃ ▷ F₃),
      ← TwoSupercategory.comp_whiskerRight (R := k), hsq',
      TwoSupercategory.zero_whiskerRight (R := k)]
    simp
  · rw [L.cupL_sig hp, TwoSupercategory.zero_whiskerRight (R := k)]
    simp

/-- The positive cup swap follows from every component of the augmented inverse.
At height zero its coefficient is `-s`; above zero it is `-1`. -/
theorem cupCross_eq_of_nonneg (hw : h' = h + 2) (hh : 0 ≤ h)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    L.cupCross = -((if h = 0 then koszulSign p p else 1) •
      ((rightUnitor E₂).inv ≫ E₂ ◁ U.cupL)) := by
  apply U.whiskerLeft_hom_ext_of_nonneg (by omega) E₂
  · rw [L.cupCross_sig_of_nonneg U hh hsq' hB, Preadditive.neg_comp,
      Preadditive.zsmul_comp, Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k),
      U.cupL_sig (by omega), TwoSupercategory.whiskerLeft_zero (R := k),
      Limits.comp_zero, smul_zero, neg_zero]
  · intro n hn
    apply (cancel_mono (rightUnitor E₂).hom).mp
    simp only [Preadditive.neg_comp, Preadditive.zsmul_comp, Category.assoc]
    rw [← Category.assoc (E₂ ◁ U.cupL) (E₂ ◁ U.capD n),
      ← TwoSupercategory.whiskerLeft_comp (R := k), U.cupL_capD (by omega) hn]
    have hc := L.cupCross_capD_boundary hh hsq (n := n) (by omega)
    have he : (n : ℤ) = h + 1 ↔ (h' - 1).toNat = n := by omega
    simp only [he] at hc
    split_ifs at hc ⊢ <;>
      simpa only [capD, Category.assoc, TwoSupercategory.whiskerLeft_id (R := k),
        TwoSupercategory.whiskerLeft_zero (R := k), Category.comp_id, Category.id_comp,
        Limits.comp_zero, Limits.zero_comp, Preadditive.neg_comp,
        Preadditive.zsmul_comp, Iso.inv_hom_id, smul_zero, neg_zero] using hc

/-- The signed left-cup pitchfork at nonnegative lower height.
Its coefficient is `s` at zero and one at strictly positive height. -/
theorem cupL_pitchfork_of_nonneg (hw : h' = h + 2) (hh : 0 ≤ h)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (leftUnitor E₂).inv ≫ L.cupL ▷ E₂ ≫ (associator F₁ E₁ E₂).hom ≫
      F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv =
      (if h = 0 then koszulSign p p else 1) •
        ((rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫ L.sigL ▷ E₂) := by
  apply L.whiskerRight_hom_ext_of_nonneg hh E₂
  · have hc := congrArg (fun z => z ≫ (associator E₂ F₂ E₂).inv)
      (L.cupCross_eq_of_nonneg U hw hh hsq hsq' hB)
    simp only [cupCross, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Preadditive.neg_comp, Preadditive.zsmul_comp] at hc
    simp only [Preadditive.zsmul_comp, Category.assoc]
    rw [← TwoSupercategory.comp_whiskerRight (R := k), L.sigL_sig_of_nonneg hh,
      TwoSupercategory.neg_whiskerRight (R := k), TwoSupercategory.id_whiskerRight (R := k)]
    simpa only [Preadditive.comp_neg, Category.comp_id, smul_neg] using hc
  · intro n hn
    apply (cancel_mono (leftUnitor E₂).hom).mp
    have hc := L.curlG_capD_zero (n := n) (by omega)
    simp only [Preadditive.zsmul_comp, Category.assoc]
    rw [← Category.assoc (L.sigL ▷ E₂) (L.capD n ▷ E₂),
      ← TwoSupercategory.comp_whiskerRight (R := k), L.sigL_capD hh hn,
      TwoSupercategory.zero_whiskerRight (R := k)]
    simpa only [curlG, capD, Category.assoc, Limits.zero_comp, Limits.comp_zero,
      smul_zero] using hc

/-- The canonical nonnegative E zigzag has coefficient `(-1)^p`.
Neither inverse-defined generator is rescaled. -/
theorem leftAdj_triangle_E_of_nonneg (hw : h' = h + 2) (hh : 0 ≤ h)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫
      L.capL ▷ E₂ ≫ (leftUnitor E₂).hom = koszulSign p p • 𝟙 E₂ := by
  have hp := L.cupL_pitchfork_of_nonneg U hw hh hsq hsq' hB
  have hc : curlG L.cupL (L.capD h.toNat) t =
      (if h = 0 then koszulSign p p else 1) •
        ((rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫
          L.sigL ▷ E₂ ≫ L.capD h.toNat ▷ E₂ ≫ (leftUnitor E₂).hom) := by
    simpa only [curlG, Preadditive.zsmul_comp, Category.assoc] using
      congrArg (fun z => z ≫ L.capD h.toNat ▷ E₂ ≫ (leftUnitor E₂).hom) hp
  rw [L.curlG_capD_self hh] at hc
  have he := congrArg (fun z => -((if h = 0 then koszulSign p p else 1) • z)) hc
  rw [L.capL_of_nonneg hh, TwoSupercategory.neg_whiskerRight (R := k),
    TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
  split_ifs at he <;> simpa only [smul_neg, smul_smul, koszulSign_mul_self,
    one_smul, mul_one, one_mul, neg_neg] using he.symm

/-- Postcomposing the mixed braid with the left cap introduces no new sign:
the cap is not exchanged with either crossing. -/
theorem sig_capCross
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    L.sig ▷ E₂ ≫ U.capCross =
      (associator F₁ E₁ E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫
      L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫ E₂ ◁ (U.sig ≫ U.capL) ≫
      (rightUnitor E₂).hom := by
  have hb := rouquierMate_mixed_braid A₁ A₂ A₃ L.cross_mem U.cross_mem hB
  have hc := congrArg (fun z => z ≫ E₂ ◁ U.capL ≫ (rightUnitor E₂).hom) hb.symm
  simpa only [capCross, sig, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc] using hc

/-- At negative lower height the crossing component vanishes except at `h=-1`,
where its coefficient is `(-1)^p` from the one-dot capped double crossing. -/
theorem sig_capCross_of_neg (hw : h' = h + 2) (hh : h < 0) (hsq : t ≫ t = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    L.sig ▷ E₂ ≫ U.capCross = if h = -1 then koszulSign p p •
      (L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫ E₂ ◁ A₂.counit ≫
        (rightUnitor E₂).hom) else 0 := by
  have h0 := congrArg (fun z => z ≫ (rightUnitor E₂).inv ≫
    E₂ ◁ U.cw (-1) ≫ (rightUnitor E₂).hom) (L.cross_sig_capD_zero hsq)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Limits.zero_comp] at h0
  rw [L.sig_capCross U hB, U.sig_capL_low (by omega)]
  by_cases he : h = -1
  · rw [ite_eq_left (show h' = 1 by omega), ite_eq_left he,
      TwoSupercategory.whiskerLeft_add (R := k)]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
    simpa only [capD, rouquierPower_zero, rouquierPower_succ,
      TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp,
      h0, zero_add] using L.cross_sig_capD_one hsq
  · rw [ite_eq_right (show h' ≠ 1 by omega), ite_eq_right he, add_zero]
    simpa only [capD, rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
      Category.id_comp, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc] using h0
/-- Super cap swap, derived from all components of the negative augmented inverse.
For `h < -1` its coefficient is `-1`. At `h=-1` the whole difference of
left and right caps is scaled by `s=(-1)^p`; scaling only the right cap would
violate the undotted cup component. This is the super counterpart of Brundan,
arXiv:1501.00350v1, (4.5) in the proof of Lemma 4.2. -/
theorem capCross_eq_of_neg (hw : h' = h + 2) (hh : h < 0)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    U.capCross = if h = -1 then koszulSign p p •
      (-(L.capL ▷ E₂ ≫ (leftUnitor E₂).hom) +
        (associator E₂ F₂ E₂).hom ≫ E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom)
      else -(L.capL ▷ E₂ ≫ (leftUnitor E₂).hom) := by
  apply L.whiskerRight_hom_ext_of_nonpos hh.le E₂
  · have hc : L.sig ▷ E₂ ≫ L.capL ▷ E₂ ≫ (leftUnitor E₂).hom = 0 := by
      rw [← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
        L.sig_capL hh, TwoSupercategory.zero_whiskerRight (R := k), Limits.zero_comp]
    rw [L.sig_capCross_of_neg U hw hh hsq hB]
    split_ifs <;> simp only [Preadditive.comp_zsmul, Preadditive.comp_add,
      Preadditive.comp_neg, hc, neg_zero, zero_add]
  · intro n hn
    have hcap : L.cupD n ▷ E₂ ≫ L.capL ▷ E₂ ≫ (leftUnitor E₂).hom =
        if n = (-h - 1).toNat then (leftUnitor E₂).hom else 0 := by
      rw [← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k), L.cupD_capL hh hn]
      split_ifs
      · rw [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
      · rw [TwoSupercategory.zero_whiskerRight (R := k), Limits.zero_comp]
    by_cases he : h = -1
    · have hn0 : n = 0 := by omega
      subst n
      have hz : L.cupD 0 ▷ E₂ ≫ U.capCross = 0 := by
        have hc := congrArg (fun z => (leftUnitor E₂).hom ≫ z) (U.unit_capCross_zero hsq')
        simpa only [cupD, rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k),
          Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
          Limits.comp_zero] using hc
      have ht : L.cupD 0 ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
          E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom = (leftUnitor E₂).hom := by
        have hc := congrArg (fun z => (leftUnitor E₂).hom ≫ z) A₂.left_triangle
        simpa only [cupD, rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k),
          Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hc
      rw [ite_eq_left he, hz, Preadditive.comp_zsmul, Preadditive.comp_add,
        Preadditive.comp_neg, hcap, ht]
      simp [he]
    · rw [ite_eq_right he, Preadditive.comp_neg, hcap]
      by_cases hn0 : n = 0
      · subst n
        have hc := congrArg (fun z => (leftUnitor E₂).hom ≫ z) (U.unit_capCross_zero hsq')
        have hnz : (0 : ℕ) ≠ (-h - 1).toNat := by omega
        simpa only [cupD, rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k),
          Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
          Limits.comp_zero, ite_eq_right hnz, neg_zero] using hc
      · have hc := congrArg (fun z => (leftUnitor E₂).hom ≫ z)
          (U.dottedUnit_capCross_boundary hsq' (by omega : 0 < n) (by omega))
        have hb : (n : ℤ) = 1 - h' ↔ n = (-h - 1).toNat := by omega
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
          hb, apply_ite (fun z => (leftUnitor E₂).hom ≫ z),
          Preadditive.comp_neg, Category.comp_id, Limits.comp_zero] at hc
        split_ifs at hc ⊢ <;> simpa only [cupD, neg_zero] using hc
/-- The left-cap pitchfork at the exceptional negative boundary.
Its coefficient is `(-1)^p`, as forced by the signed cap swap. -/
theorem capL_pitchfork_at_neg_one (hw : h' = h + 2) (hh : h = -1)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (associator E₂ E₃ F₃).inv ≫ t₂₃ ▷ F₃ ≫ (associator E₂ E₃ F₃).hom ≫
      E₂ ◁ U.capL ≫ (rightUnitor E₂).hom = koszulSign p p •
      (E₂ ◁ U.sigL ≫ (associator E₂ F₂ E₂).inv ≫ L.capL ▷ E₂ ≫
        (leftUnitor E₂).hom) := by
  have hz : U.sigL ≫ A₂.counit = 0 := by
    simpa only [capD, rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
      Category.id_comp] using U.sigL_capD (n := 0) (by omega) (by omega)
  have hc := congrArg (fun z => E₂ ◁ U.sigL ≫ (associator E₂ F₂ E₂).inv ≫ z)
    (L.capCross_eq_of_neg U hw (by omega) hsq hsq' hB)
  rw [ite_eq_left hh] at hc
  simp only [capCross, Iso.inv_hom_id_assoc,
    Preadditive.comp_zsmul, Preadditive.comp_add, Preadditive.comp_neg] at hc
  rw [← Category.assoc (E₂ ◁ U.sigL) (E₂ ◁ U.sig),
    ← TwoSupercategory.whiskerLeft_comp (R := k),
    U.sigL_sig_of_nonneg (by omega), TwoSupercategory.whiskerLeft_neg (R := k),
    TwoSupercategory.whiskerLeft_id (R := k), Preadditive.neg_comp, Category.id_comp,
    ← Category.assoc (E₂ ◁ U.sigL) (E₂ ◁ A₂.counit),
    ← TwoSupercategory.whiskerLeft_comp (R := k), hz,
    TwoSupercategory.whiskerLeft_zero (R := k), Limits.zero_comp, add_zero, smul_neg] at hc
  exact neg_injective hc

/-- Below height minus one the negative left-cap pitchfork has coefficient one.
Unlike the boundary value, no crossing is interchanged with a cap in this argument. -/
theorem capL_pitchfork_below_neg_one (hw : h' = h + 2) (hh : h < -1)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (associator E₂ E₃ F₃).inv ≫ t₂₃ ▷ F₃ ≫ (associator E₂ E₃ F₃).hom ≫
      E₂ ◁ U.capL ≫ (rightUnitor E₂).hom =
      E₂ ◁ U.sigL ≫ (associator E₂ F₂ E₂).inv ≫ L.capL ▷ E₂ ≫
        (leftUnitor E₂).hom := by
  have hu : h' ≤ 0 := by omega
  apply U.whiskerLeft_hom_ext_of_nonpos hu E₂
  · have hc := congrArg (fun z => (associator E₂ F₂ E₂).inv ≫ z)
      (L.capCross_eq_of_neg U hw (by omega) hsq hsq' hB)
    rw [ite_eq_right (show h ≠ -1 by omega)] at hc
    simp only [capCross, Iso.inv_hom_id_assoc, Preadditive.comp_neg] at hc
    rw [← Category.assoc (E₂ ◁ U.sig) (E₂ ◁ U.sigL),
      ← TwoSupercategory.whiskerLeft_comp (R := k), U.sig_sigL_of_nonpos hu,
      TwoSupercategory.whiskerLeft_neg (R := k), TwoSupercategory.whiskerLeft_id (R := k),
      Preadditive.neg_comp, Category.id_comp]
    exact hc
  · intro n hn
    have hc := congrArg (fun z => (rightUnitor E₂).hom ≫ z)
      (U.curlEG_cupD_zero (n := n) (by omega))
    simp only [curlEG, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      Limits.comp_zero] at hc
    rw [← Category.assoc (E₂ ◁ U.cupD n) (E₂ ◁ U.sigL),
      ← TwoSupercategory.whiskerLeft_comp (R := k), U.cupD_sigL hu hn,
      TwoSupercategory.whiskerLeft_zero (R := k), Limits.zero_comp]
    simpa only [Category.assoc] using hc

/-- The canonical E-strand left zigzag is the identity at negative lower
height. The cup and cap are the inverse-defined generators, without rescaling. -/
theorem leftAdj_triangle_E_of_neg (hw : h' = h + 2) (hh : h < 0)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫
      L.capL ▷ E₂ ≫ (leftUnitor E₂).hom = 𝟙 E₂ := by
  by_cases he : h = -1
  · have hu : 0 < h' := by omega
    have hs : U.cupL ≫ U.sig = 0 := U.cupL_sig hu
    have hb : U.cupL ≫ A₂.counit = 𝟙 (𝟙 c) := by
      simpa only [capD, rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
        Category.id_comp, show (h' - 1).toNat = 0 by omega, ite_true] using
        U.cupL_capD hu (n := 0) (by omega)
    have hz : (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫
        (associator E₂ F₂ E₂).inv ≫ U.capCross = 0 := by
      unfold capCross
      rw [Iso.inv_hom_id_assoc,
        ← Category.assoc (E₂ ◁ U.cupL) (E₂ ◁ U.sig),
        ← TwoSupercategory.whiskerLeft_comp (R := k), hs,
        TwoSupercategory.whiskerLeft_zero (R := k), Limits.zero_comp, Limits.comp_zero]
    rw [L.capCross_eq_of_neg U hw hh hsq hsq' hB, ite_eq_left he] at hz
    simp only [Preadditive.comp_zsmul, Preadditive.comp_add, Preadditive.comp_neg,
      Iso.inv_hom_id_assoc] at hz
    rw [← Category.assoc (E₂ ◁ U.cupL) (E₂ ◁ A₂.counit),
      ← TwoSupercategory.whiskerLeft_comp (R := k), hb,
      TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp, Iso.inv_hom_id] at hz
    have hz' := congrArg (fun z => koszulSign p p • z) hz
    rw [smul_smul, koszulSign_mul_self, one_smul, smul_zero] at hz'
    exact neg_add_eq_zero.mp hz'
  · have hu : h' ≤ 0 := by omega
    have hp := L.capL_pitchfork_below_neg_one U hw (by omega) hsq hsq' hB
    rw [cupL, ite_eq_right (show ¬0 < h' by omega),
      TwoSupercategory.whiskerLeft_comp (R := k)]
    simp only [Category.assoc]
    rw [← hp]
    exact U.curlEG_cupD_self hu

end Adjacent

end SuperRouquierLoc

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D)

/-- The canonical left zigzag on E at negative source height, in the family API. -/
theorem leftZigE_of_neg (i : I) {x y : X} (e : x + D.α i = y) (hh : D.h i x < 0) :
    T.leftZigE i e = 𝟙 (T.E i e) := by
  apply (T.loc i (sub_add_cancel x (D.α i)) e).leftAdj_triangle_E_of_neg
    (T.loc i e rfl) _ hh (T.square i (sub_add_cancel x (D.α i)) e)
    (T.square i e rfl) (T.braid i (sub_add_cancel x (D.α i)) e rfl)
  rw [← e]
  simp [Datum.h, Datum.α, map_add, D.cd.coroot_root_self]

/-- The inverse-defined E zigzag at nonnegative source height. -/
theorem leftZigE_of_nonneg (i : I) {x y : X} (e : x + D.α i = y) (hh : 0 ≤ D.h i x) :
    T.leftZigE i e = koszulSign (D.parity i) (D.parity i) • 𝟙 (T.E i e) := by
  apply (T.loc i (sub_add_cancel x (D.α i)) e).leftAdj_triangle_E_of_nonneg
    (T.loc i e rfl) _ hh (T.square i (sub_add_cancel x (D.α i)) e)
    (T.square i e rfl) (T.braid i (sub_add_cancel x (D.α i)) e rfl)
  rw [← e]
  simp [Datum.h, Datum.α, map_add, D.cd.coroot_root_self]

/-- The canonical E zigzag at every height. This is not an assertion of the
F zigzag or of a simultaneous normalization of the two triangles. -/
theorem leftZigE_eq (i : I) {x y : X} (e : x + D.α i = y) :
    T.leftZigE i e =
      (if D.h i x < 0 then 1 else koszulSign (D.parity i) (D.parity i)) • 𝟙 (T.E i e) := by
  split_ifs with hh
  · simpa only [one_smul] using T.leftZigE_of_neg i e hh
  · exact T.leftZigE_of_nonneg i e (by omega)

end RouquierFamily
end OddMath.SKM
