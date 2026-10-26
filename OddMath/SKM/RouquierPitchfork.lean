import OddMath.SKM.RouquierCurl

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

end SuperRouquierLoc
end OddMath.SKM
