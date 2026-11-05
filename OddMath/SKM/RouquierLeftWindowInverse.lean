import OddMath.SKM.RouquierDotSlide
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Reversed left dotted windows

The raw cup and cap windows for the precomposition augmented inverse retain
ordered endomorphism coefficients. Their antidiagonal evaluations and expansions
are the finite-window calculation of `ReversedReservoirMatrix.md`, §§3–5.

`leftWindowCup_inverse` and `leftWindowCap_inverse` give all five augmented
inverse identities, and `leftWindow_zero_inverse` handles the empty boundary.
The transformed rows and columns retain parity `p(h+1)+np`. These supply the
raw local input of `SwappedHomInversion.md`, §2; transport to the prescribed
Hom coordinates and their normalization signs is a separate obligation.

Matrix multiplication uses the ordinary `End` ring: `a * b = b ≫ a`.
No endomorphism coefficient is replaced by a central scalar. Only the strictly
triangular finite-window error is nilpotent; the dots need not be nilpotent
or invertible.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

omit [∀ a b : B, Preadditive (a ⟶ b)] in
private theorem leftWindow_power_add {a b : B} {E : a ⟶ b} (x : E ⟶ E) (n m : ℕ) :
    rouquierPower x (n + m) = rouquierPower x n ≫ rouquierPower x m := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Nat.add_succ, rouquierPower_succ, ih, Category.assoc]

private theorem leftWindow_strict_pow {R : Type*} [Ring R] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) R) (rank : Fin N → ℕ)
    (hM : ∀ i j, rank j ≤ rank i → M i j = 0) (m : ℕ) :
    ∀ i j, rank j < rank i + m → (M ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j hij
    have hne : i ≠ j := by intro he; subst j; omega
    simp [hne]
  | succ m ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : rank l < rank i + m
    · rw [ih i l hl, zero_mul]
    · rw [hM l j (by omega), mul_zero]

private theorem leftWindow_strict_nilpotent {R : Type*} [Ring R] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) R) (rank : Fin N → ℕ)
    (hrank : ∀ i, rank i < N)
    (hM : ∀ i j, rank j ≤ rank i → M i j = 0) : M ^ N = 0 := by
  ext i j
  exact leftWindow_strict_pow M rank hM N i j (by have := hrank j; omega)

/-- Finite ordered series; only the finite window error is nilpotent. -/
def leftWindowSeries {R : Type*} [Ring R] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) R) : Matrix (Fin N) (Fin N) R :=
  ∑ l ∈ Finset.range N, (1 - M) ^ l

private theorem leftWindowSeries_inverse {R : Type*} [Ring R] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) R) (hM : (1 - M) ^ N = 0) :
    leftWindowSeries M * M = 1 ∧ M * leftWindowSeries M = 1 := by
  constructor
  · simpa only [sub_sub_cancel, hM, sub_zero, leftWindowSeries] using
      geom_sum_mul_neg (1 - M) N
  · have he := mul_geom_sum (1 - M) N
    rw [sub_sub_cancel_left, hM, zero_sub, neg_mul, neg_inj] at he
    exact he

private theorem leftWindow_double (q : ZMod 2) : q + q = 0 := by
  fin_cases q <;> rfl

private theorem leftWindow_matrix_one_mem {C : Type*} [Category C] [Preadditive C]
    [Linear k C] [Supercategory k C] (Z : C) {N : ℕ} (q : Fin N → ZMod 2) (i j : Fin N) :
    (1 : Matrix (Fin N) (Fin N) (End Z)) i j ∈ parity (R := k) Z Z (q i + q j) := by
  rw [Matrix.one_apply]
  split_ifs with he
  · subst j
    rw [leftWindow_double]
    exact id_mem Z
  · exact Submodule.zero_mem _

private theorem leftWindow_matrix_pow_mem {C : Type*} [Category C] [Preadditive C]
    [Linear k C] [Supercategory k C] (Z : C) {N : ℕ} (q : Fin N → ZMod 2)
    (M : Matrix (Fin N) (Fin N) (End Z))
    (hm : ∀ i j, M i j ∈ parity (R := k) Z Z (q i + q j)) (l : ℕ) :
    ∀ i j, (M ^ l) i j ∈ parity (R := k) Z Z (q i + q j) := by
  induction l with
  | zero => exact leftWindow_matrix_one_mem Z q
  | succ l ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    apply Submodule.sum_mem
    intro t _
    have hh := comp_mem (hm t j) (ih i t)
    have he : (q t + q j) + (q i + q t) = q i + q j := by
      calc _ = (q i + q j) + (q t + q t) := by abel
           _ = _ := by rw [leftWindow_double, add_zero]
    rw [he] at hh
    exact hh

private theorem leftWindowSeries_mem {C : Type*} [Category C] [Preadditive C]
    [Linear k C] [Supercategory k C] (Z : C) {N : ℕ} (q : Fin N → ZMod 2)
    (M : Matrix (Fin N) (Fin N) (End Z))
    (hm : ∀ i j, M i j ∈ parity (R := k) Z Z (q i + q j)) (i j : Fin N) :
    leftWindowSeries M i j ∈ parity (R := k) Z Z (q i + q j) := by
  rw [leftWindowSeries, Matrix.sum_apply]
  apply Submodule.sum_mem
  intro l _
  apply leftWindow_matrix_pow_mem Z q
  intro a b
  exact Submodule.sub_mem _ (leftWindow_matrix_one_mem Z q a b) (hm a b)

namespace SuperRouquierLoc
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {p : ZMod 2} {h : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- Dots on the original upward strand after the left cup. -/
def leftWindowCup (n : ℕ) : 𝟙 b ⟶ F₁ ≫ E₁ :=
  L.cupL ≫ F₁ ◁ rouquierPower x₁ n

/-- Dots on the original upward strand before the left cap. -/
def leftWindowCap (n : ℕ) : E₂ ≫ F₂ ⟶ 𝟙 b :=
  rouquierPower x₂ n ▷ F₂ ≫ L.capL

theorem leftWindowCup_mem (n : ℕ) : L.leftWindowCup n ∈
    parity (R := k) _ _ (p * ((h : ZMod 2) + 1) + (n : ZMod 2) * p) :=
  comp_mem L.cupL_mem (TwoSupercategory.whiskerLeft_mem F₁ (rouquierPower_mem L.dot₁_mem n))

theorem leftWindowCap_mem (n : ℕ) : L.leftWindowCap n ∈
    parity (R := k) _ _ (p * ((h : ZMod 2) + 1) + (n : ZMod 2) * p) := by
  simpa only [add_comm, leftWindowCap] using
    comp_mem (TwoSupercategory.whiskerRight_mem F₂ (rouquierPower_mem L.dot₂_mem n)) L.capL_mem

theorem leftWindowCup_capD (n j : ℕ) :
    L.leftWindowCup n ≫ L.capD j = L.cupL ≫ L.capD (n + j) := by
  simp only [leftWindowCup, capD, leftWindow_power_add,
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]

theorem cupD_leftWindowCap (j n : ℕ) :
    L.cupD j ≫ L.leftWindowCap n = L.cupD (j + n) ≫ L.capL := by
  simp only [leftWindowCap, cupD, leftWindow_power_add,
    TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]

theorem leftWindowCup_sig (hh : 0 < h) {n : ℕ} (hn : n < h.toNat) :
    L.leftWindowCup n ≫ L.sig = 0 := by
  simpa only [leftWindowCup, Category.assoc] using L.cupL_powComp_sig hh hn

/-- The negative window annihilation follows from the signed slide, not reflection. -/
theorem sig_leftWindowCap (hh : h < 0) {n : ℕ} (hn : n < (-h).toNat) :
    L.sig ≫ L.leftWindowCap n = 0 := by
  have hs := congrArg (fun f => f ≫ L.capL) (L.powComp_sig n)
  have hz : (F₁ ◁ rouquierPower x₁ n ≫ L.sig) ≫ L.capL = 0 := by
    rw [Category.assoc, L.sig_capL hh, Limits.comp_zero]
  have hsum : (∑ j ∈ Finset.range n,
      (koszulSign p p ^ (n - j)) • (L.capD j ≫ L.cupD (n - 1 - j))) ≫ L.capL = 0 := by
    rw [Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [Preadditive.zsmul_comp, Category.assoc, L.cupD_capL hh (by omega),
      ite_eq_right (by omega), Limits.comp_zero, smul_zero]
  rw [hz, Preadditive.sub_comp, hsum, sub_zero, Preadditive.zsmul_comp,
    Category.assoc] at hs
  have hs' := congrArg (fun f => (koszulSign p p ^ n) • f) hs
  simpa only [smul_zero, smul_smul, ← mul_pow, koszulSign_mul_self, one_pow,
    one_smul, leftWindowCap] using hs'.symm

/-- Expansion in the old inverse cups, with no scalar centrality assumption. -/
theorem leftWindowCup_expansion (hh : 0 < h) {n : ℕ} (hn : n < h.toNat) :
    L.leftWindowCup n = ∑ j ∈ Finset.range h.toNat,
      (L.leftWindowCup n ≫ L.capD j) ≫ L.cupN j := by
  have ht := (L.invPos hh.le).total
  change L.sig ≫ (L.invPos hh.le).f' +
    ∑ j ∈ Finset.range h.toNat, L.capD j ≫ (L.invPos hh.le).g' j = 𝟙 _ at ht
  have ht' := congrArg (fun f => L.leftWindowCup n ≫ f) ht
  simp only [Preadditive.comp_add, Preadditive.comp_sum, ← Category.assoc,
    L.leftWindowCup_sig hh hn, Limits.zero_comp, zero_add,
    Category.comp_id, ← L.cupN_of_nonneg hh.le] at ht'
  simpa only [Category.assoc] using ht'.symm

/-- Dual expansion in the old inverse caps, preserving coefficient order. -/
theorem leftWindowCap_expansion (hh : h < 0) {n : ℕ} (hn : n < (-h).toNat) :
    L.leftWindowCap n = ∑ j ∈ Finset.range (-h).toNat,
      L.capN j ≫ (L.cupD j ≫ L.leftWindowCap n) := by
  have ht := (L.invNeg hh.le).total
  change (L.invNeg hh.le).f' ≫ L.sig +
    ∑ j ∈ Finset.range (-h).toNat, (L.invNeg hh.le).g' j ≫ L.cupD j = 𝟙 _ at ht
  have ht' := congrArg (fun f => f ≫ L.leftWindowCap n) ht
  simpa only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc,
    L.sig_leftWindowCap hh hn, Limits.comp_zero, zero_add,
    Category.id_comp, ← L.capN_of_nonpos hh.le] using ht'.symm

/-- Reversal puts the old positive identity window on the diagonal. -/
def leftCupTransition : Matrix (Fin h.toNat) (Fin h.toNat) (End (𝟙 b)) :=
  fun j n => L.leftWindowCup n ≫ L.capD (h.toNat - 1 - j)

/-- The cap transition has the dual matrix orientation. -/
def leftCapTransition : Matrix (Fin (-h).toNat) (Fin (-h).toNat) (End (𝟙 b)) :=
  fun n j => L.cupD ((-h).toNat - 1 - j) ≫ L.leftWindowCap n

theorem leftCupTransition_of_le (hh : 0 < h) (j n : Fin h.toNat) (hn : n ≤ j) :
    L.leftCupTransition j n = if j = n then 1 else 0 := by
  rw [leftCupTransition, L.leftWindowCup_capD, L.cupL_capD hh (by omega)]
  by_cases he : j = n
  · subst j; rw [ite_eq_left rfl, ite_eq_left (by omega)]; rfl
  · rw [ite_eq_right he, ite_eq_right (by intro heq; apply he; apply Fin.ext; omega)]

theorem leftCapTransition_of_le (hh : h < 0) (n j : Fin (-h).toNat) (hn : n ≤ j) :
    L.leftCapTransition n j = if n = j then 1 else 0 := by
  rw [leftCapTransition, L.cupD_leftWindowCap, L.cupD_capL hh (by omega)]
  by_cases he : n = j
  · subst j; rw [ite_eq_left rfl, ite_eq_left (by omega)]; rfl
  · rw [ite_eq_right he, ite_eq_right (by intro heq; apply he; apply Fin.ext; omega)]

/-- The positive error is strictly upper triangular in reversed coordinates. -/
theorem leftCupTransition_nilpotent (hh : 0 < h) :
    (1 - L.leftCupTransition) ^ h.toNat = 0 := by
  apply leftWindow_strict_nilpotent _ Fin.val (fun i => i.isLt)
  intro i j hij
  change (1 : Matrix _ _ (End (𝟙 b))) i j - L.leftCupTransition i j = 0
  rw [L.leftCupTransition_of_le hh i j hij, Matrix.one_apply, sub_self]

/-- The negative error is strictly lower triangular, with reversed rank. -/
theorem leftCapTransition_nilpotent (hh : h < 0) :
    (1 - L.leftCapTransition) ^ (-h).toNat = 0 := by
  apply leftWindow_strict_nilpotent _ (fun i => (-h).toNat - 1 - i.val)
    (fun i => by omega)
  intro i j hij
  change (1 : Matrix _ _ (End (𝟙 b))) i j - L.leftCapTransition i j = 0
  rw [L.leftCapTransition_of_le hh i j (by omega), Matrix.one_apply, sub_self]

/-- Both ordered products of the positive finite transition and its series. -/
theorem leftCupTransition_inverse (hh : 0 < h) :
    leftWindowSeries (R := End (𝟙 b)) L.leftCupTransition * L.leftCupTransition = 1 ∧
      L.leftCupTransition * leftWindowSeries (R := End (𝟙 b)) L.leftCupTransition = 1 :=
  leftWindowSeries_inverse _ (L.leftCupTransition_nilpotent hh)

/-- Both ordered products of the negative finite transition and its series. -/
theorem leftCapTransition_inverse (hh : h < 0) :
    leftWindowSeries (R := End (𝟙 b)) L.leftCapTransition * L.leftCapTransition = 1 ∧
      L.leftCapTransition * leftWindowSeries (R := End (𝟙 b)) L.leftCapTransition = 1 :=
  leftWindowSeries_inverse _ (L.leftCapTransition_nilpotent hh)

/-- Transformed inverse rows, with the finite transition series retained. -/
def leftWindowCupRow (n : Fin h.toNat) : F₁ ≫ E₁ ⟶ 𝟙 b :=
  ∑ j : Fin h.toNat, L.capD (h.toNat - 1 - j) ≫
    leftWindowSeries (R := End (𝟙 b)) L.leftCupTransition n j

/-- Transformed inverse columns in the negative regime. -/
def leftWindowCapColumn (n : Fin (-h).toNat) : 𝟙 b ⟶ E₂ ≫ F₂ :=
  ∑ j : Fin (-h).toNat, leftWindowSeries (R := End (𝟙 b)) L.leftCapTransition j n ≫
    L.cupD ((-h).toNat - 1 - j)

theorem leftWindowCup_row (hh : 0 < h) (m n : Fin h.toNat) :
    L.leftWindowCup m ≫ L.leftWindowCupRow n = if m = n then 𝟙 _ else 0 := by
  have he := congrArg (fun M => M n m) (L.leftCupTransition_inverse hh).1
  change (∑ j, L.leftCupTransition j m ≫
    leftWindowSeries (R := End (𝟙 b)) L.leftCupTransition n j) = _ at he
  simpa only [leftWindowCupRow, Preadditive.comp_sum, ← Category.assoc,
    leftCupTransition, Matrix.one_apply, End.one_def, eq_comm] using he

theorem leftWindowCap_column (hh : h < 0) (m n : Fin (-h).toNat) :
    L.leftWindowCapColumn m ≫ L.leftWindowCap n = if m = n then 𝟙 _ else 0 := by
  have he := congrArg (fun M => M n m) (L.leftCapTransition_inverse hh).2
  change (∑ j, leftWindowSeries (R := End (𝟙 b)) L.leftCapTransition j m ≫
    L.leftCapTransition n j) = _ at he
  simpa only [leftWindowCapColumn, Preadditive.sum_comp, Category.assoc,
    leftCapTransition, Matrix.one_apply, End.one_def, eq_comm] using he

omit [TwoSupercategory k B] in
theorem sigL_leftWindowCupRow (hh : 0 < h) (n : Fin h.toNat) :
    (-L.sigL) ≫ L.leftWindowCupRow n = 0 := by
  rw [Preadditive.neg_comp, neg_eq_zero]
  simp only [leftWindowCupRow, Preadditive.comp_sum, ← Category.assoc]
  apply Finset.sum_eq_zero
  intro j _
  simp only [L.sigL_capD hh.le (n := h.toNat - 1 - j) (by omega), Limits.zero_comp]

omit [TwoSupercategory k B] in
theorem leftWindowCapColumn_sigL (hh : h < 0) (n : Fin (-h).toNat) :
    L.leftWindowCapColumn n ≫ (-L.sigL) = 0 := by
  rw [Preadditive.comp_neg, neg_eq_zero]
  simp only [leftWindowCapColumn, Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_eq_zero
  intro j _
  simp only [L.cupD_sigL hh.le (n := (-h).toNat - 1 - j) (by omega), Limits.comp_zero]

private theorem leftWindowCup_expansion_rev (hh : 0 < h) (n : Fin h.toNat) :
    L.leftWindowCup n = ∑ j : Fin h.toNat,
      L.leftCupTransition j n ≫ L.cupN (h.toNat - 1 - j) := by
  rw [L.leftWindowCup_expansion hh n.isLt, ← Fin.sum_univ_eq_sum_range]
  simpa only [leftCupTransition, leftCapTransition, Fin.revPerm_apply, Fin.val_rev,
    Nat.sub_sub, Nat.add_comm] using (Equiv.sum_comp Fin.revPerm
    (fun j : Fin h.toNat => (L.leftWindowCup n ≫ L.capD j) ≫ L.cupN j)).symm

private theorem leftWindowCap_expansion_rev (hh : h < 0) (n : Fin (-h).toNat) :
    L.leftWindowCap n = ∑ j : Fin (-h).toNat,
      L.capN ((-h).toNat - 1 - j) ≫ L.leftCapTransition n j := by
  rw [L.leftWindowCap_expansion hh n.isLt, ← Fin.sum_univ_eq_sum_range]
  simpa only [leftCupTransition, leftCapTransition, Fin.revPerm_apply, Fin.val_rev,
    Nat.sub_sub, Nat.add_comm] using (Equiv.sum_comp Fin.revPerm
    (fun j : Fin (-h).toNat => L.capN j ≫ L.cupD j ≫ L.leftWindowCap n)).symm

private theorem leftWindowCup_recover (hh : 0 < h) (j : Fin h.toNat) :
    ∑ n : Fin h.toNat, leftWindowSeries (R := End (𝟙 b)) L.leftCupTransition n j ≫ L.leftWindowCup n =
      L.cupN (h.toNat - 1 - j) := by
  simp_rw [L.leftWindowCup_expansion_rev hh, Preadditive.comp_sum, ← Category.assoc]
  rw [Finset.sum_comm]
  simp_rw [← Preadditive.sum_comp]
  have he (l : Fin h.toNat) := congrArg (fun M => M l j) (L.leftCupTransition_inverse hh).2
  change ∀ l, (∑ n, leftWindowSeries (R := End (𝟙 b)) L.leftCupTransition n j ≫
    L.leftCupTransition l n) =
    (1 : Matrix _ _ (End (𝟙 b))) l j at he
  simp_rw [he, Matrix.one_apply, End.one_def]
  rw [Finset.sum_eq_single j]
  · simp only [ite_eq_left, Category.id_comp]
  · intro l _ hlj
    simp only [ite_eq_right hlj, Limits.zero_comp]
  · simp

private theorem leftWindowCap_recover (hh : h < 0) (j : Fin (-h).toNat) :
    ∑ n : Fin (-h).toNat, L.leftWindowCap n ≫ leftWindowSeries (R := End (𝟙 b)) L.leftCapTransition j n =
      L.capN ((-h).toNat - 1 - j) := by
  simp_rw [L.leftWindowCap_expansion_rev hh, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_comm]
  simp_rw [← Preadditive.comp_sum]
  have he (l : Fin (-h).toNat) := congrArg (fun M => M j l) (L.leftCapTransition_inverse hh).1
  change ∀ l, (∑ n, L.leftCapTransition n l ≫
    leftWindowSeries (R := End (𝟙 b)) L.leftCapTransition j n) =
    (1 : Matrix _ _ (End (𝟙 b))) j l at he
  simp_rw [he, Matrix.one_apply, End.one_def]
  rw [Finset.sum_eq_single j]
  · simp only [ite_eq_left, Category.comp_id]
  · intro l _ hlj
    simp only [ite_eq_right (Ne.symm hlj), Limits.comp_zero]
  · simp

/-- The positive augmented inverse total identity. -/
theorem leftWindowCup_total (hh : 0 < h) :
    L.sig ≫ (-L.sigL) + ∑ n : Fin h.toNat,
      L.leftWindowCupRow n ≫ L.leftWindowCup n = 𝟙 _ := by
  simp only [leftWindowCupRow, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_comm]
  simp_rw [← Preadditive.comp_sum, L.leftWindowCup_recover hh]
  have he := Equiv.sum_comp Fin.revPerm
    (fun j : Fin h.toNat => L.capD j ≫ L.cupN j)
  simp only [Fin.revPerm_apply, Fin.val_rev, ← Nat.sub_sub] at he
  simp only [Nat.sub_right_comm _ _ 1] at he
  rw [he, Fin.sum_univ_eq_sum_range (fun j => L.capD j ≫ L.cupN j),
    Preadditive.comp_neg, L.sig_sigL_of_nonneg hh.le]
  abel

/-- The negative augmented inverse total identity. -/
theorem leftWindowCap_total (hh : h < 0) :
    (-L.sigL) ≫ L.sig + ∑ n : Fin (-h).toNat,
      L.leftWindowCap n ≫ L.leftWindowCapColumn n = 𝟙 _ := by
  simp only [leftWindowCapColumn, Preadditive.comp_sum, ← Category.assoc]
  rw [Finset.sum_comm]
  simp_rw [← Preadditive.sum_comp, L.leftWindowCap_recover hh]
  have he := Equiv.sum_comp Fin.revPerm
    (fun j : Fin (-h).toNat => L.capN j ≫ L.cupD j)
  simp only [Fin.revPerm_apply, Fin.val_rev, ← Nat.sub_sub] at he
  simp only [Nat.sub_right_comm _ _ 1] at he
  rw [he, Fin.sum_univ_eq_sum_range (fun j => L.capN j ≫ L.cupD j),
    Preadditive.neg_comp, L.sigL_sig_of_nonpos hh.le]
  abel

private theorem leftWindow_reverse_parity_pos (hh : 0 < h) (j : Fin h.toNat) :
    ((h.toNat - 1 - j : ℕ) : ZMod 2) * p =
      p * ((h : ZMod 2) + 1) + (j : ZMod 2) * p := by
  have he : ((h.toNat - 1 - j : ℕ) : ℤ) = h - 1 - j := by omega
  have hz := congrArg (fun z : ℤ => (z : ZMod 2)) he
  push_cast at hz
  rw [hz]
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ring

private theorem leftWindow_reverse_parity_neg (hh : h < 0) (j : Fin (-h).toNat) :
    (((-h).toNat - 1 - j : ℕ) : ZMod 2) * p =
      p * ((h : ZMod 2) + 1) + (j : ZMod 2) * p := by
  have he : (((-h).toNat - 1 - j : ℕ) : ℤ) = -h - 1 - j := by omega
  have hz := congrArg (fun z : ℤ => (z : ZMod 2)) he
  push_cast at hz
  rw [hz]
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ring

/-- The reversed transition is homogeneous between its prescribed summands. -/
theorem leftCupTransition_mem (hh : 0 < h) (j n : Fin h.toNat) :
    L.leftCupTransition j n ∈ parity (R := k) _ _
      ((p * ((h : ZMod 2) + 1) + (j : ZMod 2) * p) +
       (p * ((h : ZMod 2) + 1) + (n : ZMod 2) * p)) := by
  have hm := comp_mem (L.leftWindowCup_mem n) (L.capD_mem (h.toNat - 1 - j))
  rw [leftWindow_reverse_parity_pos hh j, add_comm] at hm
  exact hm

theorem leftCapTransition_mem (hh : h < 0) (n j : Fin (-h).toNat) :
    L.leftCapTransition n j ∈ parity (R := k) _ _
      ((p * ((h : ZMod 2) + 1) + (n : ZMod 2) * p) +
       (p * ((h : ZMod 2) + 1) + (j : ZMod 2) * p)) := by
  have hm := comp_mem (L.cupD_mem ((-h).toNat - 1 - j)) (L.leftWindowCap_mem n)
  rw [leftWindow_reverse_parity_neg hh j, add_comm] at hm
  exact hm

/-- The inverse row has exactly the same parity as its left cup. -/
theorem leftWindowCupRow_mem (hh : 0 < h) (n : Fin h.toNat) :
    L.leftWindowCupRow n ∈ parity (R := k) _ _
      (p * ((h : ZMod 2) + 1) + (n : ZMod 2) * p) := by
  apply Submodule.sum_mem
  intro j _
  have hs := leftWindowSeries_mem (k := k) (𝟙 b)
    (fun i : Fin h.toNat => p * ((h : ZMod 2) + 1) + (i : ZMod 2) * p)
    L.leftCupTransition (L.leftCupTransition_mem hh) n j
  have hm := comp_mem (L.capD_mem (h.toNat - 1 - j)) hs
  rw [leftWindow_reverse_parity_pos hh j] at hm
  have he (q r : ZMod 2) : q + (r + q) = r := by
    rw [add_left_comm, leftWindow_double, add_zero]
  rwa [he] at hm

/-- The inverse column has exactly the same parity as its left cap. -/
theorem leftWindowCapColumn_mem (hh : h < 0) (n : Fin (-h).toNat) :
    L.leftWindowCapColumn n ∈ parity (R := k) _ _
      (p * ((h : ZMod 2) + 1) + (n : ZMod 2) * p) := by
  apply Submodule.sum_mem
  intro j _
  have hs := leftWindowSeries_mem (k := k) (𝟙 b)
    (fun i : Fin (-h).toNat => p * ((h : ZMod 2) + 1) + (i : ZMod 2) * p)
    L.leftCapTransition (L.leftCapTransition_mem hh) j n
  have hm := comp_mem hs (L.cupD_mem ((-h).toNat - 1 - j))
  rw [leftWindow_reverse_parity_neg hh j] at hm
  have he (q r : ZMod 2) : (q + r) + q = r := by
    rw [add_assoc, add_comm r q, ← add_assoc, leftWindow_double, zero_add]
  rwa [he] at hm

/-- All five raw positive-height inverse identities, with principal inverse `sig`. -/
theorem leftWindowCup_inverse (hh : 0 < h) :
    (L.sig ≫ (-L.sigL) + ∑ n : Fin h.toNat,
      L.leftWindowCupRow n ≫ L.leftWindowCup n = 𝟙 _) ∧
    ((-L.sigL) ≫ L.sig = 𝟙 _) ∧
    (∀ n : Fin h.toNat, (-L.sigL) ≫ L.leftWindowCupRow n = 0) ∧
    (∀ n : Fin h.toNat, L.leftWindowCup n ≫ L.sig = 0) ∧
    (∀ m n : Fin h.toNat,
      L.leftWindowCup m ≫ L.leftWindowCupRow n = if m = n then 𝟙 _ else 0) := by
  refine ⟨L.leftWindowCup_total hh, ?_, L.sigL_leftWindowCupRow hh,
    fun n => L.leftWindowCup_sig hh n.isLt, L.leftWindowCup_row hh⟩
  rw [Preadditive.neg_comp, L.sigL_sig_of_nonneg hh.le, neg_neg]

/-- All five raw negative-height inverse identities, with principal inverse `sig`. -/
theorem leftWindowCap_inverse (hh : h < 0) :
    ((-L.sigL) ≫ L.sig + ∑ n : Fin (-h).toNat,
      L.leftWindowCap n ≫ L.leftWindowCapColumn n = 𝟙 _) ∧
    (L.sig ≫ (-L.sigL) = 𝟙 _) ∧
    (∀ n : Fin (-h).toNat, L.sig ≫ L.leftWindowCap n = 0) ∧
    (∀ n : Fin (-h).toNat, L.leftWindowCapColumn n ≫ (-L.sigL) = 0) ∧
    (∀ m n : Fin (-h).toNat,
      L.leftWindowCapColumn m ≫ L.leftWindowCap n = if m = n then 𝟙 _ else 0) := by
  refine ⟨L.leftWindowCap_total hh, ?_, fun n => L.sig_leftWindowCap hh n.isLt,
    L.leftWindowCapColumn_sigL hh, L.leftWindowCap_column hh⟩
  rw [Preadditive.comp_neg, L.sig_sigL_of_nonpos hh.le, neg_neg]

omit [TwoSupercategory k B] in
/-- At height zero both windows are empty and both bare products are identities. -/
theorem leftWindow_zero_inverse (hh : h = 0) :
    L.sig ≫ (-L.sigL) = 𝟙 _ ∧ (-L.sigL) ≫ L.sig = 𝟙 _ := by
  constructor
  · rw [Preadditive.comp_neg, L.sig_sigL_of_nonpos (by omega), neg_neg]
  · rw [Preadditive.neg_comp, L.sigL_sig_of_nonneg (by omega), neg_neg]

end SuperRouquierLoc
end OddMath.SKM
