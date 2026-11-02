/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega

/-! # The coefficient-extraction cap of a principal inverse

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. This proves the polynomial step (8)–(13) of
`docs/Nondegeneracy/SwappedVacuumNonpositiveBubbles.md` from the literal mate
slide and the coefficient-extraction window. In particular the height-zero
cap is obtained from the prescribed principal inverse, rather than chosen
to have the desired bubble moments. No factor action or bubble formula is
assumed or constructed here.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum

open CategoryTheory Finset

universe u v w

variable {k : Type w} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] {V X Y : C}

/-- A finite scalar polynomial evaluated at an endomorphism. The coefficient
order and the chronological order of all surrounding maps are retained. -/
def capPolynomial (c : ℕ → k) (P : ℕ) (x : End X) : End X :=
  ∑ n ∈ range (P + 1), c n • (x ^ n)

/-- Up to the top coefficient-extraction degree, the mate slide has only one
boundary term. The scalar `q` retains the signed odd slide as well. -/
theorem slide_coefficient_window (q : k) (x : End X) (y : End Y)
    (s : X ⟶ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N : ℕ) (hN : 0 < N)
    (hslide : s ≫ y - q • (x ≫ s) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (n : ℕ) (hn : n ≤ N) :
    s ≫ (y ^ n) ≫ ell = q ^ n • ((x ^ n) ≫ s ≫ ell) + if n = N then v else 0 := by
  have hs : s ≫ y = q • (x ≫ s) + v ≫ u := ((sub_eq_iff_eq_add).mp hslide).trans (add_comm _ _)
  induction n with
  | zero => simp [ne_of_lt hN]
  | succ n ih =>
    have hn' : n < N := by omega
    have hi := ih (by omega)
    rw [ite_eq_right (ne_of_lt hn')] at hi
    rw [add_zero] at hi
    calc
      s ≫ (y ^ (n + 1)) ≫ ell = (s ≫ y) ≫ (y ^ n) ≫ ell := by
        simp [pow_succ, End.mul_def, Category.assoc]
      _ = q • (x ≫ s ≫ (y ^ n) ≫ ell) + v ≫ (u ≫ (y ^ n) ≫ ell) := by
        rw [hs]
        simp [Preadditive.add_comp, Category.assoc]
      _ = q • (x ≫ (q ^ n • ((x ^ n) ≫ s ≫ ell))) +
          v ≫ (if n + 1 = N then 𝟙 V else 0) := by rw [hi, hwindow n hn']
      _ = q ^ (n + 1) • ((x ^ (n + 1)) ≫ s ≫ ell) +
          if n + 1 = N then v else 0 := by
        split_ifs <;> simp [pow_succ, End.mul_def, Category.assoc, smul_smul, mul_comm]

/-- At equal probe and reservoir levels the monic probe relation determines
the cap after the principal inverse. This is the height-zero coefficient
identity; in particular no global sign multiplies its right moments. -/
theorem principal_cap_polynomial (q : k) (x : End X) (y : End Y)
    (s : X ⟶ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N : ℕ) (hN : 0 < N) (c : ℕ → k) (hmonic : c N = 1)
    (hsupport : ∀ n ≤ N, c n • q ^ n = c n)
    (hslide : s ≫ y - q • (x ≫ s) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c N x = 0) :
    s ≫ capPolynomial c N y ≫ ell = v := by
  have hterm (n : ℕ) (hn : n ∈ range (N + 1)) :
      c n • (s ≫ (y ^ n) ≫ ell) = c n • ((x ^ n) ≫ s ≫ ell) +
        if n = N then v else 0 := by
    rw [slide_coefficient_window q x y s u v ell N hN hslide hwindow n
      (by simpa using Nat.le_of_lt_succ (mem_range.mp hn)), smul_add, smul_smul]
    rw [show c n * q ^ n = c n from hsupport n (Nat.le_of_lt_succ (mem_range.mp hn))]
    split_ifs with h
    · simp [h, hmonic]
    · simp
  calc
    s ≫ capPolynomial c N y ≫ ell =
        ∑ n ∈ range (N + 1), c n • (s ≫ (y ^ n) ≫ ell) := by
      rw [capPolynomial, Preadditive.sum_comp, Preadditive.comp_sum]
      apply sum_congr rfl
      intro n hn
      rw [Linear.smul_comp, Linear.comp_smul]
    _ = ∑ n ∈ range (N + 1), (c n • ((x ^ n) ≫ s ≫ ell) +
        if n = N then v else 0) := sum_congr rfl hterm
    _ = capPolynomial c N x ≫ s ≫ ell + v := by
      rw [sum_add_distrib]
      rw [capPolynomial, Preadditive.sum_comp]
      have hdelta : (∑ n ∈ range (N + 1), if n = N then v else 0) = v := by simp
      rw [hdelta]
      congr 1
      apply sum_congr rfl
      intro n hn
      rw [Linear.smul_comp]
    _ = v := by rw [hprobe]; simp

/-- The prescribed principal inverse has the coefficient-extraction cap.
Only its two-sided inverse identity and the literal slide enter. -/
theorem principal_inverse_cap (q : k) (x : End X) (y : End Y)
    (s : X ≅ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N : ℕ) (hN : 0 < N) (c : ℕ → k) (hmonic : c N = 1)
    (hsupport : ∀ n ≤ N, c n • q ^ n = c n)
    (hslide : s.hom ≫ y - q • (x ≫ s.hom) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c N x = 0) :
    s.inv ≫ v = capPolynomial c N y ≫ ell := by
  have h := congrArg (fun f => s.inv ≫ f)
    (principal_cap_polynomial q x y s.hom u v ell N hN c hmonic hsupport
      hslide hwindow hprobe)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

/-- Every positive-index right moment of the principal inverse is the
coefficient-extraction moment of the probe polynomial. This is the direct
input to the height-zero generating-series calculation. -/
theorem principal_inverse_right_moment (q : k) (x : End X) (y : End Y)
    (s : X ≅ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N : ℕ) (hN : 0 < N) (c : ℕ → k) (hmonic : c N = 1)
    (hsupport : ∀ n ≤ N, c n • q ^ n = c n)
    (hslide : s.hom ≫ y - q • (x ≫ s.hom) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c N x = 0) (r : ℕ) :
    u ≫ (y ^ r) ≫ s.inv ≫ v =
      ∑ n ∈ range (N + 1), c n • (u ≫ (y ^ (n + r)) ≫ ell) := by
  rw [principal_inverse_cap q x y s u v ell N hN c hmonic hsupport hslide hwindow hprobe,
    capPolynomial, Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.comp_sum]
  apply sum_congr rfl
  intro n hn
  rw [Linear.smul_comp, Linear.comp_smul, Linear.comp_smul]
  congr 1
  rw [pow_add, End.mul_def, Category.assoc]

end OddMath.QuiverHecke.SwappedVacuum
