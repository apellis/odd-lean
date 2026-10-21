/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SerrePolynomial
import OddMath.SKM.Grading

/-! A connected rank-two example with an odd vertex, a nonzero mixed
parameter, and a symmetrizer not congruent to the parity function. -/

namespace OddMath.SKM.SerrePolynomialExamples
open SerrePolynomial

/-- Symmetric Cartan matrix with off-diagonal entries -4. -/
def datum : Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -4
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun i => if i then 0 else 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -4)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨-2, by norm_num⟩

/-- The equal positive symmetrizer. The second vertex is even. -/
def symmetrizer : Symmetrizer datum where
  d := fun _ => 1
  pos := by intro i; norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

/-- `Q_ij=2u⁴+5u²v²+2v⁴`. -/
def scalars : Scalars datum ℚ where
  t := fun i j => if i = j then 1 else Units.mk0 2 (by norm_num)
  t_self := by intro i; simp
  t_symm_of_d_eq_zero := by
    intro i j _
    simp [eq_comm]
  s := fun i j p q => if i ≠ j ∧ p = 2 ∧ q = 2 then 5 else 0
  s_symm := by intro i j p q; simp [eq_comm, and_comm]
  s_eq_zero := by
    intro i j p q hp
    split_ifs with h
    · obtain ⟨_, rfl, _⟩ := h
      have hz : (2 : ZMod 2) = 0 := by decide
      simp only [Nat.cast_ofNat, hz, zero_mul] at hp
      exact (zero_ne_one hp).elim
    · rfl
  two_isUnit := by intro _; norm_num

/-- The mixed coefficient has the required weighted degree. -/
theorem homogeneous : scalars.Homogeneous := by
  intro i j p q _ _ _ _ h
  have h' : i ≠ j ∧ p = 2 ∧ q = 2 := by
    by_contra hn
    exact h (by simp [scalars, hn])
  obtain ⟨hij, rfl, rfl⟩ := h'
  change 2 * (-(if j = i then (2 : ℤ) else -4)) +
    2 * (-(if i = j then (2 : ℤ) else -4)) =
    (-(if i = j then (2 : ℤ) else -4)) * (-(if j = i then (2 : ℤ) else -4))
  norm_num [hij, Ne.symm hij]

/-- Bar-consistency fails at the even second vertex. -/
theorem symmetrizer_not_parity :
    (symmetrizer.d true : ZMod 2) ≠ datum.parity true := by decide

/-- An interior window, with both outer dot exponents positive. -/
theorem mixed_window :
    serreWindow 4 2 (braidPolynomial scalars false true) =
      Finsupp.single (2, 1, 0) (-2 : ℚ) := by
  have h := serreWindow_braidPolynomial scalars false true (k := 2) (by decide) (by decide)
  change serreWindow 4 2 (braidPolynomial scalars false true) =
    Finsupp.single (4 - 2, 2 - 1, 0) ((2 : ℚ) * (-1) ^ (2 - 1)) at h
  norm_num only [Nat.reduceSub, pow_one, mul_neg_one] at h
  exact h

/-- Admissibility on a non-bar-consistent parameter family. -/
theorem neg_left (u v : ℚ) :
    quadraticValue scalars false true (-u) v = quadraticValue scalars false true u v :=
  quadraticValue_neg_left scalars (by decide) (by rfl) u v

end OddMath.SKM.SerrePolynomialExamples
