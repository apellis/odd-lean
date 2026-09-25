import OddMath.Diagrams.OddNilHecke.Differential
import OddMath.Diagrams.OddNilHecke.Comparison

/-!
# The Ellis–Qi differential on odd-lean's presented odd nilHecke ring

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §2.2 ((2.1)–(2.4)) and §3.2 (Proposition 3.3).

The differential `d ℤ (n + 2)` of `OddMath.Diagrams.OddNilHecke.Differential` is transported
along the ring isomorphism `presentedEquivEnd n : Presented n ≃+* End (strands (n + 2))` to
odd-lean's presented odd nilHecke ring `NilHeckeAction.Presented n` (rank `n + 2`, integer
coefficients). The result is a dg superalgebra structure in the sense of Ellis–Qi §2.2:

* `parity n k`: the parity grading (`k : ZMod 2`), transported from the diagrammatic
  grading; `dot_mem_parity`, `crossing_mem_parity` (generators are odd), `one_mem_parity`,
  `mul_mem_parity`;
* `dONH n : Presented n →+ Presented n` with `dONH_dot` (`d(x_j) = x_j²`), `dONH_crossing`
  (`d(∂_i) = 1`), `dONH_mem_parity` (`d` is odd), `dONH_mul` (the super Leibniz rule (2.3)
  for homogeneous left factors), `dONH_dot_mul`, `dONH_crossing_mul`, and `dONH_dONH`
  (`d² = 0`).

Indices: `dot n j` and `crossing n i` are EKL's (and Ellis–Qi's) `x_{j+1}` and `∂_{i+1}`.
Products are composition of operators (the left factor acts last), as in Ellis–Qi §2.3.
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams
open OddMath.Frontier NilHeckeAction

/-- The parity-`k` part of `Presented n`: the preimage of the parity-`k` part of the
diagrammatic endomorphism algebra of `n + 2` strands. -/
def parity (n : ℕ) (k : ZMod 2) : AddSubgroup (Presented n) :=
  ((pres ℤ).endDeg parityDeg (strands (n + 2)) k).toAddSubgroup.comap
    (presentedEquivEnd n).toAddMonoidHom

theorem mem_parity {n : ℕ} {k : ZMod 2} {p : Presented n} :
    p ∈ parity n k ↔ presentedEquivEnd n p ∈ (pres ℤ).endDeg parityDeg (strands (n + 2)) k :=
  Iff.rfl

theorem dot_mem_parity (n : ℕ) (j : Fin (n + 2)) : dot n j ∈ parity n 1 := by
  rw [mem_parity, presentedEquivEnd_dot]; exact x_mem_endDeg ℤ _ _

theorem crossing_mem_parity (n : ℕ) (i : Fin (n + 1)) : crossing n i ∈ parity n 1 := by
  rw [mem_parity, presentedEquivEnd_crossing]; exact ψ_mem_endDeg ℤ _ _

theorem one_mem_parity (n : ℕ) : (1 : Presented n) ∈ parity n 0 := by
  rw [mem_parity, map_one]; exact SetLike.GradedOne.one_mem

theorem mul_mem_parity {n : ℕ} {k l : ZMod 2} {p q : Presented n} (hp : p ∈ parity n k)
    (hq : q ∈ parity n l) : p * q ∈ parity n (k + l) := by
  rw [mem_parity, map_mul]; exact SetLike.GradedMul.mul_mem hp hq

/-- The Ellis–Qi differential on `Presented n`. -/
def dONH (n : ℕ) : Presented n →+ Presented n :=
  (presentedEquivEnd n).symm.toAddEquiv.toAddMonoidHom.comp
    ((d ℤ (n + 2)).toAddMonoidHom.comp (presentedEquivEnd n).toAddEquiv.toAddMonoidHom)

theorem presentedEquivEnd_dONH (n : ℕ) (p : Presented n) :
    presentedEquivEnd n (dONH n p) = d ℤ (n + 2) (presentedEquivEnd n p) :=
  (presentedEquivEnd n).apply_symm_apply _

theorem dONH_eq_iff {n : ℕ} {p q : Presented n} :
    dONH n p = q ↔ d ℤ (n + 2) (presentedEquivEnd n p) = presentedEquivEnd n q := by
  rw [← presentedEquivEnd_dONH, (presentedEquivEnd n).injective.eq_iff]

/-- `d(x_j) = x_j²` (Ellis–Qi (3.1)). -/
theorem dONH_dot (n : ℕ) (j : Fin (n + 2)) : dONH n (dot n j) = dot n j ^ 2 := by
  rw [dONH_eq_iff, presentedEquivEnd_dot, map_pow, presentedEquivEnd_dot, d_x, sq]

/-- `d(∂_i) = 1` (Ellis–Qi, Proposition 3.3). -/
theorem dONH_crossing (n : ℕ) (i : Fin (n + 1)) : dONH n (crossing n i) = 1 := by
  rw [dONH_eq_iff, presentedEquivEnd_crossing, map_one, d_ψ ℤ (by omega)]

/-- The differential is odd. -/
theorem dONH_mem_parity {n : ℕ} {k : ZMod 2} {p : Presented n} (hp : p ∈ parity n k) :
    dONH n p ∈ parity n (k + 1) := by
  rw [mem_parity, presentedEquivEnd_dONH]
  exact deriv_mem_homDeg ℤ (mem_parity.mp hp)

/-- The super Leibniz rule, Ellis–Qi (2.3): `d(p q) = d(p) q + (-1)^{|p|} p d(q)` for `p`
homogeneous of parity `k`. -/
theorem dONH_mul {n : ℕ} {k : ZMod 2} {p : Presented n} (hp : p ∈ parity n k) (q : Presented n) :
    dONH n (p * q) = dONH n p * q + (-1) ^ k.val * (p * dONH n q) := by
  rw [dONH_eq_iff, map_mul, d_mul_of_mem ℤ (mem_parity.mp hp), map_add, map_mul, map_mul, map_mul, map_pow,
    map_neg, map_one, presentedEquivEnd_dONH, presentedEquivEnd_dONH, Algebra.smul_def,
    eq_intCast, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- `d(x_j q) = x_j² q - x_j d(q)`. -/
theorem dONH_dot_mul (n : ℕ) (j : Fin (n + 2)) (q : Presented n) :
    dONH n (dot n j * q) = dot n j ^ 2 * q - dot n j * dONH n q := by
  rw [dONH_mul (dot_mem_parity n j), dONH_dot]
  simp [ZMod.val_one, sub_eq_add_neg]

/-- `d(∂_i q) = q - ∂_i d(q)`. -/
theorem dONH_crossing_mul (n : ℕ) (i : Fin (n + 1)) (q : Presented n) :
    dONH n (crossing n i * q) = q - crossing n i * dONH n q := by
  rw [dONH_mul (crossing_mem_parity n i), dONH_crossing]
  simp [ZMod.val_one, sub_eq_add_neg]

/-- `d² = 0`. -/
theorem dONH_dONH (n : ℕ) (p : Presented n) : dONH n (dONH n p) = 0 := by
  rw [dONH_eq_iff, presentedEquivEnd_dONH, map_zero, d_d]

end OddMath.Diagrams.OddNilHecke

end
