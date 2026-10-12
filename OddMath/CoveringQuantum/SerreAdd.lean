import OddMath.CoveringQuantum.Integers
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel

/-!
# Additivity of covering Serre polynomials

The covering analogue of the twisted-commutator factorization used by
`LieLean.QuantumGroup.qSerre_add`. It works over a commutative coefficient ring,
with the quantum parameter a unit. The parity-compatible degree condition
is exactly the one supplied by a super Cartan datum; neither parity component
is discarded.
-/

noncomputable section
namespace OddMath.CoveringQuantum
open Finset
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]

/-- Covering Serre polynomial with an independent mixed-parity coefficient. -/
def coveringSerre (q : kˣ) (p c : k) (n : ℕ) (a b : B) : B :=
  ∑ r ∈ range (n + 1),
    ((-1) ^ r * p ^ r.choose 2 * qpBinom q p n r * c ^ r) • (a ^ (n - r) * b * a ^ r)

private theorem coveringSerre_sub (q : kˣ) (p c : k) (n : ℕ) (a x y : B) (t : k) :
    coveringSerre q p c n a (x - t • y) =
      coveringSerre q p c n a x - t • coveringSerre q p c n a y := by
  simp only [coveringSerre, mul_sub, sub_mul, smul_sub, sum_sub_distrib, smul_sum,
    mul_smul_comm, smul_mul_assoc]
  congr 1
  exact sum_congr rfl fun _ _ ↦ smul_comm _ _ _

/-- Factor off the outermost scalar root of the covering Serre polynomial. -/
theorem coveringSerre_succ (q : kˣ) (p c : k) (m : ℕ) (a b : B) :
    coveringSerre q p c (m + 1) a b =
      coveringSerre q p (c * p * (↑q⁻¹ : k)) m a
        (a * b - (c * (q : k) ^ m) • (b * a)) := by
  rw [coveringSerre_sub]
  simp only [coveringSerre]
  rw [sum_range_succ' _ (m + 1)]
  simp only [qpBinom_succ_succ, pow_zero, mul_one, qpBinom_zero_right, one_smul,
    Nat.sub_zero, Nat.choose_zero_succ, add_mul, mul_add, add_smul, sum_add_distrib,
    smul_sum, smul_smul]
  have h1 : ∑ r ∈ range (m + 1),
      ((-1 : k) ^ (r + 1) * p ^ ((r + 1).choose 2) *
        (p ^ (r + 1) * (↑q⁻¹ : k) ^ (r + 1) * qpBinom q p m (r + 1)) * c ^ (r + 1)) •
          (a ^ (m + 1 - (r + 1)) * b * a ^ (r + 1)) + a ^ (m + 1) * b =
      ∑ r ∈ range (m + 1),
        ((-1 : k) ^ r * p ^ (r.choose 2) * qpBinom q p m r * (c * p * (↑q⁻¹ : k)) ^ r) •
          (a ^ (m - r) * (a * b) * a ^ r) := by
    conv_lhs => rw [sum_range_succ, qpBinom_eq_zero_of_lt (Nat.lt_succ_self m)]
    conv_rhs => rw [sum_range_succ']
    simp only [mul_zero, zero_mul, zero_smul, add_zero, pow_zero, qpBinom_zero_right,
      mul_one, one_smul, Nat.sub_zero, Nat.choose_zero_succ]
    congr 1
    · refine sum_congr rfl fun r hr ↦ ?_
      have hr := mem_range.mp hr
      rw [show m + 1 - (r + 1) = m - (r + 1) + 1 by omega]
      congr 1
      · simp only [mul_pow]; ring
      · rw [pow_succ, mul_assoc (a ^ (m - (r + 1))) a b]
    · rw [← mul_assoc, ← pow_succ]
  have h2 : ∑ r ∈ range (m + 1),
      ((-1 : k) ^ (r + 1) * p ^ ((r + 1).choose 2) *
        ((q : k) ^ (m - r) * qpBinom q p m r) * c ^ (r + 1)) •
          (a ^ (m + 1 - (r + 1)) * b * a ^ (r + 1)) =
      -∑ r ∈ range (m + 1),
        (c * (q : k) ^ m * ((-1 : k) ^ r * p ^ (r.choose 2) * qpBinom q p m r *
          (c * p * (↑q⁻¹ : k)) ^ r)) • (a ^ (m - r) * (b * a) * a ^ r) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun r hr ↦ ?_
    have hr := mem_range.mp hr
    rw [← neg_smul]
    congr 1
    · have hqm : (q : k) ^ m = (q : k) ^ (m - r) * (q : k) ^ r := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      have hqr : (q : k) ^ r * (↑q⁻¹ : k) ^ r = 1 := by
        rw [← mul_pow, Units.mul_inv, one_pow]
      rw [hqm, Nat.choose_succ_succ, Nat.choose_one_right, pow_add, mul_pow, mul_pow]
      linear_combination
        ((-1 : k) ^ r * c ^ (r + 1) * (q : k) ^ (m - r) * p ^ (r.choose 2 + r) * qpBinom q p m r)
          * hqr
    · simp only [Nat.add_sub_add_right, mul_assoc, ← pow_succ']
  rw [add_right_comm, h1, h2, sub_eq_add_neg]

/-- A braided eigenvector summand cancels from the full covering Serre polynomial. -/
theorem coveringSerre_add_left (q : kˣ) (p : k) {u w : B}
    (hwu : w * u = (p * (↑q⁻¹ : k) ^ 2) • (u * w)) (m : ℕ) :
    ∀ (c : k) (b : B), w * b = (c * (q : k) ^ m) • (b * w) →
      coveringSerre q p c (m + 1) (u + w) b = coveringSerre q p c (m + 1) u b := by
  induction m with
  | zero =>
    intro c b hb
    simp [coveringSerre, sum_range_succ, hb, add_mul, mul_add]
    abel
  | succ m ih =>
    intro c b hb
    have key : (u + w) * b - (c * (q : k) ^ (m + 1)) • (b * (u + w)) =
        u * b - (c * (q : k) ^ (m + 1)) • (b * u) := by
      rw [add_mul, mul_add, hb, smul_add]; abel
    rw [coveringSerre_succ, coveringSerre_succ q p c (m + 1) u b, key]
    apply ih
    set l := c * (q : k) ^ (m + 1)
    have e1 : w * (u * b) = (p * (↑q⁻¹ : k) ^ 2 * l) • (u * b * w) := by
      rw [← mul_assoc, hwu, smul_mul_assoc, mul_assoc, hb, mul_smul_comm,
        smul_smul]
      simp only [mul_assoc]
    have e2 : w * (b * u) = (l * (p * (↑q⁻¹ : k) ^ 2)) • (b * u * w) := by
      rw [← mul_assoc, hb, smul_mul_assoc, mul_assoc, hwu, mul_smul_comm,
        smul_smul]
      simp only [mul_assoc]
    have hq : (↑q⁻¹ : k) * (q : k) = 1 := Units.inv_mul q
    rw [mul_sub, mul_smul_comm, e1, e2, sub_mul, smul_mul_assoc, smul_sub,
      smul_smul, smul_smul]
    congr 2
    · simp only [l]
      linear_combination (c * p * (↑q⁻¹ : k) * (q : k) ^ m) * hq
    · simp only [l]
      linear_combination (c * c * p * (q : k) ^ (2 * m + 1) * (↑q⁻¹ : k)) * hq

/-- Parameter inversion at precisely the parity-compatible Serre degrees. -/
theorem coveringSerre_inv (q : kˣ) {p : k} (hp : p ^ 2 = 1) (c : k) (n : ℕ)
    (hn : Odd n ∨ p = 1) (a b : B) :
    coveringSerre q⁻¹ p c n a b = coveringSerre q p c n a b := by
  unfold coveringSerre
  apply sum_congr rfl
  intro r hr
  rw [qpBinom_inv hp]
  have he : p ^ (r * (n - r)) = 1 := by
    rcases hn with hn | hn
    · have hev : Even (r * (n - r)) := by
        rcases Nat.even_or_odd r with hr | hr
        · exact hr.mul_right _
        · exact (Nat.Odd.sub_odd hn hr).mul_left _
      obtain ⟨s, hs⟩ := hev
      rw [hs, ← two_mul, pow_mul, hp, one_pow]
    · rw [hn, one_pow]
  rw [he, one_mul]

/-- Additivity for covering Serre elements, retaining both parity components. -/
theorem coveringSerre_add (q : kˣ) {p c : k} (hp : p ^ 2 = 1)
    {u w b b' : B} (m : ℕ) (hn : Odd (m + 1) ∨ p = 1)
    (hwu : w * u = (p * (↑q⁻¹ : k) ^ 2) • (u * w))
    (hb : w * b = (c * (q : k) ^ m) • (b * w))
    (hb' : u * b' = (c * (↑q⁻¹ : k) ^ m) • (b' * u)) :
    coveringSerre q p c (m + 1) (u + w) (b + b') =
      coveringSerre q p c (m + 1) u b + coveringSerre q p c (m + 1) w b' := by
  have huw : u * w = (p * (q : k) ^ 2) • (w * u) := by
    rw [hwu, smul_smul]
    have hs : p * (q : k) ^ 2 * (p * (↑q⁻¹ : k) ^ 2) = 1 := by
      calc
        _ = p ^ 2 * ((q : k) * (↑q⁻¹ : k)) ^ 2 := by ring
        _ = 1 := by rw [hp, Units.mul_inv]; ring
    rw [hs, one_smul]
  have hadd : coveringSerre q p c (m + 1) (u + w) (b + b') =
      coveringSerre q p c (m + 1) (u + w) b + coveringSerre q p c (m + 1) (u + w) b' := by
    simp only [coveringSerre, mul_add, add_mul, smul_add, sum_add_distrib]
  rw [hadd, coveringSerre_add_left q p hwu m c b hb]
  congr 1
  rw [← coveringSerre_inv q hp c (m + 1) hn, add_comm u w,
    coveringSerre_add_left q⁻¹ p (by simpa only [inv_inv] using huw) m c b' hb',
    coveringSerre_inv q hp c (m + 1) hn]

end OddMath.CoveringQuantum
