import OddMath.SKM.DividedPowerDecomposition
import OddMath.CoveringQuantum.Integers

/-!
# The multiplicity in BE2 Lemma 11.1

The splitters' degree and parity indices give the expansion of the existing
`qpFact`, with BE2's normalization and no extra parity shift on the divided
projective. The finite combinatorial identity is valid over any commutative
ring, for any unit `q` and any parameter `π`.
-/

namespace OddMath.SKM.DividedPowerDecomposition

open OddMath.Frontier BoxPartitionCount
open OddMath.CoveringQuantum
open scoped BigOperators

noncomputable section

variable {k : Type*} [CommRing k]

/-- The degree/parity monomial for one factoradic tuple. -/
def multiplicity (q : kˣ) (π : k) {a : ℕ} (ℓ : Fin (a - 1) → ℕ) : k :=
  ∏ j, π ^ (j.val + 1 - ℓ j) * (q : k) ^ ℓ j *
    ((q⁻¹ : kˣ) : k) ^ (j.val + 1 - ℓ j)

private theorem local_multiplicity (q : kˣ) (π : k) (m : ℕ) :
    (∑ l ∈ Finset.range (m + 2), π ^ (m + 1 - l) * (q : k) ^ l *
      ((q⁻¹ : kˣ) : k) ^ (m + 1 - l)) = qpNat q π (m + 2) := by
  unfold qpNat
  rw [← Finset.sum_range_reflect
    (fun s => π ^ s * (q : k) ^ (m + 2 - 1 - s) * ((q⁻¹ : kˣ) : k) ^ s) (m + 2)]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  simp only [show m + 2 - 1 = m + 1 by omega,
    show m + 1 - (m + 1 - l) = l by omega]

private theorem prod_qpNat (q : kˣ) (π : k) (a : ℕ) :
    (∏ j : Fin (a - 1), qpNat q π (j.val + 2)) = qpFact q π a := by
  have h : ∀ c, (∏ j ∈ Finset.range c, qpNat q π (j + 2)) = qpFact q π (c + 1) := by
    intro c
    induction c with
    | zero => simp [qpFact]
    | succ c ih => rw [Finset.prod_range_succ, ih, qpFact_succ (q := q) (π := π) (c + 1), mul_comm]
  rw [Fin.prod_univ_eq_prod_range (fun j => qpNat q π (j + 2))]
  cases a with
  | zero => rfl
  | succ a => simpa using h a

/-- The sum of the individual degree/parity monomials is exactly BE2's
`[a]!_{q,π}`, not its bar or the Hill–Wang normalization. -/
theorem sum_multiplicity (q : kˣ) (π : k) (a : ℕ) :
    (∑ ℓ ∈ Sq a, multiplicity q π ℓ) = qpFact q π a := by
  unfold Sq multiplicity
  rw [← Finset.prod_univ_sum]
  simp_rw [local_multiplicity]
  exact prod_qpNat q π a

/-- Consolidating the powers displays the independent parity exponent and the
positive and negative degree exponents of a summand. -/
theorem multiplicity_eq (q : kˣ) (π : k) {a : ℕ} (ℓ : Fin (a - 1) → ℕ) :
    multiplicity q π ℓ = π ^ (∑ j, j.val + 1 - ℓ j) * (q : k) ^ (∑ j, ℓ j) *
      ((q⁻¹ : kˣ) : k) ^ (∑ j, j.val + 1 - ℓ j) := by
  simp only [multiplicity, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The same complementary exponent is the actual homogeneous splitter degree
and, modulo two, its parity. -/
theorem complement_eq_shift {n : ℕ} (ℓ : Sq (n + 2)) :
    ((∑ j : Fin (n + 1), j.val + 1 - ℓ.1 j : ℕ) : ℤ) = shift n ℓ := by
  have hsum : (∑ j : Fin (n + 1), ((j.val : ℤ) + 1)) = ((n + 2).choose 2 : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range]
    exact ThickMatrixUnits.sum_range_succ_cast (n + 1)
  simp only [shift, Categorification.deg61, Nat.cast_sum]
  simp_rw [Nat.cast_sub (Categorification.mem_Sq' ℓ _), Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_sub_distrib, hsum]
  ring

/-- The total `q` exponent agrees with the normalized projective's shift. -/
theorem multiplicity_degree {n : ℕ} (ℓ : Sq (n + 2)) :
    ((∑ j, ℓ.1 j : ℕ) : ℤ) - ((∑ j : Fin (n + 1), j.val + 1 - ℓ.1 j : ℕ) : ℤ) =
      ((n + 2).choose 2 : ℤ) - 2 * shift n ℓ := by
  rw [complement_eq_shift]
  simp only [shift, Categorification.deg61]
  ring

end
end OddMath.SKM.DividedPowerDecomposition
