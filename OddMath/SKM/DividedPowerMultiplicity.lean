import OddMath.SKM.DividedPowerDecomposition
import OddMath.CoveringQuantum.Integers

/-!
# The multiplicity in BE2 Lemma 11.1

The splitters' degree and parity indices give the expansion of the existing
`qpFact`, with BE2's normalization and no extra parity shift on the divided
projective. Hill–Wang (5.28) instead includes `Π^(|i| choose(n,2))`; BE2's
paragraph after Lemma 11.1 removes it when changing the quantum-integer
convention. In rank two the coefficient here is `q + π q⁻¹`, not
`π q + q⁻¹`. The finite combinatorial identity is valid over any commutative
ring, for any unit `q` and any parameter `π`.

The left-module convention is `(Q V)_r = V_(r-1)`. It must not be identified
silently with the raw categorical summand: `TwoStrand.qDecomposition` has
raw coefficient `1 + q^(2dᵢ)` and `normalizedTwo` is `Q^(dᵢ) raw₀`, whereas
the principal LEFT projective here is normalized by `Q^(-dᵢ)`. The projection
diagrams and right-multiplication module maps use opposite directions. The
rank-two consumer compares their normalized coefficients, not their objects.
BE2's categorical definition before Lemma 11.5 uses the unshifted `(0,0)`
idempotent; it therefore differs from that landed normalized object. No global
categorical divided power is defined here.
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
  rw [← Finset.prod_univ_sum (fun j : Fin (a - 1) => Finset.range (j.val + 2))
    (fun (j : Fin (a - 1)) (l : ℕ) =>
      π ^ (j.val + 1 - l) * (q : k) ^ l * ((q⁻¹ : kˣ) : k) ^ (j.val + 1 - l))]
  simp_rw [local_multiplicity]
  exact prod_qpNat q π a

/-- Consolidating the powers displays the independent parity exponent and the
positive and negative degree exponents of a summand. -/
theorem multiplicity_eq (q : kˣ) (π : k) {a : ℕ} (ℓ : Fin (a - 1) → ℕ) :
    multiplicity q π ℓ = π ^ (∑ j : Fin (a - 1), (j.val + 1 - ℓ j)) *
      (q : k) ^ (∑ j : Fin (a - 1), ℓ j) *
      ((q⁻¹ : kˣ) : k) ^ (∑ j : Fin (a - 1), (j.val + 1 - ℓ j)) := by
  simp only [multiplicity, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The same complementary exponent is the actual homogeneous splitter degree
and, modulo two, its parity. -/
theorem complement_eq_shift {n : ℕ} (ℓ : Sq (n + 2)) :
    ((∑ j : Fin (n + 1), (j.val + 1 - ℓ.1 j) : ℕ) : ℤ) = shift n ℓ := by
  have hsum : (∑ j : Fin (n + 1), ((j.val : ℤ) + 1)) = ((n + 2).choose 2 : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j : ℤ) + 1) (n + 1)]
    exact ThickMatrixUnits.sum_range_succ_cast (n + 1)
  have hc (j : Fin (n + 1)) : ((j.val + 1 - ℓ.1 j : ℕ) : ℤ) =
      (j.val : ℤ) + 1 - (ℓ.1 j : ℤ) := by
    rw [Nat.cast_sub (Categorification.mem_Sq' ℓ j), Nat.cast_add, Nat.cast_one]
  rw [Nat.cast_sum]
  simp_rw [hc]
  rw [Finset.sum_sub_distrib, hsum]
  change ((n + 2).choose 2 : ℤ) - (∑ j : Fin (n + 1), (ℓ.1 j : ℤ)) =
    -(((∑ j : Fin (n + 1), ℓ.1 j : ℕ) : ℤ) - ((n + 2).choose 2 : ℤ))
  rw [Nat.cast_sum]
  abel

/-- The total `q` exponent agrees with the normalized projective's shift. -/
theorem multiplicity_degree {n : ℕ} (ℓ : Sq (n + 2)) :
    ((∑ j, ℓ.1 j : ℕ) : ℤ) - ((∑ j : Fin (n + 1), (j.val + 1 - ℓ.1 j) : ℕ) : ℤ) =
      ((n + 2).choose 2 : ℤ) - 2 * shift n ℓ := by
  rw [complement_eq_shift]
  let s : ℤ := ((∑ j : Fin (n + 1), ℓ.1 j : ℕ) : ℤ)
  let c : ℤ := (n + 2).choose 2
  change s - (-(s - c)) = c - 2 * (-(s - c))
  ring

/-- BE2, arXiv:1701.04133v2, Lemma 11.1, the multiplicity: the summand of
`H_n 1_{i^n}` indexed by `ℓ` is `Q^(dᵢ (choose(n,2) - 2 shift)) Π^shift P(i^(n))`,
and these degree/parity monomials sum to `[n]!_{q,π}` (with `q = q_i`, `π = π_i`). -/
theorem sum_shift_monomial (q : kˣ) (π : k) (n : ℕ) :
    ∑ ℓ : Sq (n + 2), π ^ (shift n ℓ).toNat *
      ((q ^ (((n + 2).choose 2 : ℤ) - 2 * shift n ℓ) : kˣ) : k) = qpFact q π (n + 2) := by
  rw [← sum_multiplicity q π (n + 2), ← Finset.sum_coe_sort (Sq (n + 2))]
  apply Finset.sum_congr rfl
  intro ℓ _
  have h1 := complement_eq_shift ℓ
  have h2 := multiplicity_degree ℓ
  rw [← h1] at h2 ⊢
  rw [← h2, Int.toNat_natCast, multiplicity_eq, zpow_sub, zpow_natCast, zpow_natCast,
    ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact (mul_assoc _ _ _).symm

end
end OddMath.SKM.DividedPowerDecomposition
