import OddMath.Frontier.EKAutomorphisms
import OddMath.Frontier.EKQuotientRelations
import OddMath.Frontier.OddLREKIdentification

/-! EKL arXiv:1111.1320v1, §2.1.2, Remark 2.4, display (2.25), p.7, and §2.1.3,
Lemma 2.9, display (2.33), p.10.

* (2.25) is proved for all `k, ℓ` with `k + ℓ` odd (the source assumes `k < ℓ`), in every rank.
* (2.33) is proved for all indices and every rank: the even mixed relation for `i + j` even,
  the odd one for `i + j` odd with `j ≥ 1`. The proof applies the EK automorphism `ψ₁ψ₂`
  (which exchanges `e_k` and `h_k` up to the signs `(-1)^{C(k+1,2)}`) to EK's mixed relations
  (EK arXiv:1107.5610v2, (2.16)–(2.17)) and specializes along `Q → OPol_a`. -/
namespace OddMath.Frontier.EKLSectionTwo
open OddMath.SkewPolynomial (SkewPolynomial)
open FiniteCompleteElementary
open scoped BigOperators
noncomputable section

/-! ### The reordering formula (2.25) -/

section Reorder
variable (N : ℕ)

local notation "e" => elementaryPoly N

/-- Sign of `ε_{ℓ+1+i} ε_{k-1-i}` in the reordering of `ε_k ε_ℓ`. -/
def reorderSign (k i : ℕ) : ℤ := (-1) ^ (i + i * k + i.choose 2)

theorem reorderSign_succ (k i : ℕ) :
    reorderSign (k+1) (i+1) = (-1) ^ k * reorderSign k i := by
  unfold reorderSign
  rw [← pow_add]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := k + _)]
  congr 1
  rw [Nat.choose_succ_succ, Nat.choose_one_right]
  ring_nf
  omega

/-- (2.25) in closed recursive form, for all `k, ℓ` with `k + ℓ` odd:
`ε_k ε_ℓ = (-1)^k ε_ℓ ε_k + 2 Σ_{i<k} (-1)^{i+ik+C(i,2)} ε_{ℓ+1+i} ε_{k-1-i}`. -/
theorem reorder (k : ℕ) : ∀ ℓ, Odd (k + ℓ) →
    e k * e ℓ = (-1 : ℤ) ^ k • (e ℓ * e k) +
      (2 : ℤ) • ∑ i ∈ Finset.range k, reorderSign k i • (e (ℓ+1+i) * e (k-1-i)) := by
  induction k with
  | zero => intro ℓ _; simp
  | succ k ih =>
    intro ℓ hkl
    have hev : Even (ℓ + k) := by
      rcases hkl with ⟨t, ht⟩; exact ⟨t, by omega⟩
    have rel := ElementaryRelations.elementary_odd N ℓ k hev
    have hl : (-1 : ℤ) ^ ℓ = (-1 : ℤ) ^ k := by
      rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := k)]
      congr 1
      have := Nat.even_iff.mp hev
      omega
    rw [hl] at rel
    have hi := ih (ℓ+1) (by rcases hkl with ⟨t, ht⟩; exact ⟨t, by omega⟩)
    have hsum : ∑ i ∈ Finset.range (k+1), reorderSign (k+1) i • (e (ℓ+1+i) * e (k+1-1-i)) =
        e (ℓ+1) * e k + (-1 : ℤ) ^ k •
          ∑ i ∈ Finset.range k, reorderSign k i • (e (ℓ+1+1+i) * e (k-1-i)) := by
      rw [Finset.sum_range_succ', add_comm, Finset.smul_sum]
      congr 1
      · simp [reorderSign]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [reorderSign_succ, mul_smul, show ℓ + 1 + (i + 1) = ℓ + 1 + 1 + i by ring,
          show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
    rw [hsum]
    rcases neg_one_pow_eq_or ℤ k with hs | hs
    · rw [hs] at rel hi ⊢
      rw [pow_succ, hs] at *
      rw [hi] at rel
      simp only [one_smul, one_mul] at rel ⊢
      linear_combination (norm := module) rel
    · rw [hs] at rel hi ⊢
      rw [pow_succ, hs]
      rw [hi] at rel
      simp only [neg_smul, one_smul, neg_mul, neg_neg, one_mul] at rel ⊢
      linear_combination (norm := module) -rel

theorem reorder_even_term (k ℓ : ℕ) (hk : Even k) (i : ℕ) :
    reorderSign k i • (e (ℓ+1+i) * e (k-1-i)) =
      (-1 : ℤ) ^ (1 + i).choose 2 • (e (ℓ + (1 + i)) * e (k - (1 + i))) := by
  obtain ⟨t, rfl⟩ := hk
  rw [reorderSign, show ℓ + 1 + i = ℓ + (1 + i) by ring, show t + t - 1 - i = t + t - (1 + i) by omega]
  congr 1
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := (1 + i).choose 2)]
  congr 1
  rw [add_comm 1 i, Nat.choose_succ_succ, Nat.choose_one_right]
  ring_nf; omega

/-- (2.25), `k` even: `ε_k ε_ℓ = ε_ℓ ε_k + 2 Σ_{i=1}^k (-1)^{C(i,2)} ε_{ℓ+i} ε_{k-i}`. -/
theorem reorder_even (k ℓ : ℕ) (hk : Even k) (hkl : Odd (k + ℓ)) :
    e k * e ℓ = e ℓ * e k +
      (2 : ℤ) • ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ i.choose 2 • (e (ℓ+i) * e (k-i)) := by
  have hsum : ∑ i ∈ Finset.range k, reorderSign k i • (e (ℓ+1+i) * e (k-1-i)) =
      ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ i.choose 2 • (e (ℓ+i) * e (k-i)) := by
    rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range, Nat.succ_sub_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact reorder_even_term N k ℓ hk i
  rw [reorder N k ℓ hkl, hk.neg_one_pow, one_smul, hsum]

theorem reorder_odd_term (k ℓ : ℕ) (hk : Odd k) (i : ℕ) :
    reorderSign k i • (e (ℓ+1+i) * e (k-1-i)) =
      (-1 : ℤ) ^ (1 + i - 1).choose 2 • (e (ℓ + (1 + i)) * e (k - (1 + i))) := by
  obtain ⟨t, rfl⟩ := hk
  rw [reorderSign, show ℓ + 1 + i = ℓ + (1 + i) by ring,
    show 2 * t + 1 - 1 - i = 2 * t + 1 - (1 + i) by omega, show 1 + i - 1 = i by omega]
  congr 1
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := i.choose 2)]
  congr 1
  ring_nf; omega

/-- (2.25), `k` odd: `ε_k ε_ℓ = -ε_ℓ ε_k + 2 Σ_{i=1}^k (-1)^{C(i-1,2)} ε_{ℓ+i} ε_{k-i}`. -/
theorem reorder_odd (k ℓ : ℕ) (hk : Odd k) (hkl : Odd (k + ℓ)) :
    e k * e ℓ = -(e ℓ * e k) +
      (2 : ℤ) • ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i-1).choose 2 • (e (ℓ+i) * e (k-i)) := by
  have hsum : ∑ i ∈ Finset.range k, reorderSign k i • (e (ℓ+1+i) * e (k-1-i)) =
      ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i-1).choose 2 • (e (ℓ+i) * e (k-i)) := by
    rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range, Nat.succ_sub_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact reorder_odd_term N k ℓ hk i
  rw [reorder N k ℓ hkl, hk.neg_one_pow, neg_one_smul, hsum]

end Reorder

/-! ### Mixed relations (2.33) -/

open EKElementaryQuotient in
theorem ek_mixed_even_swapped (a b : ℕ) (hab : Even (a+b)) : e a * h b = h b * e a := by
  have h1 := congrArg EKAutomorphisms.psi12 (EKQuotientRelations.mixed_even a b hab)
  simp only [map_mul, EKAutomorphisms.psi12_h, EKAutomorphisms.psi12_e, smul_mul_smul_comm,
    mul_comm (EKAutomorphisms.s b)] at h1
  have hu := congrArg (fun x => (EKAutomorphisms.s a * EKAutomorphisms.s b) • x) h1
  simp only [smul_smul] at hu
  rw [show EKAutomorphisms.s a * EKAutomorphisms.s b * (EKAutomorphisms.s a *
    EKAutomorphisms.s b) = 1 by
      calc _ = (EKAutomorphisms.s a * EKAutomorphisms.s a) *
          (EKAutomorphisms.s b * EKAutomorphisms.s b) := by ring
        _ = 1 := by rw [EKAutomorphisms.s_square, EKAutomorphisms.s_square, one_mul]] at hu
  simpa using hu

open EKElementaryQuotient in
theorem ek_mixed_odd_swapped (a b : ℕ) (hb : 0 < b) (hab : Odd (a+b)) :
    e a * h b + (-1 : ℤ)^a • (h b * e a) =
      (-1 : ℤ)^a • (e (a+1) * h (b-1)) + h (b-1) * e (a+1) := by
  have h1 := congrArg EKAutomorphisms.psi12 (EKQuotientRelations.mixed_odd a b hb hab)
  simp only [map_add, map_zsmul, map_mul, EKAutomorphisms.psi12_h, EKAutomorphisms.psi12_e,
    smul_mul_smul_comm] at h1
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hp : EKAutomorphisms.s a * EKAutomorphisms.s (c+1) =
      EKAutomorphisms.s (a+1) * EKAutomorphisms.s c :=
    EKAutomorphisms.s_pair a c (by rcases hab with ⟨t, ht⟩; exact ⟨t, by omega⟩)
  simp only [Nat.add_sub_cancel] at h1 ⊢
  rw [mul_comm (EKAutomorphisms.s (c+1)) (EKAutomorphisms.s a), hp,
    mul_comm (EKAutomorphisms.s c) (EKAutomorphisms.s (a+1))] at h1
  set u := EKAutomorphisms.s (a+1) * EKAutomorphisms.s c
  have hu : u * u = 1 := by
    calc u * u = (EKAutomorphisms.s (a+1) * EKAutomorphisms.s (a+1)) *
        (EKAutomorphisms.s c * EKAutomorphisms.s c) := by ring
      _ = 1 := by rw [EKAutomorphisms.s_square, EKAutomorphisms.s_square, one_mul]
  have h2 := congrArg (fun x => u • x) h1
  simp only [smul_add, smul_smul, mul_comm _ u, ← mul_assoc, hu, one_mul, one_smul] at h2
  exact h2

/-- (2.33), first relation, in every rank and for all `i, j` with `i + j` even:
`ε_i h_j = h_j ε_i`. -/
theorem mixed_even (N i j : ℕ) (h : Even (i+j)) :
    elementaryPoly N i * completePoly N j = completePoly N j * elementaryPoly N i := by
  have := congrArg (OddLREKIdentification.piN N) (ek_mixed_even_swapped i j h)
  simpa only [map_mul, OddLREKIdentification.piN_e, OddLREKIdentification.piN_h] using this

/-- (2.33), second relation, in every rank and for all `i, j` with `i + j` even:
`ε_i h_{j+1} + (-1)^i h_{j+1} ε_i = (-1)^i ε_{i+1} h_j + h_j ε_{i+1}`. -/
theorem mixed_odd (N i j : ℕ) (h : Even (i+j)) :
    elementaryPoly N i * completePoly N (j+1) +
        (-1 : ℤ)^i • (completePoly N (j+1) * elementaryPoly N i) =
      (-1 : ℤ)^i • (elementaryPoly N (i+1) * completePoly N j) +
        completePoly N j * elementaryPoly N (i+1) := by
  have := congrArg (OddLREKIdentification.piN N)
    (ek_mixed_odd_swapped i (j+1) (by omega) (by rcases h with ⟨t, ht⟩; exact ⟨t, by omega⟩))
  simpa only [map_add, map_zsmul, map_mul, OddLREKIdentification.piN_e,
    OddLREKIdentification.piN_h, Nat.add_sub_cancel] using this

end
end OddMath.Frontier.EKLSectionTwo
