import OddMath.Frontier.OnhPolynomial
import OddMath.Frontier.MonomialReversal
import OddMath.Frontier.LongestFactor

/-! # Dotted thick strands and odd Schur polynomials

EKL arXiv:1111.1320v1, §4.1.2 Definition 4.3, (4.7)–(4.11); §4.2.1 (4.17)–(4.22);
Definition 4.10; pp. 32–38.  Rank `a = n+2`, with `ONH_a = NilHeckeAction.Presented n`.

* The normal-ordering sign `x^α x^{δ_a} = (-1)^{C(a,3)+χ^a_α} x^{α+δ_a}`, with `χ^a_α`
  of (4.20).
* The odd Schur polynomial (4.17) and its normal-ordered form (4.19); it is the library's
  `OddSymmetrizer.schur` (EKL (2.69)).  The dual Schur polynomial of Definition 4.10.
* For `f ∈ OΛ_a`: (4.8), (4.9) `e_a f e_a = e_a f`, and (4.10)/(4.11)
  `(e_a g e_a)(e_a f e_a) = e_a g f e_a`.  Products `x y` are drawn with `x` on top of `y`.
* (4.21)–(4.22) `e_a s_α e_a = (-1)^{χ^a_α} e_a x^{α+δ_a} D_a`, and the analogue for `ŝ_α`
  stated after Definition 4.10.
* Top-degree sandwiches: if `D_a(g) = c` then `D_a g D_a = c D_a` and `e_a g D_a = c e_a`. -/
namespace OddMath.Frontier.ThickDots
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open NilHeckeAction LongestDivided SignedPermutation ZeroHecke OnhPolynomial

variable {n : ℕ}

/-! ## The normal-ordering sign (4.20) -/

/-- The staircase exponent `δ_a = (a-1, …, 1, 0)`, indexed from `0`. -/
def delta (n : ℕ) : Fin (n+2) → ℕ := fun i => n+1-i.val

theorem staircase_eq : staircase (n+2) = monomial (delta n) 1 := rfl

/-- EKL (4.20): `χ^a_α = C(a,3) + |α| C(a,2) + Σ_j α_j C(a-j+1,2)` (1-based `j`). -/
def chi (α : Fin (n+2) → ℕ) : ℕ :=
  (n+2).choose 3 + (∑ k, α k) * (n+2).choose 2 + ∑ k, α k * (n+2-k.val).choose 2

private theorem range_sum_add_choose (k : ℕ) (hk : k ≤ n+2) :
    ∑ j ∈ Finset.range k, (n+1-j) + (n+2-k).choose 2 = (n+2).choose 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, n+2-k = m+1 := ⟨n+1-k, by omega⟩
    have hm' : n+2-(k+1) = m := by omega
    have hc : (m+1).choose 2 = m + m.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    rw [Finset.sum_range_succ, ← ih (by omega), hm, hm', hc]
    omega

private theorem sum_lt_eq_range (i : Fin (n+2)) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (n+2) => j < i), (n+1-j.val) =
      ∑ j ∈ Finset.range i.val, (n+1-j) := by
  rw [Finset.sum_filter]
  simp only [Fin.lt_iff_val_lt_val]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < i.val then n+1-j else 0), ← Finset.sum_filter,
    Finset.range_eq_Ico, Finset.Ico_filter_lt, min_eq_right (by omega)]

theorem crossingCount_delta (α : Fin (n+2) → ℕ) :
    OddMath.crossingCount α (delta n) + ∑ k, α k * (n+2-k.val).choose 2 =
      (∑ k, α k) * (n+2).choose 2 := by
  rw [OddMath.crossingCount, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← mul_add]
  simp only [delta]
  rw [sum_lt_eq_range, range_sum_add_choose i.val (by omega)]

private theorem sign_double (a b : ℕ) : (-1 : ℤ)^(a + 2*b) = (-1)^a := by
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- `(-1)^{C(a,3)} (-1)^{χ^a_α}` is the sign normal-ordering `x^α x^{δ_a}`
(EKL, after (4.20)). -/
theorem skewSign_delta (α : Fin (n+2) → ℕ) :
    OddMath.skewSign α (delta n) = (-1 : ℤ)^((n+2).choose 3 + chi α) := by
  have h := crossingCount_delta α
  have e : (n+2).choose 3 + chi α = OddMath.crossingCount α (delta n) +
      2 * ((n+2).choose 3 + ∑ k, α k * (n+2-k.val).choose 2) := by
    unfold chi; omega
  rw [OddMath.skewSign, e, sign_double]

theorem monomial_mul_staircase (α : Fin (n+2) → ℕ) (c : ℤ) :
    monomial α c * staircase (n+2) =
      (-1 : ℤ)^((n+2).choose 3 + chi α) • monomial (α + delta n) c := by
  rw [staircase_eq, MonomialReversal.monomial_mul_monomial, skewSign_delta, mul_one,
    Finsupp.smul_single, smul_eq_mul, mul_comm]

/-! ## Odd Schur and dual Schur polynomials -/

/-- EKL (4.17): `s_α = (-1)^{C(a,3)} (D_a(x^α x^{δ_a}))^{w_0}`. -/
noncomputable def schur (α : Fin (n+2) → ℕ) : SkewPolynomial (n+2) :=
  (-1 : ℤ)^((n+2).choose 3) •
    skewAction (LongestElementary.longest (n+2)) (D (n+2) (monomial α 1 * staircase (n+2)))

/-- (4.17) is the odd Schur polynomial of EKL (2.69). -/
theorem schur_eq_oddSymmetrizer (α : OddSymmetrizer.PartitionExponent n) :
    schur α.val = OddSymmetrizer.schur n α := rfl

/-- EKL (4.19): `s_α = (-1)^{χ^a_α} (D_a(x^{δ_a+α}))^{w_0}`. -/
theorem schur_eq (α : Fin (n+2) → ℕ) :
    schur α = (-1 : ℤ)^(chi α) •
      skewAction (LongestElementary.longest (n+2)) (D (n+2) (monomial (α + delta n) 1)) := by
  rw [schur, monomial_mul_staircase, map_zsmul, map_zsmul, smul_smul, ← pow_add,
    show (n+2).choose 3 + ((n+2).choose 3 + chi α) = chi α + 2 * (n+2).choose 3 by ring,
    sign_double]

/-- EKL Definition 4.10:
`ŝ_α = (-1)^{χ^a_α} (D_a(x_1^{α_a} x_2^{1+α_{a-1}} ⋯ x_a^{a-1+α_1}))^{w_0}`. -/
noncomputable def dualSchur (α : Fin (n+2) → ℕ) : SkewPolynomial (n+2) :=
  (-1 : ℤ)^(chi α) • skewAction (LongestElementary.longest (n+2))
    (D (n+2) (monomial (fun k => k.val + α (Fin.rev k)) 1))

theorem reversal_D_mem_kernel (g : SkewPolynomial (n+2)) :
    skewAction (LongestElementary.longest (n+2)) (D (n+2) g) ∈
      OddSymmetricKernel.kernelSubring n :=
  LongestElementary.action_mem_kernel n _ (LongestKernel.D_mem_kernel n g)

theorem schur_mem_kernel (α : Fin (n+2) → ℕ) :
    schur α ∈ OddSymmetricKernel.kernelSubring n :=
  Subring.zsmul_mem _ (reversal_D_mem_kernel _) _

theorem dualSchur_mem_kernel (α : Fin (n+2) → ℕ) :
    dualSchur α ∈ OddSymmetricKernel.kernelSubring n :=
  Subring.zsmul_mem _ (reversal_D_mem_kernel _) _

/-! ## Dotted thick strands (Definition 4.3) -/

/-- `e_a f = (-1)^{C(a,3)} x^{δ_a} f^{w_0} D_a` for `f ∈ OΛ_a` (Prop 3.5 and (2.64)). -/
theorem projector_mul_poly (f : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    projector n * polyElem n f = (-1 : ℤ)^((n+2).choose 3) •
      (staircaseElem n * polyElem n (skewAction (LongestElementary.longest (n+2)) f) *
        DElem n) := by
  rw [prop_3_5, smul_mul_assoc, mul_assoc, DElem_poly_kernel f hf, ← mul_assoc]

/-- EKL (4.8): `e_a f e_a = (-1)^{C(a,3)} x^{δ_a} f^{w_0} D_a` for `f ∈ OΛ_a`. -/
theorem projector_poly_projector (f : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    projector n * polyElem n f * projector n = (-1 : ℤ)^((n+2).choose 3) •
      (staircaseElem n * polyElem n (skewAction (LongestElementary.longest (n+2)) f) *
        DElem n) := by
  rw [projector_mul_poly f hf, smul_mul_assoc, mul_assoc _ (DElem n), DElem_mul_projector]

/-- EKL (4.9): `e_a f e_a = e_a f` for `f ∈ OΛ_a`. -/
theorem projector_poly_projector_eq (f : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    projector n * polyElem n f * projector n = projector n * polyElem n f := by
  rw [projector_poly_projector f hf, projector_mul_poly f hf]

/-- EKL (4.10)/(4.11): `(e_a g e_a)(e_a f e_a) = e_a g f e_a` for `g ∈ OΛ_a`. -/
theorem thick_mul (g f : SkewPolynomial (n+2))
    (hg : g ∈ OddSymmetricKernel.kernelSubring n) :
    (projector n * polyElem n g * projector n) * (projector n * polyElem n f * projector n) =
      projector n * polyElem n (g * f) * projector n := by
  simp only [← mul_assoc]
  rw [mul_assoc (projector n * polyElem n g) (projector n) (projector n),
    projector_mul_projector, projector_poly_projector_eq g hg, map_mul, mul_assoc (projector n)]

/-! ## Exploded Schur polynomials (4.21)–(4.22) -/

/-- `e_a (D_a g)^{w_0} e_a = e_a g D_a` for every polynomial `g`. -/
theorem projector_reversal_D_projector (g : SkewPolynomial (n+2)) :
    projector n * polyElem n (skewAction (LongestElementary.longest (n+2)) (D (n+2) g)) *
        projector n = projector n * polyElem n g * DElem n := by
  rw [projector_poly_projector _ (reversal_D_mem_kernel g), LongestElementary.action_involutive,
    prop_3_5, smul_mul_assoc, smul_mul_assoc, mul_assoc (staircaseElem n) (DElem n) (polyElem n g),
    mul_assoc (staircaseElem n) (DElem n * polyElem n g), DElem_poly_DElem, mul_assoc]

/-- EKL (4.21)–(4.22): `e_a s_α e_a = (-1)^{χ^a_α} e_a x^{α+δ_a} D_a`. -/
theorem projector_schur_projector (α : Fin (n+2) → ℕ) :
    projector n * polyElem n (schur α) * projector n =
      (-1 : ℤ)^(chi α) • (projector n * polyElem n (monomial (α + delta n) 1) * DElem n) := by
  rw [schur_eq, map_zsmul, mul_smul_comm, smul_mul_assoc, projector_reversal_D_projector]

/-- EKL, after Definition 4.10:
`e_a ŝ_α e_a = (-1)^{χ^a_α} e_a x_1^{α_a} x_2^{1+α_{a-1}} ⋯ x_a^{a-1+α_1} D_a`. -/
theorem projector_dualSchur_projector (α : Fin (n+2) → ℕ) :
    projector n * polyElem n (dualSchur α) * projector n =
      (-1 : ℤ)^(chi α) •
        (projector n * polyElem n (monomial (fun k => k.val + α (Fin.rev k)) 1) * DElem n) := by
  rw [dualSchur, map_zsmul, mul_smul_comm, smul_mul_assoc, projector_reversal_D_projector]

/-! ## Top-degree sandwiches -/

/-- If `D_a(g) = c`, then `D_a g D_a = c D_a`. -/
theorem DElem_poly_DElem_of_D_eq (g : SkewPolynomial (n+2)) (c : ℤ)
    (h : D (n+2) g = c • 1) :
    DElem n * polyElem n g * DElem n = c • DElem n := by
  rw [DElem_poly_DElem, h, map_zsmul, map_one, smul_mul_assoc, one_mul]

/-- If `D_a(g) = c`, then `x^{δ_a} D_a g D_a = c x^{δ_a} D_a`. -/
theorem staircase_DElem_poly_DElem (g : SkewPolynomial (n+2)) (c : ℤ)
    (h : D (n+2) g = c • 1) :
    staircaseElem n * DElem n * polyElem n g * DElem n = c • (staircaseElem n * DElem n) := by
  rw [mul_assoc (staircaseElem n) (DElem n), mul_assoc (staircaseElem n),
    DElem_poly_DElem_of_D_eq g c h, mul_smul_comm]

/-- If `D_a(g) = c`, then `e_a g D_a = c e_a`. -/
theorem projector_poly_DElem (g : SkewPolynomial (n+2)) (c : ℤ) (h : D (n+2) g = c • 1) :
    projector n * polyElem n g * DElem n = c • projector n := by
  rw [prop_3_5, smul_mul_assoc, smul_mul_assoc, staircase_DElem_poly_DElem g c h, smul_comm]

/-- Top-degree monomials: `e_a x^γ D_a = D_a(x^γ) e_a` when `|γ| = C(a,2)`. -/
theorem projector_monomial_DElem (γ : Fin (n+2) → ℕ) (hγ : ∑ j, γ j = (n+2).choose 2) :
    projector n * polyElem n (monomial γ 1) * DElem n =
      (D (n+2) (monomial γ 1) 0) • projector n :=
  projector_poly_DElem _ _ (LongestFactor.D_monomial_top_degree (n+2) γ 1 hγ)

end OddMath.Frontier.ThickDots
