import OddMath.Frontier.OddCategorificationRank
import OddMath.Frontier.QuantumSl2Plus

/-!
# (6.1)–(6.2) in `K₀(ONH_{a+b})`: `[ONH_a] = [a]! [E^{(a)}]`, `[E^{(a)}E^{(b)}] = [a+b, a] [E^{(a+b)}]`

EKL arXiv:1111.1320v1, §6, pp. 46–47. Here `a + b = n+2`, `e_a ⊗ e_b =
ThickBubble.blockE n 0 a * ThickBubble.blockE n a b` (a degree-zero idempotent of `ONH_{a+b}`),
and the induction of `E^{(a)} ⊠ E^{(b)}` is the graded projective
`E^{(a)}E^{(b)} = ONH_{a+b}(e_a ⊗ e_b){C(a,2) + C(b,2)}` (`indE`).

* `eq_6_2_K0`: `[E^{(a)}E^{(b)}] = [a+b, a] [E^{(a+b)}]`, from the degree-zero Murray–von Neumann
  equivalence `ONH_{a+b}(e_a ⊗ e_b) ≅ ⊕_{α ∈ P(a,b)} ONH_{a+b} e_{a+b}{2ab - 2|α|}` given by the
  row `(σ_α)` and column `(λ_α)` of `Categorification.split62` (degrees `±2(|α| - ab)`), and the
  symmetry `|α| ↦ ab - |α|` of `P(a,b)` (`sum_box_compl`).
* `eq_6_1_qFact`: `[ONH_a] = [a]! [E^{(a)}]`, i.e. `∑_{ℓ ∈ Sq(a)} q^{C(a,2) - 2|ℓ|} = [a]!`.
-/

noncomputable section
open Matrix LaurentPolynomial

namespace OddMath.Frontier.OddCategorification
open GradedK0 NilHeckeAction NilHeckeGrading BoxPartitionCount QuantumSl2Plus

/-! ### The complement symmetry of `P(a,b)` -/

/-- The complement `k ↦ b - α_{a-1-k}` of `α` in the `a × b` box. -/
def boxCompl (b : ℕ) {a : ℕ} (α : Fin a → ℕ) : Fin a → ℕ := fun k => b - α (Fin.rev k)

theorem boxCompl_mem {a b : ℕ} {α : Fin a → ℕ} (hα : α ∈ box a b) : boxCompl b α ∈ box a b := by
  rw [mem_box] at hα ⊢
  refine ⟨fun k k' hk => Nat.sub_le_sub_left (hα.1 (Fin.rev_le_rev.2 hk)) b, fun k => ?_⟩
  exact Nat.sub_le _ _

theorem boxCompl_boxCompl {a b : ℕ} {α : Fin a → ℕ} (hα : α ∈ box a b) :
    boxCompl b (boxCompl b α) = α := by
  funext k
  simp only [boxCompl, Fin.rev_rev]
  exact Nat.sub_sub_self ((mem_box.1 hα).2 k)

theorem sum_boxCompl {a b : ℕ} {α : Fin a → ℕ} (hα : α ∈ box a b) :
    ((∑ k, boxCompl b α k : ℕ) : ℤ) = (a : ℤ) * b - ((∑ k, α k : ℕ) : ℤ) := by
  have h : ∑ k, boxCompl b α k = ∑ k, (b - α k) :=
    Equiv.sum_comp Fin.revPerm (fun k => b - α k)
  rw [h, Nat.cast_sum, Nat.cast_sum]
  simp only [Nat.cast_sub ((mem_box.1 hα).2 _), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `∑_{α ∈ P(a,b)} q^{c + 2ab - 2|α|} = ∑_{α ∈ P(a,b)} q^{c + 2|α|}`. -/
theorem sum_box_compl (a b : ℕ) (c : ℤ) :
    ∑ α ∈ box a b, (T (c + 2 * ((a : ℤ) * b) - 2 * ((∑ i, α i : ℕ) : ℤ)) : LaurentPolynomial ℤ) =
      ∑ α ∈ box a b, T (c + 2 * ((∑ i, α i : ℕ) : ℤ)) :=
  Finset.sum_nbij' (boxCompl b) (boxCompl b) (fun _ h => boxCompl_mem h)
    (fun _ h => boxCompl_mem h) (fun _ h => boxCompl_boxCompl h) (fun _ h => boxCompl_boxCompl h)
    (fun α h => by rw [sum_boxCompl h]; congr 1; ring)

/-! ### (6.2) -/

theorem of_divE (n : ℕ) :
    K0.of (divE n) = (T (((n+2).choose 2 : ℕ) : ℤ) : LaurentPolynomial ℤ) • K0.of (projE n 0) :=
  of_elem _ _ _

section Eq62
variable {n a b : ℕ}

/-- `E^{(a)}E^{(b)} = ONH_{a+b}(e_a ⊗ e_b){C(a,2) + C(b,2)}`, `a + b = n+2`: the induction of
`E^{(a)} ⊠ E^{(b)}`, realised by the idempotent `e_a ⊗ e_b = blockE n 0 a * blockE n a b`. -/
def indE (hab : a + b = n+2) : GIdem (onhGrading n) :=
  gelem (blockE_pair_mem n a b) (ThickDecomposition.blockE_pair_idem hab)
    ((a.choose 2 + b.choose 2 : ℕ) : ℤ)

/-- (6.2) in `K₀`, before normalization:
`[E^{(a)}E^{(b)}] = ∑_{α ∈ P(a,b)} q^{C(a,2)+C(b,2) - 2(|α| - ab)} [ONH_{a+b} e_{a+b}]`. -/
theorem of_indE_eq_sum (hab : a + b = n+2) :
    K0.of (indE hab) = ∑ α : box a b,
      (T (((a.choose 2 + b.choose 2 : ℕ) : ℤ) - 2 * ThickDecomposition.shift a b α.1) :
        LaurentPolynomial ℤ) • K0.of (projE n 0) :=
  of_elem_splitting (A := onhGrading n) (blockE_pair_mem n a b)
    (ThickDecomposition.blockE_pair_idem hab) (projector_mem n) ZeroHecke.projector_mul_projector
    (Categorification.split62 hab) (fun α => 2 * ThickDecomposition.shift a b α.1)
    (fun α => sigma62_mem hab α.1) (fun α => lam62_mem hab (Categorification.mem_box' α).2) _

/-- **EKL (6.2)** in `K₀(ONH_{a+b})`: `[E^{(a)}E^{(b)}] = [a+b, a] [E^{(a+b)}]`, for all
`a, b` with `a + b = n+2 ≥ 2`. -/
theorem eq_6_2_K0 (hab : a + b = n+2) :
    K0.of (indE hab) = qBinom a b • K0.of (divE n) := by
  rw [of_indE_eq_sum, of_divE, smul_smul, qBinom, Finset.sum_mul,
    Finset.sum_smul, ← Finset.sum_coe_sort (box a b)]
  refine (Finset.sum_congr rfl fun α _ => ?_).trans
    ((Finset.sum_coe_sort (box a b) fun α => (T (((a.choose 2 + b.choose 2 : ℕ) : ℤ) +
      2 * ((a : ℤ) * b) - 2 * ((∑ i, α i : ℕ) : ℤ)) : LaurentPolynomial ℤ) •
      K0.of (projE n 0)).trans ?_)
  · rw [ThickDecomposition.shift]
    congr 2
    push_cast
    ring
  rw [← Finset.sum_smul, sum_box_compl, Finset.sum_smul, ← Finset.sum_coe_sort (box a b)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← T_add]
  congr 2
  have hc : (((n+2).choose 2 : ℕ) : ℤ) = ((a.choose 2 + b.choose 2 : ℕ) : ℤ) + (a : ℤ) * b := by
    rw [← hab, BoxComplement.choose_two_add]
    push_cast
    ring
  rw [hc]
  push_cast
  ring

end Eq62

/-! ### `[ONH_a] = [a]! [E^{(a)}]` -/

theorem T_choose_two (a : ℕ) :
    (T ((a.choose 2 : ℕ) : ℤ) : LaurentPolynomial ℤ) = ∏ j ∈ Finset.range a, T (j : ℤ) := by
  induction a with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, ← T_add, Nat.choose_succ_succ', Nat.choose_one_right]
    congr 1
    push_cast
    ring

/-- `∑_{ℓ ∈ Sq(a)} q^{C(a,2) - 2|ℓ|} = [a]!`. -/
theorem sum_Sq_eq_qFact (a : ℕ) :
    ∑ ℓ ∈ Sq a, (T (((a.choose 2 : ℕ) : ℤ) - 2 * ((∑ ν, ℓ ν : ℕ) : ℤ)) : LaurentPolynomial ℤ) =
      qFact a := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℤ))
    (T (-2) : LaurentPolynomial ℤ)) (sum_Sq_eq_prod a)
  simp only [Polynomial.eval₂_finset_sum, Polynomial.eval₂_finset_prod, Polynomial.eval₂_X_pow,
    T_pow] at h
  have h' := congrArg (fun p => (T ((a.choose 2 : ℕ) : ℤ) : LaurentPolynomial ℤ) * p) h
  simp only [Finset.mul_sum, ← T_add] at h'
  rw [show (∑ ℓ ∈ Sq a, (T (((a.choose 2 : ℕ) : ℤ) - 2 * ((∑ ν, ℓ ν : ℕ) : ℤ)) :
      LaurentPolynomial ℤ)) = ∑ ℓ ∈ Sq a, T (((a.choose 2 : ℕ) : ℤ) +
        ((∑ ν, ℓ ν : ℕ) : ℤ) * -2) from Finset.sum_congr rfl fun ℓ _ => by congr 1; ring, h',
    T_choose_two, ← Finset.prod_mul_distrib, qFact]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, qInt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← T_add]
  congr 1
  push_cast
  ring

/-- **EKL (6.1)** as `E^a = [a]! E^{(a)}`: `[ONH_a] = [a]! [E^{(a)}]` in `K₀(ONH_a)`. -/
theorem eq_6_1_qFact (n : ℕ) :
    K0.of (GIdem.single 0 : GIdem (onhGrading n)) = qFact (n+2) • K0.of (divE n) := by
  rw [eq_6_1_K0, ← Finset.sum_smul, ← sum_Sq_eq_qFact,
    Finset.sum_coe_sort (Sq (n+2)) fun ℓ => (T ((((n+2).choose 2 : ℕ) : ℤ) -
      2 * ((∑ ν, ℓ ν : ℕ) : ℤ)) : LaurentPolynomial ℤ)]

end OddMath.Frontier.OddCategorification
