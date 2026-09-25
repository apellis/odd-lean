import OddMath.Frontier.CenterPoly
import OddMath.Frontier.OddSchurPieri
import OddMath.Frontier.ElementaryBranching
import OddMath.Frontier.NonadjacentDivided

/-! EKL arXiv:1111.1320v1, §2.1–§2.2: small items.

* (2.6), p.4, in every rank `a ≥ 2` and at every adjacent pair.
* (2.11), p.5: the multiplication operators `ψ_k` form a chain homotopy from the identity
  to zero.
* Proof of Proposition 2.2, p.8: the printed "highest order term of `ε_α` is `x^α` with
  coefficient 1" fails already for `α = (2)`: the lexicographically highest monomial of `ε₂`
  is `x₁x₂ = x^{ᾱ}`, with coefficient `-1`, and `x₁²` does not occur.
* (2.45), p.11, with `∂_{w₀} = D_a` as fixed in (2.56).
* Remark 2.17, p.14: for `a ≥ 3`, no `s_j` preserves `OΛ_a`; indeed `s_j(ε₁) ∉ OΛ_a`.
* §2.1.1, p.4: `x₁² + x₂² = (x₁ - x₂)² = (x₁ + x₂)²`, with `x₁ - x₂ ≠ ±(x₁ + x₂)`.
* (2.59), p.15: `∂_{1,3}(ε₁) = 2` for `a ≥ 3`, so `ker ∂_{1,3} ⊉ OΛ_a`.
* (2.34), p.10, with the index misprint `h_{k-j}` read as `h_{m-j}`. -/
namespace OddMath.Frontier.EKLSectionTwo
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open AllRankDivided OddSymmetricKernel FiniteCompleteElementary
open scoped BigOperators
noncomputable section

/-! ### (2.6) -/

section BasicFormulae
variable {n : ℕ} (i : Fin (n+1))

local notation "xl" => generator i.castSucc
local notation "xr" => generator i.succ

/-- (2.6): `∂_i(x_i - x_{i+1}) = 0`. -/
theorem divided_difference_linear : divided i (xl - xr) = 0 := by
  rw [map_sub, divided_generator, divided_generator]; simp

/-- (2.6): `∂_i(x_i x_{i+1}) = 0`. -/
theorem divided_product_pair : divided i (xl * xr) = 0 := by
  simpa using LongestDivided.divided_balanced i 1

/-- (2.6): `∂_i(x_i^m x_{i+1}^m) = 0`. -/
theorem divided_balanced_power (m : ℕ) : divided i (xl ^ m * xr ^ m) = 0 :=
  LongestDivided.divided_balanced i m

/-- (2.6): `∂_i(x_i^m) = Σ_{j<m} (-1)^j x_{i+1}^j x_i^{m-1-j}`. -/
theorem divided_left_power (m : ℕ) :
    divided i (xl ^ m) = ∑ j ∈ Finset.range m, (-1 : ℤ) ^ j • (xr ^ j * xl ^ (m - 1 - j)) := by
  induction m with
  | zero => simp [divided_one]
  | succ m ih =>
    have key : ∀ j ∈ Finset.range m,
        (-1 : ℤ) ^ (j + 1) • (xr ^ (j + 1) * xl ^ (m + 1 - 1 - (j + 1))) =
          -(xr * ((-1 : ℤ) ^ j • (xr ^ j * xl ^ (m - 1 - j)))) := by
      intro j hj
      rw [mul_smul_comm, ← mul_assoc, ← pow_succ', pow_succ, mul_neg_one, neg_smul,
        show m + 1 - 1 - (j + 1) = m - 1 - j by omega]
    rw [pow_succ', divided_left_mul, ih, Finset.sum_range_succ', Finset.mul_sum,
      Finset.sum_congr rfl key, Finset.sum_neg_distrib]
    simp only [pow_zero, one_smul, one_mul, Nat.add_sub_cancel, Nat.sub_zero]
    abel

/-- (2.6): `∂_i(x_{i+1}^m) = Σ_{j<m} (-1)^j x_i^j x_{i+1}^{m-1-j}`. -/
theorem divided_right_power (m : ℕ) :
    divided i (xr ^ m) = ∑ j ∈ Finset.range m, (-1 : ℤ) ^ j • (xl ^ j * xr ^ (m - 1 - j)) := by
  induction m with
  | zero => simp [divided_one]
  | succ m ih =>
    have key : ∀ j ∈ Finset.range m,
        (-1 : ℤ) ^ (j + 1) • (xl ^ (j + 1) * xr ^ (m + 1 - 1 - (j + 1))) =
          -(xl * ((-1 : ℤ) ^ j • (xl ^ j * xr ^ (m - 1 - j)))) := by
      intro j hj
      rw [mul_smul_comm, ← mul_assoc, ← pow_succ', pow_succ, mul_neg_one, neg_smul,
        show m + 1 - 1 - (j + 1) = m - 1 - j by omega]
    rw [pow_succ', divided_right_mul, ih, Finset.sum_range_succ', Finset.mul_sum,
      Finset.sum_congr rfl key, Finset.sum_neg_distrib]
    simp only [pow_zero, one_smul, one_mul, Nat.add_sub_cancel, Nat.sub_zero]
    abel

/-- (2.6): `∂_i(x_i^{2m} + x_{i+1}^{2m}) = 0`. -/
theorem divided_even_power_sum (m : ℕ) : divided i (xl ^ (2 * m) + xr ^ (2 * m)) = 0 := by
  have h := (CenterPoly.second_claim i
    (MvPolynomial.X i.castSucc ^ m + MvPolynomial.X i.succ ^ m)).mpr (by
      rw [CenterPoly.s_squareHom]
      simp only [map_add, map_pow, MvPolynomial.rename_X, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
      exact add_comm _ _)
  simpa only [map_add, map_pow, CenterPoly.squareHom_X, ← pow_mul] using h

end BasicFormulae

/-! ### (2.11) -/

/-- The multiplication operators `ψ_k` of (2.11): `x_i` for `k` even, `x_{i+1}` for `k` odd. -/
def psi {n : ℕ} (i : Fin (n+1)) (k : ℕ) : SkewPolynomial (n+2) :=
  if Even k then generator i.castSucc else generator i.succ

/-- (2.11): `∂_i ψ_{k+1} + ψ_k ∂_i = id`, on all of `OPol_a`. -/
theorem psi_homotopy {n : ℕ} (i : Fin (n+1)) (k : ℕ) (f : SkewPolynomial (n+2)) :
    divided i (psi i (k+1) * f) + psi i k * divided i f = f := by
  unfold psi
  rcases Nat.even_or_odd k with hk | hk
  · rw [if_neg (Nat.not_even_iff_odd.mpr hk.add_one), if_pos hk, divided_right_mul]; abel
  · rw [if_pos hk.add_one, if_neg (Nat.not_even_iff_odd.mpr hk), divided_left_mul]; abel

/-- (2.11) in degree 0: `∂_i ψ_0 = id` on constants. -/
theorem psi_homotopy_zero {n : ℕ} (i : Fin (n+1)) (c : ℤ) :
    divided i (psi i 0 * (c • 1 : SkewPolynomial (n+2))) = c • 1 := by
  have h := psi_homotopy i 0 (c • 1 : SkewPolynomial (n+2))
  rw [map_smul, divided_one, smul_zero, mul_zero, add_zero] at h
  unfold psi at h ⊢
  rw [if_neg (by decide)] at h
  rw [if_pos (by decide), divided_left_mul, map_smul, divided_one, smul_zero, mul_zero,
    sub_zero]

/-! ### The leading term in the proof of Proposition 2.2 -/

/-- `ε₂` has coefficient `-1` at `x₁x₂`, in every rank `a ≥ 2`. -/
theorem elementary_two_coeff_pair (n : ℕ) :
    elementaryPoly (n+2) 2 (fun j => if j.val < 2 then 1 else 0) = -1 := by
  classical
  rw [OddSchurPieri.elementary_subsets, Finsupp.finset_sum_apply,
    Finset.sum_eq_single (OddSchurPieri.initial (n+2) 2)]
  · rw [OddSchurPieri.subsetTilde, OddSchurPieri.initial_weight _ _ (by omega)]
    have : OddSchurPieri.subsetExp (OddSchurPieri.initial (n+2) 2) =
        fun j : Fin (n+2) => if j.val < 2 then 1 else 0 := by
      funext j; simp [OddSchurPieri.subsetExp, OddSchurPieri.initial]
    rw [this, Finsupp.smul_apply, Finsupp.single_eq_same]
    norm_num
  · intro I hI hne
    rw [OddSchurPieri.subsetTilde, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
    intro he
    apply hne
    ext j
    have := congrFun he j
    simp only [OddSchurPieri.subsetExp, OddSchurPieri.initial, Finset.mem_filter,
      Finset.mem_univ, true_and] at this ⊢
    split_ifs at this <;> simp_all
  · intro h
    exact absurd (by simp [OddSchurPieri.initial_card _ _ (by omega : 2 ≤ n+2)]) h

/-- `x₁²` does not occur in `ε₂`, in every rank `a ≥ 2`. -/
theorem elementary_two_coeff_square (n : ℕ) :
    elementaryPoly (n+2) 2 (fun j => if j.val = 0 then 2 else 0) = 0 := by
  obtain ⟨c, _, hl⟩ := ElementaryGeneration.elementary_leading (n+2) 2 (by omega)
  by_contra hne
  have h := hl.1 _ hne
  have hlt : toLex (ElementaryGeneration.prefixExp (n+2) 2) <
      toLex (fun j : Fin (n+2) => if j.val = 0 then 2 else 0) :=
    ⟨⟨0, by omega⟩, fun j hj => absurd (Fin.lt_def.mp hj) (by simp),
      by simp [ElementaryGeneration.prefixExp]⟩
  exact absurd h (not_le.mpr hlt)

/-- The printed leading-term claim fails for `α = (2)`: the coefficient of `x^α = x₁²`
in `ε_α = ε₂` is `0`, not `1`. -/
theorem printed_leading_term_false (n : ℕ) :
    elementaryPoly (n+2) 2 (fun j => if j.val = 0 then 2 else 0) ≠ 1 := by
  rw [elementary_two_coeff_square]; norm_num

/-! ### (2.45) -/

theorem applyWord_const (n : ℕ) (c : ℤ) (w : List (Fin (n+1))) :
    LongestDivided.applyWord w (c • (1 : SkewPolynomial (n+2))) =
      if w = [] then c • 1 else 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [LongestDivided.applyWord_cons, ih, if_neg (List.cons_ne_nil i w)]
    split_ifs
    · rw [map_smul, divided_one, smul_zero]
    · exact map_zero _

/-- (2.45) with `s_e = D_a(x^δ)`: `(x^A ∂_w)(s_e) = (-1)^{C(a,3)} x^A` for the empty word and
`0` for every nonempty word. -/
theorem schubert_identity_action (n : ℕ) (A : SkewPolynomial (n+2)) (w : List (Fin (n+1))) :
    A * LongestDivided.applyWord w (LongestDivided.D (n+2) (LongestDivided.staircase (n+2))) =
      if w = [] then (-1 : ℤ) ^ (n+2).choose 3 • A else 0 := by
  rw [LongestDivided.D_staircase, applyWord_const]
  split_ifs
  · rw [mul_smul_comm, mul_one]
  · rw [mul_zero]

/-! ### Remark 2.17 -/

theorem elementary_one_eq (N : ℕ) :
    elementaryPoly N 1 = ∑ j : Fin N, PlacticEvaluation.tildeGenerator j := by
  classical
  unfold elementaryPoly
  rw [← (Equiv.funUnique (Fin 1) (Fin N)).symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hm : StrictMono ((Equiv.funUnique (Fin 1) (Fin N)).symm j) := fun a b h => by
    rw [Subsingleton.elim a b] at h; exact absurd h (lt_irrefl _)
  rw [if_pos hm]
  simp

theorem swap_val {n : ℕ} (j : Fin (n+1)) (k : Fin (n+2)) :
    (Equiv.swap j.castSucc j.succ k).val =
      if k.val = j.val then j.val + 1 else if k.val = j.val + 1 then j.val else k.val := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h3 h4 <;> simp_all [Fin.ext_iff]

theorem divided_s_tilde {n : ℕ} (m j : Fin (n+1)) (k : Fin (n+2)) :
    divided m (s j (PlacticEvaluation.tildeGenerator k)) =
      if (Equiv.swap j.castSucc j.succ k).val = m.val ∨
        (Equiv.swap j.castSucc j.succ k).val = m.val + 1
      then -((-1 : ℤ) ^ k.val • 1) else 0 := by
  rw [PlacticEvaluation.tildeGenerator, map_zsmul, s_generator, smul_neg, map_neg, map_zsmul,
    divided_generator]
  simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> simp

theorem smul_one_ne_zero {N : ℕ} {c : ℤ} (hc : c ≠ 0) : (c • 1 : SkewPolynomial N) ≠ 0 := by
  intro h
  have := congrArg (fun f : SkewPolynomial N => f 0) h
  change c * (1 : SkewPolynomial N) 0 = 0 at this
  rw [show (1 : SkewPolynomial N) 0 = 1 from Finsupp.single_eq_same, mul_one] at this
  exact hc this

theorem divided_s_elementary_one {n : ℕ} (m j : Fin (n+1)) (a b : Fin (n+2)) (hab : a ≠ b)
    (hin : ∀ k : Fin (n+2), ((Equiv.swap j.castSucc j.succ k).val = m.val ∨
      (Equiv.swap j.castSucc j.succ k).val = m.val + 1) ↔ (k = a ∨ k = b))
    (hpar : (-1 : ℤ) ^ a.val = (-1 : ℤ) ^ b.val) :
    divided m (s j (elementaryPoly (n+2) 1)) = (-(2 * (-1 : ℤ) ^ a.val)) • 1 := by
  classical
  rw [elementary_one_eq, map_sum, map_sum, Fintype.sum_eq_add a b hab]
  · rw [divided_s_tilde, divided_s_tilde, if_pos ((hin a).mpr (Or.inl rfl)),
      if_pos ((hin b).mpr (Or.inr rfl)), ← hpar, ← neg_add, ← add_smul, ← two_mul, neg_smul]
  · rintro k ⟨hka, hkb⟩
    rw [divided_s_tilde, if_neg]
    rw [hin k]
    rintro (h | h) <;> contradiction

/-- Remark 2.17: for `a ≥ 3`, every `s_j` moves `ε₁` out of `OΛ_a`. -/
theorem s_elementary_one_not_mem (n : ℕ) (j : Fin (n+2)) :
    s j (elementaryPoly (n+3) 1) ∉ kernelSubring (n+1) := by
  intro hmem
  have hjl := j.isLt
  by_cases hj : j.val = 0
  · have h := divided_s_elementary_one (⟨1, by omega⟩ : Fin (n+2)) j ⟨0, by omega⟩ ⟨2, by omega⟩
      (by simp [Fin.ext_iff]) (fun k => by
        rw [swap_val, Fin.ext_iff, Fin.ext_iff]
        simp only [hj]
        split_ifs <;> constructor <;> intro h <;> first | omega | simp at h) (by norm_num)
    rw [hmem ⟨1, by omega⟩] at h
    exact smul_one_ne_zero (by norm_num) h.symm
  · have h := divided_s_elementary_one (⟨j.val - 1, by omega⟩ : Fin (n+2)) j
      ⟨j.val - 1, by omega⟩ ⟨j.val + 1, by omega⟩
      (by simp [Fin.ext_iff]) (fun k => by
        rw [swap_val, Fin.ext_iff, Fin.ext_iff]
        simp only
        split_ifs <;> constructor <;> intro h <;> omega) (by
          change (-1 : ℤ) ^ (j.val - 1) = (-1 : ℤ) ^ (j.val + 1)
          rw [show j.val + 1 = (j.val - 1) + 2 by omega, pow_add]; norm_num)
    rw [hmem ⟨j.val - 1, by omega⟩] at h
    exact smul_one_ne_zero (by
      rcases neg_one_pow_eq_or ℤ (j.val - 1) with h1 | h1 <;> simp [h1]) h.symm

/-! ### Non-unique factorization, p.4 -/

theorem sum_squares_factorizations (n : ℕ) :
    (generator (0 : Fin (n+2)) - generator 1) ^ 2 =
        generator (0 : Fin (n+2)) ^ 2 + generator 1 ^ 2 ∧
      (generator (0 : Fin (n+2)) + generator 1) ^ 2 =
        generator (0 : Fin (n+2)) ^ 2 + generator 1 ^ 2 := by
  have hc : generator (0 : Fin (n+2)) * generator 1 = -(generator 1 * generator 0) :=
    OddMath.SkewPolynomial.generator_anticommute (0 : Fin (n+2)) 1 (by simp [Fin.ext_iff])
  constructor
  · rw [sq, sq, sq, sub_mul, mul_sub, mul_sub, hc]; abel
  · rw [sq, sq, sq, add_mul, mul_add, mul_add, hc]; abel

theorem factors_not_associate (n : ℕ) (u : ℤ) (hu : u = 1 ∨ u = -1) :
    generator (0 : Fin (n+2)) - generator 1 ≠ u • (generator (0 : Fin (n+2)) + generator 1) := by
  intro h
  have h0 := congrArg (fun f : SkewPolynomial (n+2) => f (expSingle 0)) h
  have h1 := congrArg (fun f : SkewPolynomial (n+2) => f (expSingle 1)) h
  have hne : expSingle (0 : Fin (n+2)) ≠ expSingle 1 := by
    intro he
    have := congrFun he 0
    simp [expSingle, Fin.ext_iff] at this
  simp only [generator, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hne.symm,
    smul_eq_mul] at h0 h1
  rcases hu with rfl | rfl <;> omega

/-! ### (2.59): a nonadjacent divided difference not killing `OΛ_a` -/

/-- `∂_{1,3}(ε₁) = 2` in every rank `a ≥ 3`. -/
theorem dividedPair_elementary_one (n : ℕ) :
    NonadjacentDivided.dividedPair (0 : Fin (n+3)) ⟨2, by omega⟩ (by simp [Fin.ext_iff])
      (elementaryPoly (n+3) 1) = (2 : ℤ) • 1 := by
  classical
  rw [elementary_one_eq, map_sum,
    Fintype.sum_eq_add (0 : Fin (n+3)) ⟨2, by omega⟩ (by simp [Fin.ext_iff])]
  · simp only [PlacticEvaluation.tildeGenerator, map_zsmul, NonadjacentDivided.divided_generator]
    simp [two_smul]
  · rintro k ⟨h0, h2⟩
    simp only [PlacticEvaluation.tildeGenerator, map_zsmul, NonadjacentDivided.divided_generator,
      if_neg (not_or.mpr ⟨h0, h2⟩), smul_zero]

theorem elementary_one_not_mem_ker_pair (n : ℕ) :
    NonadjacentDivided.dividedPair (0 : Fin (n+3)) ⟨2, by omega⟩ (by simp [Fin.ext_iff])
      (elementaryPoly (n+3) 1) ≠ 0 := by
  rw [dividedPair_elementary_one]
  exact smul_one_ne_zero (by norm_num)

/-! ### (2.34) -/

section Last
open FiniteWords
variable {R : Type*} [Ring R]

/-- Weakly increasing words split by the number of occurrences of the last letter. -/
theorem weakSum_last (N : ℕ) : ∀ (x : Fin (N+1) → R) (m : ℕ),
    weakSum x m = ∑ j ∈ Finset.range (m+1),
      weakSum (fun i => x i.castSucc) (m - j) * x (Fin.last N) ^ j := by
  induction N with
  | zero =>
    intro x m
    have hx : ∀ m, weakSum x m = x 0 ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [weakSum_succ, ih, weakSum_empty, add_zero, pow_succ']
    rw [hx, Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp
    · intro j hj
      have := Finset.mem_range.mp hj
      rw [show m - j = (m - j - 1) + 1 by omega, weakSum_empty, zero_mul]
  | succ N ih =>
    intro x m
    induction m with
    | zero => simp
    | succ m ihm =>
      have hL : x (Fin.last N).succ = x (Fin.last (N+1)) := rfl
      have hsplit : ∀ k, weakSum (fun i : Fin (N+1) => x i.castSucc) (k+1) =
          x 0 * weakSum (fun i : Fin (N+1) => x i.castSucc) k +
            weakSum (fun i : Fin N => x i.castSucc.succ) (k+1) := by
        intro k; rw [weakSum_succ]; simp only [Fin.succ_castSucc]; rfl
      rw [weakSum_succ, ihm, ih (fun i => x i.succ) (m+1), hL, Finset.mul_sum,
        Finset.sum_range_succ (n := m+1), Finset.sum_range_succ (n := m+1)]
      simp only [Nat.sub_self, weakSum_zero, one_mul]
      have hs : ∑ j ∈ Finset.range (m+1), weakSum (fun i => x i.castSucc) (m + 1 - j) *
            x (Fin.last (N + 1)) ^ j =
          ∑ j ∈ Finset.range (m+1), weakSum (fun i => x i.castSucc.succ) (m + 1 - j) *
            x (Fin.last (N + 1)) ^ j +
          ∑ j ∈ Finset.range (m+1), x 0 * (weakSum (fun i => x i.castSucc) (m - j) *
            x (Fin.last (N + 1)) ^ j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have := Finset.mem_range.mp hj
        rw [show m + 1 - j = (m - j) + 1 by omega, hsplit, add_mul, mul_assoc]
        abel
      rw [hs]
      abel

/-- (2.34), with the index misprint `h_{k-j}` read as `h_{m-j}`:
`h_m^{(a)} = Σ_{j=0}^m h_{m-j}^{(a-1)} x̃_a^j`, in every rank. -/
theorem complete_last (N m : ℕ) :
    completePoly (N+1) m = ∑ j ∈ Finset.range (m+1),
      ElementaryBranching.«prefix» N (completePoly N (m - j)) *
        ElementaryBranching.lastTilde N ^ j := by
  classical
  have hp : ∀ k, ElementaryBranching.«prefix» N (completePoly N k) =
      weakSum (fun i : Fin N => PlacticEvaluation.tildeGenerator i.castSucc) k := by
    intro k
    rw [completePoly_eq_weakSum]
    simp only [weakSum, word, map_sum, map_list_prod, List.map_ofFn, Function.comp_def,
      ElementaryBranching.prefix_tilde]
  simp only [hp]
  rw [completePoly_eq_weakSum, weakSum_last]
  rfl

end Last

end
end OddMath.Frontier.EKLSectionTwo
