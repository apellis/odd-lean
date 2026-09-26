import OddMath.Frontier.EKGeneralQNondeg
import OddMath.Frontier.EKGeneralQClassical
import OddMath.Frontier.EKRestEval

/-!
# A row-recursive evaluator for the form (2.1) at an integer value of `q`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1, (2.1) and Proposition 2.2.

For `t : ℤ`, `fastQ t β α` computes `(h_β, h_α)` at `q = t` by peeling off the first top
platform `β₁`: by Proposition 2.2 (adjointness) and the coproduct formula on words,
`(h_{β₁} h_{β'}, h_α) = Σ_{u ≤ α, |u| = β₁} t^{Σ_{l<j} u_j (α_l - u_l)} (h_{β'}, h_{α-u})`.

* `form_hWord_fastQ`: `form t (h_β) (h_α) = fastQ t β α` for all lists `β, α`;
* `gram_fastQ`: the entries of the Gram matrix `EKGeneralQ.gram t n`.
-/

noncomputable section
open scoped BigOperators TensorProduct

namespace OddMath.Frontier.EKFinal
open EKGeneralQ EKPairingMatrices

/-- Row-recursive evaluator for `(h_β, h_α)` at `q = t`. -/
def fastQ (t : ℤ) : List ℕ → List ℕ → ℤ
  | [], α => if α.sum = 0 then 1 else 0
  | b :: β, α => ((EKRest.splitsB b α).map (fun u =>
      t ^ EKRest.crossL u (List.zipWith (· - ·) α u) *
        fastQ t β (List.zipWith (· - ·) α u))).sum

theorem counit_vWord {c : ℕ} (α : Fin c → ℕ) :
    counit ℤ (vWord ℤ α) = if (∑ j, α j) = 0 then 1 else 0 := by
  induction c with
  | zero => simp [counit_one]
  | succ c ih =>
    rw [vWord_succ, counit_mul, counit_h, ih, Fin.sum_univ_succ]
    by_cases h0 : α 0 = 0
    · simp [h0]
    · rw [if_neg h0, zero_mul, if_neg (by omega)]

theorem form_vWord_fastQ (t : ℤ) {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    form t (vWord ℤ β) (vWord ℤ α) = fastQ t (List.ofFn β) (List.ofFn α) := by
  induction r generalizing c with
  | zero =>
    rw [vWord_nil, form_symm, form_right_one, counit_vWord, List.ofFn_zero, fastQ,
      List.sum_ofFn]
  | succ r ih =>
    rw [vWord_succ, ← adjointness, coproduct_vWord, map_sum, List.ofFn_succ, fastQ]
    simp only [map_smul, tensorForm_tmul, smul_eq_mul]
    have hsingle : ∀ u : Splits α, form t (h ℤ (β 0)) (vWord ℤ (upper u)) =
        if (∑ j, (u j : ℕ)) = β 0 then 1 else 0 := by
      intro u
      rw [← vWord_singleton (k := ℤ) (β 0), form_vWord, matForm_single_row]
    simp only [hsingle, ih, EKRest.zipWith_ofFn]
    rw [← EKRest.sum_splitsB]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs with h1
    · rw [EKRest.zipWith_ofFn, EKRest.crossCols_ofFn, one_mul]
    · ring

/-- `(h_β, h_α)` at `q = t` via the evaluator. -/
theorem form_hWord_fastQ (t : ℤ) (β α : List ℕ) :
    form t (hWord ℤ β) (hWord ℤ α) = fastQ t β α := by
  have := form_vWord_fastQ t β.get α.get
  simpa only [vWord, List.ofFn_get] using this

theorem gram_fastQ (t : ℤ) (n : ℕ) (β α : Composition n) :
    gram t n β α = fastQ t β.blocks α.blocks := by
  rw [gram, Matrix.of_apply, form_hWord_fastQ]

end OddMath.Frontier.EKFinal
