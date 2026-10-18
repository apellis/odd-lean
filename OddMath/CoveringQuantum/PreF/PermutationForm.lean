import OddMath.CoveringQuantum.PreF.Form
import Mathlib.GroupTheory.Perm.Fin

/-!
# Weighted permutations for the free half-form

Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, Claim 1 (the equal-length
algebraic calculation only). The existing `PreF.form` is expanded by successive
applications of its left skew-derivative adjunction. Permutations send source
positions to target positions: the colour condition is `a r = b (w r)` and
crossing factors use source colours at inversions of `w`. Thus the index direction
is consistent, rather than combining the printed target-to-source colour condition
with source-indexed inversions. This does not identify a decorated-matching series.

The free-form result needs no finiteness of the colour set, Cartan datum, or
bar-consistency assumption. Empty words and repeated colours are included.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.CoveringQuantum.PreF
variable {k I : Type*} [CommRing k] [DecidableEq I]

private def insertPerm {n : ℕ} (p : Fin (n + 1)) (w : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (Fin.cases p (p.succAbove ∘ w)) (by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨fun j l h ↦ ?_, rfl⟩
    induction j using Fin.cases <;> induction l using Fin.cases <;> aesop)

@[simp] private lemma insertPerm_zero {n : ℕ} (p : Fin (n + 1))
    (w : Equiv.Perm (Fin n)) : insertPerm p w 0 = p := rfl
@[simp] private lemma insertPerm_succ {n : ℕ} (p : Fin (n + 1))
    (w : Equiv.Perm (Fin n)) (r : Fin n) :
    insertPerm p w r.succ = p.succAbove (w r) := rfl

private lemma insertPerm_bijective (n : ℕ) :
    Function.Bijective (fun pw : Fin (n + 1) × Equiv.Perm (Fin n) ↦
      insertPerm pw.1 pw.2) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨fun ⟨p, w⟩ ⟨q, v⟩ h ↦ ?_, ?_⟩
  · obtain rfl : p = q := by simpa using DFunLike.congr_fun h 0
    obtain rfl : w = v := by
      ext r : 1
      simpa using DFunLike.congr_fun h r.succ
    rfl
  · rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, Nat.factorial_succ]

private lemma prefix_succ {n : ℕ} (f : Fin (n + 1) → k) (p : Fin n) :
    (∏ r : Fin (n + 1) with r < p.succ, f r) =
      f 0 * ∏ r : Fin n with r < p, f r.succ := by
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  simp

omit [DecidableEq I] in
private lemma remove_succ {n : ℕ} (b : Fin (n + 2) → I) (p : Fin (n + 1)) :
    (fun r ↦ b (p.succ.succAbove r)) =
      Fin.cons (b 0) (fun r ↦ b ((p.succAbove r).succ)) := by
  funext r
  induction r using Fin.cases <;> simp

/-- Expansion of the left skew derivative by the position removed. -/
lemma lDeriv_monomial_ofFn (χ : Bichar k I) (i : I) (n : ℕ)
    (b : Fin (n + 1) → I) :
    lDeriv χ i (monomial k (List.ofFn b)) =
      ∑ p : Fin (n + 1), if i = b p then
        (∏ r : Fin (n + 1) with r < p, χ i (b r)) •
          monomial k (List.ofFn (fun r ↦ b (p.succAbove r))) else 0 := by
  induction n with
  | zero => simp [List.ofFn_succ, monomial_cons]
  | succ n ih =>
    conv_rhs => rw [Fin.sum_univ_succ]
    rw [List.ofFn_succ, monomial_cons, lDeriv_θ_mul, ih]
    simp only [Fin.not_lt_zero, Finset.filter_false, Finset.prod_empty, one_smul,
      Fin.succAbove_zero, prefix_succ, remove_succ, List.ofFn_cons, monomial_cons]
    congr 1
    rw [Finset.mul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp [smul_smul]

/-- Product of crossing factors, indexed by inversions from source to target. -/
def inversionWeight (χ : Bichar k I) {n : ℕ} (a : Fin n → I)
    (w : Equiv.Perm (Fin n)) : k :=
  ∏ r, ∏ s with r < s ∧ w s < w r, χ (a r) (a s)

omit [DecidableEq I] in
private lemma inversionWeight_insert (χ : Bichar k I) {n : ℕ}
    (a b : Fin (n + 1) → I) (p : Fin (n + 1)) (w : Equiv.Perm (Fin n))
    (h : ∀ r, a r.succ = b (p.succAbove (w r))) :
    inversionWeight χ a (insertPerm p w) =
      (∏ r with r < p, χ (a 0) (b r)) *
        inversionWeight χ (fun r ↦ a r.succ) w := by
  unfold inversionWeight
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  have head : (∏ s : Fin n, if p.succAbove (w s) < p then χ (a 0) (a s.succ) else 1) =
      ∏ r : Fin (n + 1), if r < p then χ (a 0) (b r) else 1 := by
    simp_rw [h]
    rw [Equiv.prod_comp w (fun t ↦ if p.succAbove t < p then χ (a 0) (b (p.succAbove t)) else 1)]
    rw [Fin.prod_univ_succAbove _ p]
    simp
  simp only [Fin.prod_univ_succ, Fin.lt_irrefl, false_and, ↓reduceIte,
    one_mul, Fin.succ_pos, true_and, insertPerm_zero, insertPerm_succ,
    Fin.not_lt_zero, Fin.succ_lt_succ_iff, Fin.succAbove_lt_succAbove_iff]
  congr 1
  simpa only [Fin.prod_univ_succ] using head

/-- Removing the first source letter gives the position recurrence for the existing form. -/
lemma form_monomial_ofFn_succ (χ : Bichar k I) (nm : I → k) {n : ℕ}
    (a b : Fin (n + 1) → I) :
    form χ nm (monomial k (List.ofFn a)) (monomial k (List.ofFn b)) =
      nm (a 0) * ∑ p : Fin (n + 1), if a 0 = b p then
        (∏ r with r < p, χ (a 0) (b r)) *
          form χ nm (monomial k (List.ofFn (fun r ↦ a r.succ)))
            (monomial k (List.ofFn (fun r ↦ b (p.succAbove r)))) else 0 := by
  conv_lhs => arg 1; rw [List.ofFn_succ, monomial_cons]
  rw [form_θ_mul, lDeriv_monomial_ofFn, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

/-- The algebraic weighted-permutation expansion in [BE2], Theorem 10.3, Claim 1.
The permutation sends source positions to target positions. Repeated colours are allowed. -/
theorem form_monomial_permutations (χ : Bichar k I) (nm : I → k) (n : ℕ)
    (a b : Fin n → I) :
    form χ nm (monomial k (List.ofFn a)) (monomial k (List.ofFn b)) =
      (∏ r, nm (a r)) * ∑ w : Equiv.Perm (Fin n),
        if ∀ r, a r = b (w r) then inversionWeight χ a w else 0 := by
  classical
  induction n with
  | zero => simp [inversionWeight]
  | succ n ih =>
    rw [form_monomial_ofFn_succ, Fin.prod_univ_succ]
    simp_rw [ih]
    let e := Equiv.ofBijective _ (insertPerm_bijective n)
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    simp only [e, Equiv.ofBijective_apply]
    rw [mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : a 0 = b p
    · simp only [hp, ↓reduceIte]
      have match_iff (w : Equiv.Perm (Fin n)) :
          (∀ r, a r = b (insertPerm p w r)) ↔
            (∀ r, a r.succ = b (p.succAbove (w r))) := by
        simp [Fin.forall_fin_succ, hp]
      simp_rw [match_iff]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs with hw
      · rw [inversionWeight_insert χ a b p w hw, hp]
        ring
      · simp
    · have no_match (w : Equiv.Perm (Fin n)) : ¬ ∀ r, a r = b (insertPerm p w r) := by
        intro h
        exact hp (by simpa using h 0)
      simp [hp, no_match]
end OddMath.CoveringQuantum.PreF
