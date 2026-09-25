import Mathlib

/-! # Partitions in a box and conjugates of complements
Pure combinatorics for EKL arXiv:1111.1320v1, Lemma 4.9 (p. 36).
For `α ∈ P(a,b)` (`a` parts, each at most `b`) the complementary partition `α^c` and
`α̂ := (α^c)'` are defined in §2.3 (p. 17). Here `hat a β ∈ P(a,b)` is the conjugate of the
complement of `β ∈ P(b,a)`, written 0-based as `hat a β k = #{j | β j ≤ a - 1 - k}`.
The exponent sequences `expA α` and `expB β` of (4.32)–(4.33) are disjoint exactly when
`α = hat a β`, in which case they partition `{0, …, a + b - 1}`.
-/
namespace OddMath.Frontier.BoxComplement
open Finset

/-- The partition `β̂ ∈ P(a,b)` (conjugate of the complement of `β` in the `b × a` box). -/
def hat (a : ℕ) {b : ℕ} (β : Fin b → ℕ) : Fin a → ℕ :=
  fun k => (Finset.univ.filter (fun j : Fin b => β j ≤ a - 1 - k.val)).card

/-- Exponents of the first `a` variables in EKL (4.32)–(4.33): `a − 1 − k + α_k`. -/
def expA {a : ℕ} (α : Fin a → ℕ) : Fin a → ℕ := fun k => a - 1 - k.val + α k

/-- Exponents of the last `b` variables in EKL (4.32)–(4.33): `j + β_{b−1−j}`. -/
def expB {b : ℕ} (β : Fin b → ℕ) : Fin b → ℕ := fun j => j.val + β (Fin.rev j)

variable {a b : ℕ} {α : Fin a → ℕ} {β : Fin b → ℕ}

theorem expA_strictAnti (hα : Antitone α) : StrictAnti (expA α) := by
  intro k k' h
  have h1 := hα h.le
  have h2 : k.val < k'.val := h
  have := k'.isLt
  simp only [expA]
  omega

theorem expB_strictMono (hβ : Antitone β) : StrictMono (expB β) := by
  intro j j' h
  have h1 := hβ (Fin.rev_lt_rev.mpr h).le
  have h2 : j.val < j'.val := h
  simp only [expB]
  omega

theorem expA_lt (hαb : ∀ k, α k ≤ b) (k : Fin a) : expA α k < a + b := by
  have := hαb k
  have := k.isLt
  simp only [expA]
  omega

theorem expB_lt (hβa : ∀ j, β j ≤ a) (j : Fin b) : expB β j < a + b := by
  have := hβa (Fin.rev j)
  have := j.isLt
  simp only [expB]
  omega

theorem hat_antitone : Antitone (hat a β) := by
  intro k k' h
  refine card_le_card fun j hj => ?_
  have h' : k.val ≤ k'.val := h
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  omega

theorem hat_le (k : Fin a) : hat a β k ≤ b :=
  (card_filter_le _ _).trans (by simp)

/-- Conjugation in the box: `j < β̂_k` iff the cell `(b − 1 − j, a − 1 − k)` lies in `β`'s
complement. -/
theorem lt_hat_iff (hβ : Antitone β) (k : Fin a) (j : Fin b) :
    j.val < hat a β k ↔ β (Fin.rev j) ≤ a - 1 - k.val := by
  constructor
  · intro h
    by_contra h'
    have hsub : univ.filter (fun i : Fin b => β i ≤ a - 1 - k.val) ⊆ Ioi (Fin.rev j) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      rw [mem_Ioi]
      by_contra hle
      have := hβ (not_lt.mp hle)
      omega
    have := card_le_card hsub
    rw [Fin.card_Ioi, Fin.val_rev] at this
    unfold hat at h
    omega
  · intro h
    have hsub : Ici (Fin.rev j) ⊆ univ.filter (fun i : Fin b => β i ≤ a - 1 - k.val) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and]
      exact (hβ (mem_Ici.mp hi)).trans h
    have := card_le_card hsub
    rw [Fin.card_Ici, Fin.val_rev] at this
    have := j.isLt
    unfold hat
    omega

theorem expA_hat_ne (hβ : Antitone β) (k : Fin a) (j : Fin b) :
    expA (hat a β) k ≠ expB β j := by
  have h := lt_hat_iff hβ k j
  unfold expA expB
  by_cases hj : j.val < hat a β k
  · have := h.mp hj
    omega
  · have := mt h.mpr hj
    omega

/-- Disjoint exponent sequences fill `{0, …, a + b - 1}`. -/
theorem image_expA_eq (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β)
    (hβa : ∀ j, β j ≤ a) (hdisj : ∀ k j, expA α k ≠ expB β j) :
    univ.image (expA α) = range (a + b) \ univ.image (expB β) := by
  have hA : univ.image (expA α) ⊆ range (a + b) := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (expA_lt hαb k)
  have hB : univ.image (expB β) ⊆ range (a + b) := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (expB_lt hβa j)
  have hd : Disjoint (univ.image (expA α)) (univ.image (expB β)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨k, -, rfl⟩ := mem_image.mp hx
    obtain ⟨j, -, hj⟩ := mem_image.mp hx'
    exact hdisj k j hj.symm
  have hcard : (univ.image (expA α) ∪ univ.image (expB β)).card = a + b := by
    rw [card_union_of_disjoint hd, card_image_of_injective _ (expA_strictAnti hα).injective,
      card_image_of_injective _ (expB_strictMono hβ).injective, card_univ, card_univ,
      Fintype.card_fin, Fintype.card_fin]
  have hU : univ.image (expA α) ∪ univ.image (expB β) = range (a + b) :=
    eq_of_subset_of_card_le (union_subset hA hB) (by rw [hcard, card_range])
  rw [← hU, union_sdiff_right, sdiff_eq_self_of_disjoint hd]

/-- EKL Lemma 4.9 (combinatorial core): the exponent sequences are disjoint iff `α = β̂`. -/
theorem disjoint_iff_eq_hat {a b : ℕ} {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    (∀ k j, expA α k ≠ expB β j) ↔ α = hat a β := by
  constructor
  · intro h
    have h1 := image_expA_eq hα hαb hβ hβa h
    have h2 := image_expA_eq hat_antitone hat_le hβ hβa (expA_hat_ne hβ)
    have hr : Set.range (expA α) = Set.range (expA (hat a β)) := by
      rw [← Set.image_univ, ← Set.image_univ, ← coe_univ, ← coe_image, ← coe_image, h1, h2]
    have he := ((expA_strictAnti hα).range_inj (expA_strictAnti hat_antitone)).mp hr
    funext k
    have := congrFun he k
    simp only [expA] at this
    omega
  · rintro rfl
    exact expA_hat_ne hβ

theorem sum_hat (hβa : ∀ j, β j ≤ a) : ∑ k, hat a β k + ∑ j, β j = a * b := by
  have hcount : ∀ m n : ℕ, ∑ i ∈ range n, (if m ≤ i then 1 else 0) = n - m := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      split_ifs <;> omega
  have hcol : ∀ j : Fin b, ∑ k : Fin a, (if β j ≤ a - 1 - k.val then 1 else 0) = a - β j := by
    intro j
    have hrev : ∀ k : Fin a, a - 1 - k.val = (Fin.rev k).val := by
      intro k
      rw [Fin.val_rev]
      omega
    simp_rw [hrev]
    rw [show ∑ k : Fin a, (if β j ≤ k.rev.val then 1 else 0)
        = ∑ k : Fin a, (if β j ≤ k.val then 1 else 0) from
          Equiv.sum_comp Fin.revPerm (fun k : Fin a => if β j ≤ k.val then 1 else 0),
      Fin.sum_univ_eq_sum_range (fun i => if β j ≤ i then 1 else 0) a, hcount]
  simp only [hat, card_filter]
  rw [sum_comm, ← sum_add_distrib]
  simp_rw [hcol]
  rw [sum_congr rfl fun j _ => Nat.sub_add_cancel (hβa j), sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

theorem sum_val_fin (n : ℕ) : ∑ i : Fin n, i.val = n.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, sum_range_id, Nat.choose_two_right]

theorem choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  have h : ∀ n, n.choose 2 = ∑ i ∈ range n, i := fun n => by
    rw [sum_range_id, Nat.choose_two_right]
  rw [h, h, h, sum_range_add, sum_add_distrib, sum_const, card_range, smul_eq_mul]
  ring

/-- Degree identity for the monomials of EKL (4.32)–(4.33). -/
theorem sum_expA_add_sum_expB :
    ∑ k, expA α k + ∑ j, expB β j + a * b = (a + b).choose 2 + ∑ k, α k + ∑ j, β j := by
  have hA : ∑ k, expA α k = a.choose 2 + ∑ k, α k := by
    have hrev : ∀ k : Fin a, a - 1 - k.val = (Fin.rev k).val := by
      intro k
      rw [Fin.val_rev]
      omega
    simp only [expA, hrev]
    rw [sum_add_distrib, show ∑ k : Fin a, k.rev.val = ∑ k : Fin a, k.val from
      Equiv.sum_comp Fin.revPerm (fun k : Fin a => k.val), sum_val_fin]
  have hB : ∑ j, expB β j = b.choose 2 + ∑ j, β j := by
    simp only [expB]
    rw [sum_add_distrib, sum_val_fin,
      show ∑ j : Fin b, β j.rev = ∑ j, β j from Equiv.sum_comp Fin.revPerm β]
  rw [hA, hB, choose_two_add]
  ring

end OddMath.Frontier.BoxComplement
