import OddMath.Frontier.NilHeckeAction
import OddMath.Frontier.LongestDivided
import OddMath.Frontier.LongestElementary

/-! EKL1111.1320v1 (2.36)–(2.37). Actual permutations and the presented ring.
Written products compose rightmost first. -/
namespace OddMath.Frontier.NilCoxeterWords
open NilHeckeAction
open scoped BigOperators

abbrev Word (n : ℕ) := List (Fin (n+1))
abbrev Perm (n : ℕ) := Equiv.Perm (Fin (n+2))

def simple {n : ℕ} (i : Fin (n+1)) : Perm n := Equiv.swap i.castSucc i.succ

def permutation {n : ℕ} : Word n → Perm n
  | [] => 1
  | i::w => simple i * permutation w

/-- The ordinary inversion number, on the actual finite permutation. -/
def length {n : ℕ} (p : Perm n) : ℕ :=
  ∑ a : Fin (n+2), ∑ b : Fin (n+2), if a < b ∧ p b < p a then 1 else 0

def Reduced {n : ℕ} (w : Word n) : Prop := w.length = length (permutation w)
instance {n : ℕ} (w : Word n) : Decidable (Reduced w) := inferInstanceAs (Decidable (_ = _))

def product {n : ℕ} : Word n → Presented n
  | [] => 1
  | i::w => crossing n i * product w

@[simp] theorem permutation_append {n : ℕ} (u v : Word n) :
    permutation (u++v) = permutation u * permutation v := by
  induction u with
  | nil => simp [permutation]
  | cons i u ih => simp [permutation, ih, mul_assoc]

@[simp] theorem product_append {n : ℕ} (u v : Word n) :
    product (u++v) = product u * product v := by
  induction u with
  | nil => simp [product]
  | cons i u ih => simp [product, ih, mul_assoc]

/-- Compatibility does not assume faithfulness. -/
theorem action_product {n : ℕ} (w : Word n) :
    action n (product w) = LongestDivided.applyWord w := by
  induction w with
  | nil => simp [product, LongestDivided.applyWord]; rfl
  | cons i w ih =>
      simp only [product, map_mul, action_crossing, ih, LongestDivided.applyWord]
      rfl

private theorem relator_zero {n : ℕ} (r : Free n) (h : Relator n r) :
    Ideal.Quotient.mk (relIdeal n) r = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change r ∈ (relTwoSided n).asIdeal
  rw [TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.subset_span h

theorem crossing_square {n : ℕ} (i : Fin (n+1)) :
    crossing n i * crossing n i = 0 := by
  simpa only [map_mul, crossing] using relator_zero _ (Relator.square i)

theorem crossing_braid {n : ℕ} (i j : Fin (n+1)) (h : j.val = i.val+1) :
    crossing n i * crossing n j * crossing n i =
      crossing n j * crossing n i * crossing n j := by
  have hz := relator_zero _ (Relator.braid i j h)
  simpa only [map_sub, map_mul, crossing, sub_eq_zero] using hz

theorem crossing_distant {n : ℕ} (i j : Fin (n+1))
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    crossing n i * crossing n j = -(crossing n j * crossing n i) := by
  have hz := relator_zero _ (Relator.distant i j h)
  simpa only [map_add, map_mul, crossing, add_eq_zero_iff_eq_neg] using hz

@[simp] theorem simple_apply_left {n : ℕ} (i : Fin (n+1)) :
    simple i i.castSucc = i.succ := Equiv.swap_apply_left _ _
@[simp] theorem simple_apply_right {n : ℕ} (i : Fin (n+1)) :
    simple i i.succ = i.castSucc := Equiv.swap_apply_right _ _
@[simp] theorem simple_square {n : ℕ} (i : Fin (n+1)) : simple i * simple i = 1 :=
  Equiv.swap_mul_self _ _

theorem simple_apply_other {n : ℕ} (i : Fin (n+1)) (x : Fin (n+2))
    (ha : x ≠ i.castSucc) (hb : x ≠ i.succ) : simple i x = x :=
  Equiv.swap_apply_of_ne_of_ne ha hb

@[simp] theorem length_one (n : ℕ) : length (1 : Perm n) = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  simp only [Equiv.Perm.one_apply]
  split_ifs with h
  · exact (lt_asymm h.1 h.2).elim
  · rfl

/-- Right descents are comparisons of adjacent values, not a chosen word predicate. -/
def Descent {n : ℕ} (p : Perm n) (i : Fin (n+1)) : Prop := p i.succ < p i.castSucc

private theorem inv_swap_term {n : ℕ} (p : Perm n) (i : Fin (n+1)) (a b : Fin (n+2)) :
    (if simple i a < simple i b ∧ p b < p a then (1 : ℤ) else 0) =
    (if a < b ∧ p b < p a then (1 : ℤ) else 0) +
    (if a = i.succ ∧ b = i.castSucc ∧ p i.castSucc < p i.succ then 1 else 0) -
    (if a = i.castSucc ∧ b = i.succ ∧ p i.succ < p i.castSucc then 1 else 0) := by
  by_cases ha : a = i.castSucc <;> by_cases hb : a = i.succ <;>
    by_cases hc : b = i.castSucc <;> by_cases hd : b = i.succ
  all_goals simp only [simple, Equiv.swap_apply_def, ha, hb, hc, hd, if_pos, if_neg]
  all_goals subst_vars
  all_goals simp only [Fin.ext_iff, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ] at *
  all_goals have hl : i.castSucc.val = i.val := rfl
  all_goals have hr : i.succ.val = i.val+1 := rfl
  all_goals simp only [ite_true, ite_false, true_and, false_and, and_false] at *
  all_goals split_ifs <;> simp only [true_and, false_and, and_false, not_true_eq_false] at * <;> omega

/-- Exact adjacent-change law for the ordinary inversion count. -/
theorem length_mul_simple {n : ℕ} (p : Perm n) (i : Fin (n+1)) :
    (length (p * simple i) : ℤ) = (length p : ℤ) +
      (if p i.castSucc < p i.succ then 1 else 0) -
      (if p i.succ < p i.castSucc then 1 else 0) := by
  classical
  simp only [length, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hs : ∀ f : Fin (n+2) → ℤ, (∑ a, f (simple i a)) = ∑ a, f a :=
    fun f => Equiv.sum_comp (simple i) f
  calc
    _ = ∑ a : Fin (n+2), ∑ b : Fin (n+2),
        if simple i a < simple i b ∧ p b < p a then (1 : ℤ) else 0 := by
      rw [← hs (fun a => ∑ b : Fin (n+2),
        if a < b ∧ (p * simple i) b < (p * simple i) a then (1 : ℤ) else 0)]
      apply Finset.sum_congr rfl
      intro a _
      rw [← hs (fun b => if simple i a < b ∧
        (p * simple i) b < (p * simple i) (simple i a) then (1 : ℤ) else 0)]
      simp only [Equiv.Perm.mul_apply, simple, Equiv.swap_apply_self]
    _ = _ := by
      simp_rw [inv_swap_term]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      congr 2 <;> simp [ite_and]

theorem values_ne {n : ℕ} (p : Perm n) (i : Fin (n+1)) : p i.castSucc ≠ p i.succ := by
  intro h
  have := congrArg Fin.val (p.injective h)
  simp only [Fin.coe_castSucc, Fin.val_succ] at this
  omega

theorem length_descend {n : ℕ} (p : Perm n) (i : Fin (n+1)) (h : Descent p i) :
    length (p * simple i) + 1 = length p := by
  have he := length_mul_simple p i
  have hn : ¬p i.castSucc < p i.succ := not_lt_of_gt h
  unfold Descent at h
  rw [if_neg hn, if_pos h] at he
  omega

theorem length_ascend {n : ℕ} (p : Perm n) (i : Fin (n+1)) (h : ¬Descent p i) :
    length (p * simple i) = length p + 1 := by
  have ht : p i.castSucc < p i.succ := lt_of_le_of_ne (le_of_not_gt h) (values_ne p i)
  have he := length_mul_simple p i
  unfold Descent at h
  rw [if_pos ht, if_neg h] at he
  omega

theorem eq_one_of_no_descent {n : ℕ} (p : Perm n) (h : ∀ i, ¬Descent p i) : p = 1 := by
  have hm : StrictMono p := Fin.strictMono_iff_lt_succ.mpr fun i =>
    lt_of_le_of_ne (le_of_not_gt (h i)) (values_ne p i)
  ext x
  exact le_antisymm (hm.le_id x) (hm.id_le x)

theorem exists_descent {n : ℕ} (p : Perm n) (h : p ≠ 1) : ∃ i, Descent p i := by
  by_contra hn
  push_neg at hn
  exact h (eq_one_of_no_descent p hn)

@[simp] theorem permutation_singleton {n : ℕ} (i : Fin (n+1)) :
    permutation [i] = simple i := by simp [permutation]
@[simp] theorem product_singleton {n : ℕ} (i : Fin (n+1)) :
    product [i] = crossing n i := by simp [product]

/-- Every permutation has a word of EXACTLY its inversion number. -/
theorem exists_reduced {n : ℕ} (p : Perm n) :
    ∃ w : Word n, permutation w = p ∧ w.length = length p := by
  induction h : length p using Nat.strong_induction_on generalizing p with
  | h k ih =>
    by_cases hp : p = 1
    · subst p
      exact ⟨[], rfl, by simpa using h⟩
    · obtain ⟨i, hi⟩ := exists_descent p hp
      have hl := length_descend p i hi
      obtain ⟨w, hw, hwl⟩ := ih (length (p * simple i)) (by omega) (p * simple i) rfl
      refine ⟨w++[i], ?_, ?_⟩
      · simp [hw, mul_assoc]
      · simp only [List.length_append, List.length_singleton, hwl]
        omega

/-- No word can be shorter than the actual inversion number. -/
theorem length_le_word {n : ℕ} (w : Word n) : length (permutation w) ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [permutation, length_one]
  | append_singleton w i ih =>
      simp only [permutation_append, permutation_singleton, List.length_append, List.length_singleton]
      by_cases h : Descent (permutation w) i
      · have := length_descend (permutation w) i h; omega
      · rw [length_ascend _ _ h]; omega

theorem reduced_prefix {n : ℕ} (w : Word n) (i : Fin (n+1)) (h : Reduced (w++[i])) :
    Reduced w ∧ ¬Descent (permutation w) i := by
  have hb := length_le_word w
  change (w++[i]).length = length (permutation (w++[i])) at h
  simp only [permutation_append, permutation_singleton, List.length_append, List.length_singleton] at h
  by_cases hd : Descent (permutation w) i
  · have := length_descend (permutation w) i hd; omega
  · have := length_ascend (permutation w) i hd
    exact ⟨by unfold Reduced; omega, hd⟩

theorem reduced_append {n : ℕ} (w : Word n) (i : Fin (n+1))
    (hw : Reduced w) (hi : ¬Descent (permutation w) i) : Reduced (w++[i]) := by
  unfold Reduced at *
  simp only [List.length_append, List.length_singleton, permutation_append, permutation_singleton]
  rw [length_ascend _ _ hi, hw]

/-- A SINGLE global sign, never a coefficient- or input-dependent sign. -/
def Signed {R : Type*} [Neg R] (a b : R) : Prop := a = b ∨ a = -b

namespace Signed
variable {R : Type*} [Ring R] {a b c d : R}
theorem refl (a : R) : Signed a a := Or.inl rfl
theorem symm (h : Signed a b) : Signed b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])
theorem trans (h : Signed a b) (k : Signed b c) : Signed a c := by
  rcases h with h | h <;> rcases k with k | k
  · exact Or.inl (h.trans k)
  · exact Or.inr (h.trans k)
  · exact Or.inr (by rw [h, k])
  · exact Or.inl (by rw [h, k, neg_neg])
theorem mul (h : Signed a b) (k : Signed c d) : Signed (a*c) (b*d) := by
  rcases h with h | h <;> rcases k with k | k
  · exact Or.inl (by rw [h,k])
  · exact Or.inr (by rw [h,k,mul_neg])
  · exact Or.inr (by rw [h,k,neg_mul])
  · exact Or.inl (by rw [h,k,neg_mul_neg])
theorem zero (h : Signed a 0) : a = 0 := by rcases h with h|h <;> simpa using h
end Signed

theorem simple_distant {n : ℕ} (i j : Fin (n+1))
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) : simple i * simple j = simple j * simple i := by
  have h₁ : j.castSucc ≠ i.castSucc := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc] at hv; omega
  have h₂ : j.castSucc ≠ i.succ := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at hv; omega
  have h₃ : j.succ ≠ i.castSucc := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at hv; omega
  have h₄ : j.succ ≠ i.succ := by intro e; have hv := congrArg Fin.val e; simp only [Fin.val_succ] at hv; omega
  change simple i * Equiv.swap j.castSucc j.succ = Equiv.swap j.castSucc j.succ * simple i
  rw [Equiv.mul_swap_eq_swap_mul, simple_apply_other i _ h₁ h₂, simple_apply_other i _ h₃ h₄]

theorem simple_braid {n : ℕ} (i j : Fin (n+1)) (h : j.val = i.val+1) :
    simple i * simple j * simple i = simple j * simple i * simple j := by
  have hij : i.succ = j.castSucc := Fin.ext (by simpa using h.symm)
  have h₁ : i.castSucc ≠ j.castSucc := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc] at hv; omega
  have h₂ : i.castSucc ≠ j.succ := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at hv; omega
  have h₃ : j.castSucc ≠ j.succ := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at hv; omega
  ext a
  simp only [Equiv.Perm.mul_apply, simple, hij]
  by_cases ha : a = i.castSucc
  · subst a; simp [Equiv.swap_apply_def, h₁, h₂, h₃, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃]
  · by_cases hb : a = j.castSucc
    · subst a; simp [Equiv.swap_apply_def, h₁, h₂, h₃, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃]
    · by_cases hc : a = j.succ
      · subst a; simp [Equiv.swap_apply_def, h₁, h₂, h₃, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃]
      · simp [Equiv.swap_apply_def, ha,hb,hc]

theorem descent_distant {n : ℕ} (p : Perm n) (i j : Fin (n+1))
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) : Descent (p * simple i) j ↔ Descent p j := by
  have h₁ : j.castSucc ≠ i.castSucc := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc] at hv; omega
  have h₂ : j.castSucc ≠ i.succ := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at hv; omega
  have h₃ : j.succ ≠ i.castSucc := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at hv; omega
  have h₄ : j.succ ≠ i.succ := by intro e; have hv := congrArg Fin.val e; simp only [Fin.val_succ] at hv; omega
  simp [Descent, Equiv.Perm.mul_apply, simple_apply_other i j.castSucc h₁ h₂,
    simple_apply_other i j.succ h₃ h₄]

theorem descent_adjacent {n : ℕ} (p : Perm n) (i j : Fin (n+1))
    (h : j.val = i.val+1) (hi : Descent p i) (hj : Descent p j) :
    Descent (p * simple i) j ∧ Descent (p * simple i * simple j) i := by
  have hij : i.succ = j.castSucc := Fin.ext (by simpa using h.symm)
  have h₁ : j.succ ≠ i.castSucc := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at hv; omega
  have h₂ : j.succ ≠ i.succ := by intro e; have hv := congrArg Fin.val e; simp only [Fin.val_succ] at hv; omega
  have h₃ : i.castSucc ≠ j.castSucc := by intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc] at hv; omega
  have h₄ : i.castSucc ≠ j.succ := h₁.symm
  have hji : j.castSucc = i.succ := hij.symm
  constructor
  · change p (simple i j.succ) < p (simple i j.castSucc)
    rw [simple_apply_other i j.succ h₁ h₂, hji, simple_apply_right]
    exact lt_trans (by simpa only [Descent, hji] using hj) hi
  · change p (simple i (simple j i.succ)) < p (simple i (simple j i.castSucc))
    rw [simple_apply_other j i.castSucc h₃ h₄, simple_apply_left,
      hij, simple_apply_left, simple_apply_other i j.succ h₁ h₂]
    exact hj

@[simp] theorem mul_simple_cancel {n : ℕ} (p : Perm n) (i : Fin (n+1)) :
    p * simple i * simple i = p := by rw [mul_assoc, simple_square, mul_one]

private theorem descent_join_distant {n : ℕ} (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j)
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧ Signed (product a * crossing n i) (product b * crossing n j) := by
  obtain ⟨u, hu, hul⟩ := exists_reduced (p * simple i * simple j)
  have hpi : permutation (u++[j]) = p * simple i := by simp [hu, mul_assoc]
  have hpj : permutation (u++[i]) = p * simple j := by
    simp only [permutation_append, permutation_singleton, hu]
    calc
      p * simple i * simple j * simple i = p * (simple i * simple j) * simple i := by simp [mul_assoc]
      _ = p * (simple j * simple i) * simple i := by rw [simple_distant i j h]
      _ = p * simple j := by simp [mul_assoc]
  have hli := length_descend p i hi
  have hlj := length_descend p j hj
  have hlq := length_descend (p * simple i) j ((descent_distant p i j h).mpr hj)
  refine ⟨u++[j], u++[i], hpi, hpj, ?_, ?_, ?_⟩
  · unfold Reduced; rw [hpi]; simp only [List.length_append, List.length_singleton]; omega
  · unfold Reduced; rw [hpj]; simp only [List.length_append, List.length_singleton]; omega
  · apply Or.inr
    simp only [product_append, product_singleton, mul_assoc]
    rw [crossing_distant j i (by omega), mul_neg]

private theorem descent_join_adjacent {n : ℕ} (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j) (h : j.val = i.val+1) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧ Signed (product a * crossing n i) (product b * crossing n j) := by
  obtain ⟨u, hu, hul⟩ := exists_reduced (p * simple i * simple j * simple i)
  have hb : p * simple i * simple j * simple i = p * simple j * simple i * simple j := by
    simpa only [mul_assoc] using congrArg (p * ·) (simple_braid i j h)
  have hpi : permutation (u++[i,j]) = p * simple i := by
    simp [permutation_append, hu, permutation, ← mul_assoc]
  have hpj : permutation (u++[j,i]) = p * simple j := by
    rw [permutation_append, hu, hb]
    simp [permutation, ← mul_assoc]
  have hli := length_descend p i hi
  have hlj := length_descend p j hj
  have hd := descent_adjacent p i j h hi hj
  have hlq := length_descend (p * simple i) j hd.1
  have hlr := length_descend (p * simple i * simple j) i hd.2
  refine ⟨u++[i,j], u++[j,i], hpi, hpj, ?_, ?_, ?_⟩
  · unfold Reduced; rw [hpi]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · unfold Reduced; rw [hpj]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · apply Or.inl
    simpa only [product_append, product, mul_one, mul_assoc] using
      congrArg (product u * ·) (crossing_braid i j h)

/-- Local descent joins use only the length-two commuting and length-three braid
polygons of ACTUAL adjacent permutations, with their actual quotient signs. -/
theorem descent_join {n : ℕ} (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧ Signed (product a * crossing n i) (product b * crossing n j) := by
  by_cases he : i = j
  · subst j
    obtain ⟨u, hu, hl⟩ := exists_reduced (p * simple i)
    exact ⟨u,u,hu,hu,by simpa [Reduced,hu] using hl,by simpa [Reduced,hu] using hl,Signed.refl _⟩
  · by_cases h₁ : j.val = i.val+1
    · exact descent_join_adjacent p i j hi hj h₁
    · by_cases h₂ : i.val = j.val+1
      · obtain ⟨a,b,ha,hb,hra,hrb,hs⟩ := descent_join_adjacent p j i hj hi h₂
        exact ⟨b,a,hb,ha,hrb,hra,hs.symm⟩
      · apply descent_join_distant p i j hi hj
        have : i.val ≠ j.val := fun h => he (Fin.ext h)
        omega

theorem descent_after_ascend {n : ℕ} (p : Perm n) (i : Fin (n+1))
    (h : ¬Descent p i) : Descent (p * simple i) i := by
  change p (simple i i.succ) < p (simple i i.castSucc)
  rw [simple_apply_left, simple_apply_right]
  exact lt_of_le_of_ne (le_of_not_gt h) (values_ne p i)

/-- Signed Matsumoto conclusion proved here by induction on actual inversion
number and the local descent joins, not assumed from an abstract presentation. -/
theorem reduced_signed {n : ℕ} (w v : Word n) (hw : Reduced w) (hv : Reduced v)
    (hp : permutation w = permutation v) : Signed (product w) (product v) := by
  induction h : w.length using Nat.strong_induction_on generalizing w v with
  | h k ih =>
    cases w using List.reverseRecOn with
    | nil =>
        have hv0 : v.length = 0 := by simpa [Reduced, ← hp, permutation] using hv
        have : v = [] := List.length_eq_zero_iff.mp hv0
        subst v
        exact Signed.refl _
    | append_singleton w i =>
        cases v using List.reverseRecOn with
        | nil =>
            simp [Reduced, hp, permutation] at hw
        | append_singleton v j =>
            obtain ⟨hwr, hwi⟩ := reduced_prefix w i hw
            obtain ⟨hvr, hvj⟩ := reduced_prefix v j hv
            let p := permutation (w++[i])
            have hpi : p * simple i = permutation w := by simp [p, mul_assoc]
            have hpj : p * simple j = permutation v := by simp [p, hp, mul_assoc]
            have hd₁ : Descent p i := by simpa [p] using descent_after_ascend (permutation w) i hwi
            have hd₂ : Descent p j := by simpa [p, hp] using descent_after_ascend (permutation v) j hvj
            obtain ⟨a,b,ha,hb,hra,hrb,hs⟩ := descent_join p i j hd₁ hd₂
            have hwa := ih w.length (by simp only [List.length_append,List.length_singleton] at h; omega)
              w a hwr hra (by rw [ha,hpi]) rfl
            have hvb := ih v.length (by
                have he : v.length = w.length := by
                  unfold Reduced at hw hv
                  rw [← hp] at hv
                  simp only [List.length_append,List.length_singleton] at hw hv
                  omega
                simp only [List.length_append,List.length_singleton] at h
                omega) v b hvr hrb (by rw [hb,hpj]) rfl
            simp only [product_append, product_singleton]
            exact (hwa.mul (Signed.refl _)).trans (hs.trans (hvb.mul (Signed.refl _)).symm)

/-- An arbitrary NONREDUCED word is zero in the presented ring itself. -/
theorem nonreduced_zero {n : ℕ} (w : Word n) (hw : ¬Reduced w) : product w = 0 := by
  induction w using List.reverseRecOn with
  | nil => exact (hw (by simp [Reduced, permutation])).elim
  | append_singleton w i ih =>
      by_cases hr : Reduced w
      · have hd : Descent (permutation w) i := by
          by_contra hn
          exact hw (reduced_append w i hr hn)
        obtain ⟨v,hv,hvl⟩ := exists_reduced (permutation w * simple i)
        have hp : permutation (v++[i]) = permutation w := by simp [hv]
        have hl := length_descend (permutation w) i hd
        have hvr : Reduced (v++[i]) := by
          unfold Reduced; rw [hp]; simp only [List.length_append,List.length_singleton]; omega
        have hs := (reduced_signed w (v++[i]) hr hvr hp.symm).mul (Signed.refl (crossing n i))
        have hz : product (v++[i]) * crossing n i = 0 := by
          simp only [product_append, product_singleton, mul_assoc, crossing_square, mul_zero]
        rw [hz] at hs
        simpa only [product_append, product_singleton] using hs.zero
      · simp [ih hr]

/-- The noncomputable choice is made only after actual reduced existence. -/
noncomputable def chosenWord {n : ℕ} (p : Perm n) : Word n := (exists_reduced p).choose
@[simp] theorem chosenWord_permutation {n : ℕ} (p : Perm n) : permutation (chosenWord p) = p :=
  (exists_reduced p).choose_spec.1
@[simp] theorem chosenWord_length {n : ℕ} (p : Perm n) : (chosenWord p).length = length p :=
  (exists_reduced p).choose_spec.2
theorem chosenWord_reduced {n : ℕ} (p : Perm n) : Reduced (chosenWord p) := by
  simp [Reduced]

/-- Source (2.36), with choice ambiguity recorded rather than suppressed. -/
noncomputable def dividedElement {n : ℕ} (p : Perm n) : Presented n := product (chosenWord p)

theorem reduced_dividedElement {n : ℕ} (w : Word n) (hw : Reduced w) :
    Signed (product w) (dividedElement (permutation w)) :=
  reduced_signed w _ hw (chosenWord_reduced _) (chosenWord_permutation _).symm

/-- EKL (2.37), the length-additive branch IN THE PRESENTED QUOTIENT. -/
theorem dividedElement_mul_additive {n : ℕ} (p q : Perm n)
    (h : length (p*q) = length p + length q) :
    Signed (dividedElement p * dividedElement q) (dividedElement (p*q)) := by
  have hr : Reduced (chosenWord p ++ chosenWord q) := by simp [Reduced,h]
  simpa only [product_append, chosenWord_permutation, permutation_append, dividedElement] using
    reduced_dividedElement _ hr

/-- EKL (2.37), the nonadditive branch, WITHOUT any faithfulness premise. -/
theorem dividedElement_mul_nonadditive {n : ℕ} (p q : Perm n)
    (h : length (p*q) ≠ length p + length q) : dividedElement p * dividedElement q = 0 := by
  have hr : ¬Reduced (chosenWord p ++ chosenWord q) := by simpa [Reduced,eq_comm] using h
  simpa only [product_append, dividedElement] using nonreduced_zero _ hr

/-- Both source cases in a single statement. -/
theorem dividedElement_mul {n : ℕ} (p q : Perm n) :
    if length (p*q) = length p + length q
    then Signed (dividedElement p * dividedElement q) (dividedElement (p*q))
    else dividedElement p * dividedElement q = 0 := by
  split_ifs with h
  · exact dividedElement_mul_additive p q h
  · exact dividedElement_mul_nonadditive p q h

/-- Every arbitrary word has the source reduced/nonreduced alternative. -/
theorem word_normalization {n : ℕ} (w : Word n) :
    if Reduced w then Signed (product w) (dividedElement (permutation w)) else product w = 0 := by
  split_ifs with h
  · exact reduced_dividedElement w h
  · exact nonreduced_zero w h

/-- Global operator sign (before application to any polynomial). -/
theorem reduced_operator_signed {n : ℕ} (w v : Word n) (hw : Reduced w) (hv : Reduced v)
    (hp : permutation w = permutation v) :
    Signed (LongestDivided.applyWord w) (LongestDivided.applyWord v) := by
  rcases reduced_signed w v hw hv hp with h | h
  · exact Or.inl (by simpa only [action_product] using congrArg (action n) h)
  · exact Or.inr (by simpa only [action_product,map_neg] using congrArg (action n) h)

theorem nonreduced_operator_zero {n : ℕ} (w : Word n) (hw : ¬Reduced w) :
    LongestDivided.applyWord w = 0 := by
  simpa only [action_product,map_zero] using congrArg (action n) (nonreduced_zero w hw)

noncomputable def dividedElementOperator {n : ℕ} (p : Perm n) :
    Module.End ℤ (OddMath.SkewPolynomial.SkewPolynomial (n+2)) := action n (dividedElement p)

theorem dividedElementOperator_eq {n : ℕ} (p : Perm n) :
    dividedElementOperator p = LongestDivided.applyWord (chosenWord p) := action_product _

theorem dividedElementOperator_mul_additive {n : ℕ} (p q : Perm n)
    (h : length (p*q) = length p + length q) :
    Signed (dividedElementOperator p * dividedElementOperator q) (dividedElementOperator (p*q)) := by
  rcases dividedElement_mul_additive p q h with hs | hs
  · exact Or.inl (by simpa only [map_mul,dividedElementOperator] using congrArg (action n) hs)
  · exact Or.inr (by simpa only [map_mul,map_neg,dividedElementOperator] using congrArg (action n) hs)

theorem dividedElementOperator_mul_nonadditive {n : ℕ} (p q : Perm n)
    (h : length (p*q) ≠ length p + length q) : dividedElementOperator p * dividedElementOperator q = 0 := by
  simpa only [map_mul,map_zero,dividedElementOperator] using congrArg (action n) (dividedElement_mul_nonadditive p q h)

/-- Explicit integral witness: exactly +1 or -1, not a general unit. -/
theorem reduced_global_sign {n : ℕ} (w v : Word n) (hw : Reduced w) (hv : Reduced v)
    (hp : permutation w = permutation v) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ product w = ε • product v ∧
      LongestDivided.applyWord w = ε • LongestDivided.applyWord v := by
  rcases reduced_signed w v hw hv hp with h | h
  · refine ⟨1, Or.inl rfl, by simpa using h, ?_⟩
    simpa only [one_smul,action_product] using congrArg (action n) h
  · refine ⟨-1, Or.inr rfl, by simpa using h, ?_⟩
    simpa only [neg_one_smul,action_product,map_neg] using congrArg (action n) h

/-- The independent literal staircase computation proves the inherited source
word is reduced; no faithfulness or Schubert-basis argument is used. -/
theorem sourceWord_reduced (n : ℕ) : Reduced (LongestDivided.wordIn n (n+2) le_rfl) := by
  by_contra hn
  have hz := congrArg (fun L : Module.End ℤ (OddMath.SkewPolynomial.SkewPolynomial (n+2)) =>
    L (LongestDivided.staircase (n+2))) (nonreduced_operator_zero _ hn)
  change LongestDivided.D (n+2) (LongestDivided.staircase (n+2)) = 0 at hz
  rw [LongestDivided.D_staircase] at hz
  rcases neg_one_pow_eq_or ℤ ((n+2).choose 3) with h | h <;> simp [h] at hz

theorem coxeterWord_length (N : ℕ) : (LongestDivided.coxeterWord N).length = N.choose 2 := by
  induction N with
  | zero => rfl
  | succ N ih => simp [LongestDivided.coxeterWord, ih, Nat.choose_succ_succ, Nat.add_comm]

theorem sourceWord_length (n : ℕ) :
    (LongestDivided.wordIn n (n+2) le_rfl).length = (n+2).choose 2 := by
  simp [LongestDivided.wordIn, coxeterWord_length]

private theorem pair_count (N : ℕ) :
    (∑ a : Fin N, ∑ b : Fin N, if a < b then (1 : ℕ) else 0) = N.choose 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.sum_univ_succ, Fin.succ_lt_succ_iff, Fin.succ_pos, Fin.not_lt_zero,
        if_true, if_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one, zero_add, add_zero]
      rw [ih, Nat.choose_succ_succ, Nat.choose_one_right]

theorem length_le_max {n : ℕ} (p : Perm n) : length p ≤ (n+2).choose 2 := by
  rw [← pair_count]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  split_ifs <;> omega

/-- The maximal inversion count characterizes ACTUAL order reversal. -/
theorem eq_longest_of_length {n : ℕ} (p : Perm n) (h : length p = (n+2).choose 2) :
    p = LongestElementary.longest (n+2) := by
  have hb (a b : Fin (n+2)) : (if a < b ∧ p b < p a then (1 : ℕ) else 0) ≤
      (if a < b then 1 else 0) := by split_ifs <;> omega
  have he := (Finset.sum_eq_sum_iff_of_le (fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum (fun b _ => hb a b))).mp (h.trans (pair_count (n+2)).symm)
  have ha : StrictAnti p := by
    intro a b hab
    have hh := (Finset.sum_eq_sum_iff_of_le (fun b (_ : b ∈ Finset.univ) => hb a b)).mp
      (he a (Finset.mem_univ a)) b (Finset.mem_univ b)
    simpa [hab] using hh
  have hm : StrictMono (fun a : Fin (n+2) => p a.rev) := ha.comp Fin.rev_strictAnti
  apply Equiv.ext
  intro a
  have heq := le_antisymm (hm.le_id a.rev) (hm.id_le a.rev)
  simpa using heq

/-- The inherited literal word really denotes the longest permutation. -/
theorem sourceWord_permutation (n : ℕ) :
    permutation (LongestDivided.wordIn n (n+2) le_rfl) = LongestElementary.longest (n+2) := by
  apply eq_longest_of_length
  rw [← sourceWord_reduced, sourceWord_length]

/-- An arbitrary chosen longest expression is compared by a PROVED global sign;
we do not silently identify it with the paper's distinguished choice D. -/
theorem chosen_longest_source_sign (n : ℕ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      dividedElement (LongestElementary.longest (n+2)) =
        ε • product (LongestDivided.wordIn n (n+2) le_rfl) ∧
      dividedElementOperator (LongestElementary.longest (n+2)) = ε • LongestDivided.D (n+2) := by
  simpa only [dividedElement, dividedElementOperator, action_product, LongestDivided.D] using
    reduced_global_sign (chosenWord (LongestElementary.longest (n+2)))
      (LongestDivided.wordIn n (n+2) le_rfl) (chosenWord_reduced _) (sourceWord_reduced n)
      (by rw [chosenWord_permutation, sourceWord_permutation])

end OddMath.Frontier.NilCoxeterWords
