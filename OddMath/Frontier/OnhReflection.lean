import OddMath.Frontier.NilHeckeRightBasis
import OddMath.Frontier.MonomialReversal
import OddMath.Frontier.LongestKernel
import OddMath.Frontier.ZeroHecke

/-! # Reflections of the odd nilHecke ring
EKL arXiv:1111.1320v1 §3.3, (3.46)–(3.54), p. 30. Rank is `a = n+2`; indices are
0-based and products act rightmost first. `sigma` reflects diagrams in the vertical
axis (`x_j ↦ x_{rev j}`, `∂_i ↦ ∂_{rev i}`); `ψ` is `NilHeckeRightBasis.reverseHom`.

Printed (3.51) is false: `ψ(D_a) = (-1)^{C(a,4)} D_a`, not `(-1)^{C(a-1,4)} D_a`;
the first failure is `a = 4` (`eq_3_51_false`). The corrected form is `eq_3_51`.
All other printed signs on p. 30 are proved as stated.
-/
namespace OddMath.Frontier.OnhReflection
open NilHeckeAction NilCoxeterWords NilHeckeRightBasis
open ZeroHecke (DElem staircaseElem)
open OddMath.SkewPolynomial (SkewPolynomial monomial generator)
noncomputable section
variable {n : ℕ}

/-! ### The vertical reflection -/

def sigmaFree (n : ℕ) : Free n →ₐ[ℤ] Presented n :=
  FreeAlgebra.lift ℤ (Sum.elim (fun j => dot n j.rev) (fun i => crossing n i.rev))

@[simp] theorem sigmaFree_dot (j : Fin (n+2)) : sigmaFree n (dotFree n j) = dot n j.rev := by
  simp [sigmaFree, dotFree]
@[simp] theorem sigmaFree_crossing (i : Fin (n+1)) :
    sigmaFree n (crossingFree n i) = crossing n i.rev := by
  simp [sigmaFree, crossingFree]

/-- Every relator is preserved with no sign; the two mixed relations are interchanged. -/
theorem sigmaFree_relator (r : Free n) (h : Relator n r) : sigmaFree n r = 0 := by
  cases h with
  | square i => simpa using crossing_square i.rev
  | braid i j h =>
      have h' : i.rev.val = j.rev.val + 1 := by
        have := j.isLt; simp only [Fin.val_rev]; omega
      simpa using sub_eq_zero.mpr (crossing_braid j.rev i.rev h').symm
  | dots i j h =>
      simpa using NilHeckeBasis.dots_anticommute i.rev j.rev (Fin.rev_injective.ne h)
  | distant i j h =>
      have h' : i.rev.val+1 < j.rev.val ∨ j.rev.val+1 < i.rev.val := by
        have := i.isLt; have := j.isLt; simp only [Fin.val_rev]; omega
      simpa using add_eq_zero_iff_eq_neg.mpr (crossing_distant i.rev j.rev h')
  | mixedRight i =>
      simp [Fin.rev_castSucc, Fin.rev_succ, NilHeckeBasis.crossing_dot_left]
  | mixedLeft i =>
      simp [Fin.rev_castSucc, Fin.rev_succ, NilHeckeBasis.crossing_dot_right]
  | spectator i j hl hr =>
      have hl' : j.rev ≠ i.rev.castSucc := by
        rw [← Fin.rev_succ]; exact fun h => hr (Fin.rev_injective h)
      have hr' : j.rev ≠ i.rev.succ := by
        rw [← Fin.rev_castSucc]; exact fun h => hl (Fin.rev_injective h)
      simp [NilHeckeBasis.crossing_dot_other i.rev j.rev hl' hr']

theorem sigmaFree_ideal (r : Free n) (h : r ∈ relIdeal n) : sigmaFree n r = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at h
  induction h using TwoSidedIdeal.span_induction with
  | mem r hr => exact sigmaFree_relator r hr
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | neg a _ ha => rw [map_neg, ha, neg_zero]
  | left_absorb a b _ hb => rw [map_mul, hb, mul_zero]
  | right_absorb a b _ hb => rw [map_mul, hb, zero_mul]

def sigmaHom (n : ℕ) : Presented n →+* Presented n :=
  Ideal.Quotient.lift _ (sigmaFree n).toRingHom sigmaFree_ideal

@[simp] theorem sigmaHom_dot (j : Fin (n+2)) : sigmaHom n (dot n j) = dot n j.rev := by
  change sigmaFree n (dotFree n j) = _
  simp
@[simp] theorem sigmaHom_crossing (i : Fin (n+1)) :
    sigmaHom n (crossing n i) = crossing n i.rev := by
  change sigmaFree n (crossingFree n i) = _
  simp

theorem sigmaHom_involutive (n : ℕ) : Function.Involutive (sigmaHom n) := by
  intro x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  induction a using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 g =>
      cases g with
      | inl j => change sigmaHom n (sigmaHom n (dot n j)) = dot n j; simp
      | inr i => change sigmaHom n (sigmaHom n (crossing n i)) = crossing n i; simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

/-- The vertical reflection `σ` of §3.3, an involutive ring automorphism. -/
def sigma (n : ℕ) : Presented n ≃+* Presented n :=
  { sigmaHom n with
    invFun := sigmaHom n
    left_inv := sigmaHom_involutive n
    right_inv := sigmaHom_involutive n }

theorem sigma_apply (x : Presented n) : sigma n x = sigmaHom n x := rfl
@[simp] theorem sigma_dot (j : Fin (n+2)) : sigma n (dot n j) = dot n (Fin.rev j) :=
  sigmaHom_dot j
@[simp] theorem sigma_crossing (i : Fin (n+1)) :
    sigma n (crossing n i) = crossing n (Fin.rev i) := sigmaHom_crossing i
@[simp] theorem sigma_sigma (x : Presented n) : sigma n (sigma n x) = x :=
  sigmaHom_involutive n x
theorem sigma_symm (n : ℕ) : (sigma n).symm = sigma n := rfl

/-- `σ` and `ψ` commute. -/
theorem reverse_sigma (x : Presented n) :
    MulOpposite.unop (reverseHom n (sigma n x)) = sigma n (MulOpposite.unop (reverseHom n x)) := by
  change reverseLinear n (sigma n x) = sigma n (reverseLinear n x)
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  induction a using FreeAlgebra.induction with
  | grade0 r => simp [reverseLinear]
  | grade1 g =>
      cases g with
      | inl j => change reverseLinear n (sigma n (dot n j)) = sigma n (reverseLinear n (dot n j)); simp
      | inr i =>
          change reverseLinear n (sigma n (crossing n i)) =
            sigma n (reverseLinear n (crossing n i))
          simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb =>
      rw [map_mul, (sigma n).map_mul, reverse_mul, reverse_mul, (sigma n).map_mul, ha, hb]

theorem sigma_product (w : Word n) : sigma n (product w) = product (w.map Fin.rev) := by
  induction w with
  | nil => simp [product]
  | cons i w ih => simp [product, ih]

/-! ### The elements `D_a` and `x^{δ_a}` -/

/-! `D_a` and `x^{δ_a}` are `ZeroHecke.DElem` and `ZeroHecke.staircaseElem`. -/

theorem action_DElem (n : ℕ) : action n (DElem n) = LongestDivided.D (n+2) := by
  rw [DElem, action_product]
  rfl

theorem staircase_eq (n : ℕ) :
    LongestDivided.staircase (n+2) = monomial (fun i : Fin (n+2) => n+1-i.val) 1 := by
  unfold LongestDivided.staircase
  rfl

theorem action_staircaseElem (f : SkewPolynomial (n+2)) :
    action n (staircaseElem n) f = LongestDivided.staircase (n+2) * f := by
  rw [staircaseElem, NilHeckeBasis.action_dotMonomial, staircase_eq]

theorem DElem_ne_zero (n : ℕ) : DElem n ≠ 0 := by
  intro h
  have hz := congrArg (fun x => action n x (LongestDivided.staircase (n+2))) h
  simp only [action_DElem, LongestDivided.D_staircase, map_zero, LinearMap.zero_apply] at hz
  rcases neg_one_pow_eq_or ℤ ((n+2).choose 3) with h | h <;> simp [h] at hz

theorem smul_DElem_inj {a b : ℤ} (h : a • DElem n = b • DElem n) : a = b := by
  haveI := (NilHeckeBasis.basis n).noZeroSMulDivisors
  have h2 : (a - b) • DElem n = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · omega
  · exact absurd h3 (DElem_ne_zero n)

/-- `D_a · x^A · D_a = D_a(x^A) · D_a` whenever `D_a(x^A)` is a constant. -/
theorem DElem_mul_dotMonomial_mul (A : Fin (n+2) → ℕ) (c : ℤ)
    (h : LongestDivided.D (n+2) (monomial A 1) = c • 1) :
    DElem n * NilHeckeBasis.dotMonomial A * DElem n = c • DElem n := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro f
  rw [action_mul_apply, action_mul_apply, NilHeckeBasis.action_dotMonomial, action_DElem,
    map_zsmul, LinearMap.smul_apply, action_DElem,
    LongestDivided.D_right_kernel n _ _ (LongestKernel.D_mem_kernel n f), h, smul_mul_assoc,
    one_mul]

theorem DElem_staircase_DElem (n : ℕ) :
    DElem n * staircaseElem n * DElem n = (-1 : ℤ)^((n+2).choose 3) • DElem n := by
  apply DElem_mul_dotMonomial_mul
  rw [← staircase_eq, LongestDivided.D_staircase]

theorem DElem_increasing_DElem (n : ℕ) :
    DElem n * NilHeckeBasis.dotMonomial (fun i => i.val) * DElem n =
      (-1 : ℤ)^((n+2).choose 3 + (n+2).choose 4) • DElem n :=
  DElem_mul_dotMonomial_mul _ _ (MonomialReversal.D_increasing_staircase (n+2))

/-! ### Reordering products of dot powers -/

theorem smul_smul_neg_one_pow {M : Type*} [AddCommGroup M] (k : ℕ) (x : M) :
    (-1 : ℤ)^k • (-1 : ℤ)^k • x = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- Powers of anticommuting elements commute up to `(-1)^{pq}`. -/
theorem pow_mul_pow_anti {R : Type*} [Ring R] {a b : R} (h : a*b = -(b*a)) (p q : ℕ) :
    a^p * b^q = (-1 : ℤ)^(p*q) • (b^q * a^p) := by
  have h1 : ∀ q : ℕ, a * b^q = (-1 : ℤ)^q • (b^q * a) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h, mul_neg, ← mul_assoc,
          ← pow_succ, pow_succ (-1 : ℤ), mul_neg_one, neg_smul, smul_neg]
  induction p with
  | zero => simp
  | succ p ih =>
      rw [pow_succ, mul_assoc, h1, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc, smul_smul,
        mul_assoc, ← pow_succ, ← pow_add, add_mul, one_mul, add_comm]

/-- Sum over ordered pairs `i < j` of `k_i k_j`, along a list. -/
def pairs : List ℕ → ℕ
  | [] => 0
  | k :: l => k * l.sum + pairs l

theorem dot_pow_mul_prod (j : Fin (n+2)) (k : ℕ) (e : Fin (n+2) → ℕ)
    (l : List (Fin (n+2))) (hj : j ∉ l) :
    dot n j ^ k * (l.map fun i => dot n i ^ e i).prod =
      (-1 : ℤ)^(k * (l.map e).sum) • ((l.map fun i => dot n i ^ e i).prod * dot n j ^ k) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
      have hl : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
      have ha : dot n j * dot n i = -(dot n i * dot n j) :=
        eq_neg_of_add_eq_zero_left (NilHeckeBasis.dots_anticommute j i hji)
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [← mul_assoc, pow_mul_pow_anti ha, smul_mul_assoc, mul_assoc, ih hl, mul_smul_comm,
        smul_smul, ← pow_add, ← mul_add, mul_assoc]

theorem reverse_dot_prod (e : Fin (n+2) → ℕ) (l : List (Fin (n+2))) (hl : l.Nodup) :
    (l.reverse.map fun i => dot n i ^ e i).prod =
      (-1 : ℤ)^(pairs (l.map e)) • (l.map fun i => dot n i ^ e i).prod := by
  induction l with
  | nil => simp [pairs]
  | cons j l ih =>
      obtain ⟨hj, hl⟩ := List.nodup_cons.mp hl
      have hm := dot_pow_mul_prod j (e j) e l hj
      have hm' : (l.map fun i => dot n i ^ e i).prod * dot n j ^ e j =
          (-1 : ℤ)^(e j * (l.map e).sum) •
            (dot n j ^ e j * (l.map fun i => dot n i ^ e i).prod) := by
        rw [hm, smul_smul_neg_one_pow]
      simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, pairs]
      rw [ih hl, smul_mul_assoc, hm', smul_smul, ← pow_add, add_comm]

theorem pairs_staircase_even (N : ℕ) :
    Even (pairs ((List.finRange N).map fun i => N-1-i.val) + N.choose 4) := by
  induction N with
  | zero => simp [pairs]
  | succ N ih =>
      obtain ⟨k, hk⟩ := ih
      have hmap : ((List.finRange N).map Fin.succ).map (fun i : Fin (N+1) => N+1-1-i.val) =
          (List.finRange N).map fun i => N-1-i.val := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply, Fin.val_succ]
        omega
      have hsum : ((List.finRange N).map fun i => N-1-i.val).sum = N.choose 2 := by
        rw [← Fin.sum_univ_def, MonomialReversal.sum_rev_val]
      rw [List.finRange_succ, List.map_cons, hmap, pairs, hsum]
      have hc := Nat.choose_succ_succ' N 3
      have hm := MonomialReversal.mul_choose_two N
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel] at *
      refine ⟨k + N.choose 3 + (N+1).choose 3, ?_⟩
      rw [hc]
      linarith

theorem pairs_staircase_sign (n : ℕ) :
    (-1 : ℤ)^(pairs ((List.finRange (n+2)).map fun i => n+1-i.val)) = (-1 : ℤ)^((n+2).choose 4) := by
  apply MonomialReversal.neg_one_pow_of_even_add
  simpa using pairs_staircase_even (n+2)

/-! ### (3.46)–(3.50) -/

theorem unop_reverse_dot_pow (j : Fin (n+2)) (k : ℕ) :
    MulOpposite.unop (reverseHom n (dot n j ^ k)) = dot n j ^ k := by
  rw [map_pow, MulOpposite.unop_pow]
  exact congrArg (· ^ k) (reverse_dot j)

/-- (3.46). -/
theorem eq_3_46 (n : ℕ) :
    staircaseElem n = ((List.finRange (n+2)).map fun i => dot n i ^ (n+1-i.val)).prod := rfl

/-- (3.47): `σ(x^{δ_a}) = x_a^{a-1} x_{a-1}^{a-2} ⋯ x_1^0`. -/
theorem eq_3_47 (n : ℕ) :
    sigma n (staircaseElem n) =
      ((List.finRange (n+2)).map fun i => dot n (Fin.rev i) ^ (n+1-i.val)).prod := by
  rw [eq_3_46, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp

/-- (3.48): `ψ(x^{δ_a}) = x_a^0 x_{a-1}^1 ⋯ x_1^{a-1}`. -/
theorem eq_3_48 (n : ℕ) :
    MulOpposite.unop (reverseHom n (staircaseElem n)) =
      ((List.finRange (n+2)).reverse.map fun i => dot n i ^ (n+1-i.val)).prod := by
  rw [eq_3_46, unop_map_list_prod, List.map_map, List.map_reverse]
  congr 2
  apply List.map_congr_left
  intro i _
  exact unop_reverse_dot_pow i _

/-- (3.49): `ψσ(x^{δ_a}) = x_1^0 x_2^1 ⋯ x_a^{a-1}`. -/
theorem eq_3_49 (n : ℕ) :
    MulOpposite.unop (reverseHom n (sigma n (staircaseElem n))) =
      ((List.finRange (n+2)).map fun i => dot n i ^ i.val).prod := by
  rw [eq_3_47, unop_map_list_prod, List.map_map, ← List.map_reverse,
    List.finRange_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, unop_reverse_dot_pow, Fin.rev_rev, Fin.val_rev]
  congr 1
  omega

theorem eq_3_49_dotMonomial (n : ℕ) :
    MulOpposite.unop (reverseHom n (sigma n (staircaseElem n))) =
      NilHeckeBasis.dotMonomial (fun i => i.val) := eq_3_49 n

theorem reverse_staircaseElem (n : ℕ) :
    MulOpposite.unop (reverseHom n (staircaseElem n)) =
      (-1 : ℤ)^((n+2).choose 4) • staircaseElem n := by
  rw [eq_3_48, reverse_dot_prod _ _ (List.nodup_finRange _), pairs_staircase_sign]
  rfl

/-- (3.50), both equations. -/
theorem eq_3_50 (n : ℕ) :
    staircaseElem n =
        (-1 : ℤ)^((n+2).choose 4) • MulOpposite.unop (reverseHom n (staircaseElem n)) ∧
      sigma n (staircaseElem n) = (-1 : ℤ)^((n+2).choose 4) •
        sigma n (MulOpposite.unop (reverseHom n (staircaseElem n))) := by
  have h : staircaseElem n =
      (-1 : ℤ)^((n+2).choose 4) • MulOpposite.unop (reverseHom n (staircaseElem n)) := by
    rw [reverse_staircaseElem, smul_smul_neg_one_pow]
  refine ⟨h, ?_⟩
  rw [← map_zsmul, ← h]

theorem sigma_staircaseElem (n : ℕ) :
    sigma n (staircaseElem n) =
      (-1 : ℤ)^((n+2).choose 4) • NilHeckeBasis.dotMonomial (fun i => i.val) := by
  rw [(eq_3_50 n).2, ← reverse_sigma, eq_3_49_dotMonomial]

/-! ### The words of `σ(D_a)`, `ψ(D_a)`, `ψσ(D_a)` -/

/-- `σ(D_a) = ∂_{a-1}(∂_{a-2}∂_{a-1})⋯(∂_1⋯∂_{a-1})`: every letter `j ↦ a-2-j`. -/
theorem sigma_DElem_word (n : ℕ) :
    sigma n (DElem n) = product ((LongestDivided.wordIn n (n+2) le_rfl).map Fin.rev) :=
  sigma_product _

theorem sigma_word_values (n : ℕ) :
    ((LongestDivided.wordIn n (n+2) le_rfl).map Fin.rev).map Fin.val =
      (LongestDivided.coxeterWord (n+2)).map (fun j => n - j) := by
  rw [← LongestDivided.wordIn_values n (n+2) le_rfl, List.map_map, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Fin.val_rev]
  omega

/-- `ψ(D_a) = (∂_1⋯∂_{a-1})(∂_1⋯∂_{a-2})⋯(∂_1∂_2)∂_1`, the reversed word. -/
theorem reverse_DElem_word (n : ℕ) :
    MulOpposite.unop (reverseHom n (DElem n)) =
      product (LongestDivided.wordIn n (n+2) le_rfl).reverse :=
  reverse_product _

/-- `ψσ(D_a) = (∂_{a-1}⋯∂_1)(∂_{a-1}⋯∂_2)⋯(∂_{a-1}∂_{a-2})∂_{a-1}`. -/
theorem reverse_sigma_DElem_word (n : ℕ) :
    MulOpposite.unop (reverseHom n (sigma n (DElem n))) =
      product ((LongestDivided.wordIn n (n+2) le_rfl).map Fin.rev).reverse := by
  rw [sigma_DElem_word]
  exact reverse_product _

/-! ### (3.51) -/

/-- A nonzero word of length `C(a,2)` agrees with `D_a` up to sign. -/
theorem signed_DElem (w : Word n) (hw : product w ≠ 0)
    (hl : w.length = (n+2).choose 2) : Signed (product w) (DElem n) := by
  have hr : Reduced w := by
    by_contra h
    exact hw (nonreduced_zero w h)
  have hp : permutation w = LongestElementary.longest (n+2) :=
    eq_longest_of_length _ (hr.symm.trans hl)
  exact reduced_signed w _ hr (sourceWord_reduced n) (by rw [hp, sourceWord_permutation])

theorem signed_unit {x : Presented n} (h : Signed x (DElem n)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ x = ε • DElem n := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩

theorem sigma_DElem (n : ℕ) : sigma n (DElem n) = DElem n := by
  have hs : Signed (sigma n (DElem n)) (DElem n) := by
    rw [sigma_DElem_word]
    apply signed_DElem
    · rw [← sigma_DElem_word]
      exact (map_ne_zero_iff _ (sigma n).injective).mpr (DElem_ne_zero n)
    · rw [List.length_map, sourceWord_length]
  obtain ⟨η, hη, he⟩ := signed_unit hs
  have key := congrArg (sigma n) (DElem_staircase_DElem n)
  rw [map_mul, map_mul, map_zsmul, he, sigma_staircaseElem, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, mul_smul_comm, smul_mul_assoc, DElem_increasing_DElem, smul_smul,
    smul_smul, smul_smul, smul_smul] at key
  have hc := smul_DElem_inj key
  rw [he]
  rcases hη with rfl | rfl
  · rw [one_smul]
  · exfalso
    rcases neg_one_pow_eq_or ℤ ((n+2).choose 3) with h3 | h3 <;>
      rcases neg_one_pow_eq_or ℤ ((n+2).choose 4) with h4 | h4 <;>
      simp [pow_add, h3, h4] at hc

theorem reverse_DElem (n : ℕ) :
    MulOpposite.unop (reverseHom n (DElem n)) = (-1 : ℤ)^((n+2).choose 4) • DElem n := by
  have hs : Signed (MulOpposite.unop (reverseHom n (DElem n))) (DElem n) := by
    rw [reverse_DElem_word]
    apply signed_DElem
    · rw [← reverse_DElem_word]
      intro h
      apply DElem_ne_zero n
      have h2 := congrArg (reverseLinear n) h
      rwa [map_zero, show MulOpposite.unop (reverseHom n (DElem n)) = reverseLinear n (DElem n)
        from rfl, reverse_involutive n] at h2
    · rw [List.length_reverse, sourceWord_length]
  obtain ⟨ε, hε, he⟩ := signed_unit hs
  have key := congrArg (fun x => reverseLinear n x) (DElem_staircase_DElem n)
  simp only [reverse_mul, map_zsmul] at key
  change MulOpposite.unop (reverseHom n (DElem n)) *
      (MulOpposite.unop (reverseHom n (staircaseElem n)) *
        MulOpposite.unop (reverseHom n (DElem n))) =
      (-1 : ℤ)^((n+2).choose 3) • MulOpposite.unop (reverseHom n (DElem n)) at key
  rw [he, reverse_staircaseElem, ← mul_assoc, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    mul_smul_comm, smul_mul_assoc, DElem_staircase_DElem, smul_smul, smul_smul, smul_smul,
    smul_smul] at key
  have hc := smul_DElem_inj key
  rw [he]
  congr 1
  rcases hε with rfl | rfl <;>
    rcases neg_one_pow_eq_or ℤ ((n+2).choose 3) with h3 | h3 <;>
    rcases neg_one_pow_eq_or ℤ ((n+2).choose 4) with h4 | h4 <;>
    simp [h3, h4] at hc ⊢

theorem reverse_sigma_DElem (n : ℕ) :
    MulOpposite.unop (reverseHom n (sigma n (DElem n))) =
      (-1 : ℤ)^((n+2).choose 4) • DElem n := by
  rw [sigma_DElem, reverse_DElem]

/-- (3.51), corrected: `D_a = σ(D_a) = (-1)^{C(a,4)} ψ(D_a) = (-1)^{C(a,4)} ψσ(D_a)`. -/
theorem eq_3_51 (n : ℕ) :
    DElem n = sigma n (DElem n) ∧
      DElem n = (-1 : ℤ)^((n+2).choose 4) • MulOpposite.unop (reverseHom n (DElem n)) ∧
      DElem n = (-1 : ℤ)^((n+2).choose 4) •
        MulOpposite.unop (reverseHom n (sigma n (DElem n))) := by
  refine ⟨(sigma_DElem n).symm, ?_, ?_⟩
  · rw [reverse_DElem, smul_smul_neg_one_pow]
  · rw [reverse_sigma_DElem, smul_smul_neg_one_pow]

/-- Printed (3.51) with exponent `C(a-1,4)` fails at `a = 4`: `ψ(D_4) = -D_4`. -/
theorem eq_3_51_false :
    DElem 2 ≠ (-1 : ℤ)^((2+1).choose 4) • MulOpposite.unop (reverseHom 2 (DElem 2)) ∧
      DElem 2 ≠ (-1 : ℤ)^((2+1).choose 4) •
        MulOpposite.unop (reverseHom 2 (sigma 2 (DElem 2))) := by
  have hne : DElem 2 ≠ (-1 : ℤ) • DElem 2 := by
    intro h
    have := smul_DElem_inj (show (1 : ℤ) • DElem 2 = (-1 : ℤ) • DElem 2 by rwa [one_smul])
    omega
  have h3 : (2+1).choose 4 = 0 := by decide
  have h4 : (2+2).choose 4 = 1 := by decide
  refine ⟨?_, ?_⟩
  · rw [reverse_DElem, h3, h4, pow_zero, one_smul, pow_one]; exact hne
  · rw [reverse_sigma_DElem, h3, h4, pow_zero, one_smul, pow_one]; exact hne

theorem eq_3_51_printed_false :
    ¬ ∀ n : ℕ, DElem n = (-1 : ℤ)^((n+1).choose 4) • MulOpposite.unop (reverseHom n (DElem n)) :=
  fun h => eq_3_51_false.1 (h 2)

/-! ### (3.52)–(3.54) -/

/-- The two exponents of (3.52) agree. -/
theorem eq_3_52_sign (a : ℕ) :
    (-1 : ℤ)^((a+1).choose 4 + a.choose 4) = (-1 : ℤ)^(a.choose 3) := by
  rw [Nat.choose_succ_succ' a 3]
  rw [show a.choose 3 + a.choose (3+1) + a.choose 4 = a.choose 3 + 2 * a.choose 4 by ring,
    pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- The right-hand sides of (3.52) and (3.53) agree. -/
theorem eq_3_52_3_53 (n : ℕ) :
    (-1 : ℤ)^((n+2).choose 3) • (staircaseElem n * DElem n) =
      (-1 : ℤ)^((n+3).choose 4) •
        (MulOpposite.unop (reverseHom n (staircaseElem n)) * DElem n) := by
  rw [reverse_staircaseElem, smul_mul_assoc, smul_smul, ← pow_add]
  exact congrArg (· • _) (eq_3_52_sign (n+2)).symm

/-- `(-1)^{C(a,3)} x^{δ_a} D_a` is idempotent, as in (3.39). -/
theorem staircase_DElem_idempotent (n : ℕ) :
    IsIdempotentElem ((-1 : ℤ)^((n+2).choose 3) • (staircaseElem n * DElem n)) := by
  unfold IsIdempotentElem
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_smul, mul_assoc, ← mul_assoc (DElem n), DElem_staircase_DElem, mul_smul_comm]

theorem action_dot_pow_apply (j : Fin (n+2)) (k : ℕ) (f : SkewPolynomial (n+2)) :
    action n (dot n j ^ k) f = generator j ^ k * f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', action_mul_apply, ih, action_dot_apply, ← mul_assoc, ← pow_succ']

theorem action_dot_prod (e : Fin (n+2) → ℕ) (l : List (Fin (n+2))) (f : SkewPolynomial (n+2)) :
    action n ((l.map fun i => dot n i ^ e i).prod) f =
      (l.map fun i => generator i ^ e i).prod * f := by
  induction l with
  | nil => simp
  | cons j l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [action_mul_apply, ih, action_dot_pow_apply, mul_assoc]

/-- (3.54), operator form on the polynomials `x^{δ_a}` and `ψ(x^{δ_a})`. -/
theorem eq_3_54 (n : ℕ) :
    LongestDivided.D (n+2) (action n (staircaseElem n) 1) =
        (-1 : ℤ)^((n+2).choose 3) • (1 : SkewPolynomial (n+2)) ∧
      LongestDivided.D (n+2) (action n (MulOpposite.unop (reverseHom n (staircaseElem n))) 1) =
        (-1 : ℤ)^((n+3).choose 4) • (1 : SkewPolynomial (n+2)) := by
  refine ⟨?_, ?_⟩
  · rw [action_staircaseElem, mul_one, LongestDivided.D_staircase]
  · rw [reverse_staircaseElem, map_zsmul, LinearMap.smul_apply, action_staircaseElem, mul_one,
      map_zsmul, LongestDivided.D_staircase, smul_smul, ← pow_add,
      show (n+3).choose 4 = (n+2).choose 3 + (n+2).choose 4 from Nat.choose_succ_succ' (n+2) 3,
      add_comm ((n+2).choose 3)]

/-- (3.54), second equation, on the literal reversed product `x_a^0 x_{a-1}^1 ⋯ x_1^{a-1}`. -/
theorem eq_3_54_reversed (n : ℕ) :
    LongestDivided.D (n+2)
        (((List.finRange (n+2)).reverse.map fun i => generator i ^ (n+1-i.val)).prod) =
      (-1 : ℤ)^((n+3).choose 4) • (1 : SkewPolynomial (n+2)) := by
  have h := action_dot_prod (n := n) (fun i => n+1-i.val) (List.finRange (n+2)).reverse 1
  rw [mul_one, ← eq_3_48] at h
  rw [← h]
  exact (eq_3_54 n).2

end
/-- EKL (3.52): `e_a = (−1)^{C(a+1,4)+C(a,4)} x^{δ_a} D_a = (−1)^{C(a,3)} x^{δ_a} D_a`. -/
theorem eq_3_52 (n : ℕ) :
    ZeroHecke.projector n =
        (-1 : ℤ)^((n+3).choose 4 + (n+2).choose 4) • (staircaseElem n * DElem n) ∧
      ZeroHecke.projector n = (-1 : ℤ)^((n+2).choose 3) • (staircaseElem n * DElem n) := by
  refine ⟨?_, ZeroHecke.prop_3_5⟩
  rw [eq_3_52_sign (n+2), ZeroHecke.prop_3_5]

/-- EKL (3.53): `e_a = (−1)^{C(a+1,4)} ψ(x^{δ_a}) D_a`. -/
theorem eq_3_53 (n : ℕ) :
    ZeroHecke.projector n = (-1 : ℤ)^((n+3).choose 4) •
      (MulOpposite.unop (reverseHom n (staircaseElem n)) * DElem n) := by
  rw [ZeroHecke.prop_3_5, eq_3_52_3_53]

end OddMath.Frontier.OnhReflection
