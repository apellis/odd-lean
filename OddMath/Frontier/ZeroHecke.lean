import OddMath.Frontier.NilHeckeBasis
import OddMath.Frontier.LongestFactor

/-! # Odd 0-Hecke generators and the idempotent `e_a`

EKL arXiv:1111.1320v1, §3.2, (3.16)–(3.18), Props 3.5–3.6, pp. 22–28.

In the presented odd nilHecke ring `ONH_{n+2}` put `∂̄_i = x_i ∂_i` (3.16).  These satisfy the
0-Hecke relations (3.17)–(3.18): `∂̄_i² = ∂̄_i`, the braid relation for adjacent indices, and
exact commutation (not anticommutation) for distant indices.  Consequently the 0-Hecke product
along a reduced word depends only on the permutation.  The element `e_{n+2} = ∂̄_{w₀}` is formed
along the source word of `D_{n+2}`, and

* Prop 3.5: `e = (-1)^{C(n+2,3)} x^δ D`;
* Prop 3.6: `D ∂̄_i = D`, `D e = D`, `e² = e`, and `∂̄_i e = e = e ∂̄_i`.

Written products compose rightmost first; `x^δ = x_0^{n+1} x_1^{n} ⋯ x_{n+1}^0`.
-/
namespace OddMath.Frontier.ZeroHecke
open NilHeckeAction NilCoxeterWords NilHeckeBasis
open OddMath.SkewPolynomial (SkewPolynomial)
noncomputable section
variable {n : ℕ}

/-- EKL (3.16): the 0-Hecke generator ∂̄_r = x_r ∂_r. -/
def zeroHecke (n : ℕ) (i : Fin (n+1)) : Presented n := dot n i.castSucc * crossing n i

/-- The 0-Hecke product along a word, in written order. -/
def zeroHeckeProduct {n : ℕ} : Word n → Presented n
  | [] => 1
  | i::w => zeroHecke n i * zeroHeckeProduct w

/-- e_a = ∂̄_{w0} along the source word of D_a. -/
def projector (n : ℕ) : Presented n := zeroHeckeProduct (LongestDivided.wordIn n (n+2) le_rfl)

/-- The longest divided difference `D_{n+2}` along its source word (2.36). -/
def DElem (n : ℕ) : Presented n := product (LongestDivided.wordIn n (n+2) le_rfl)

/-- The ordered staircase monomial `x^δ` of (2.40). -/
def staircaseElem (n : ℕ) : Presented n := NilHeckeBasis.dotMonomial (fun i => n+1-i.val)

@[simp] theorem zeroHeckeProduct_nil : zeroHeckeProduct ([] : Word n) = 1 := rfl
@[simp] theorem zeroHeckeProduct_cons (i : Fin (n+1)) (w : Word n) :
    zeroHeckeProduct (i::w) = zeroHecke n i * zeroHeckeProduct w := rfl

@[simp] theorem zeroHeckeProduct_append (u v : Word n) :
    zeroHeckeProduct (u++v) = zeroHeckeProduct u * zeroHeckeProduct v := by
  induction u with
  | nil => simp
  | cons i u ih => simp [ih, mul_assoc]

@[simp] theorem zeroHeckeProduct_singleton (i : Fin (n+1)) :
    zeroHeckeProduct [i] = zeroHecke n i := mul_one _

/-! ## The 0-Hecke relations (3.17)–(3.18) -/

theorem crossing_mul_zeroHecke (i : Fin (n+1)) :
    crossing n i * zeroHecke n i = crossing n i := by
  rw [zeroHecke, ← mul_assoc, crossing_dot_left, sub_mul, one_mul, mul_assoc,
    crossing_square, mul_zero, sub_zero]

/-- EKL (3.17). -/
theorem zeroHecke_sq (i : Fin (n+1)) : zeroHecke n i * zeroHecke n i = zeroHecke n i := by
  calc zeroHecke n i * zeroHecke n i = dot n i.castSucc * (crossing n i * zeroHecke n i) := by
        rw [zeroHecke, mul_assoc]
    _ = zeroHecke n i := by rw [crossing_mul_zeroHecke]; rfl

theorem dot_anticommute (i j : Fin (n+2)) (h : i ≠ j) :
    dot n i * dot n j = -(dot n j * dot n i) :=
  eq_neg_of_add_eq_zero_left (dots_anticommute i j h)

/-- Distant 0-Hecke generators commute (the two sign changes cancel). -/
theorem zeroHecke_distant (i j : Fin (n+1)) (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    zeroHecke n i * zeroHecke n j = zeroHecke n j * zeroHecke n i := by
  have ne (a b : Fin (n+1)) (hab : a.val+1 < b.val ∨ b.val+1 < a.val) :
      b.castSucc ≠ a.castSucc ∧ b.castSucc ≠ a.succ := by
    constructor <;> intro e <;> have hv := congrArg Fin.val e <;>
      simp only [Fin.coe_castSucc, Fin.val_succ] at hv <;> omega
  have key (a b : Fin (n+1)) (hab : a.val+1 < b.val ∨ b.val+1 < a.val) :
      zeroHecke n a * zeroHecke n b =
        -(dot n a.castSucc * dot n b.castSucc * (crossing n a * crossing n b)) := by
    simp only [zeroHecke, mul_assoc]
    rw [← mul_assoc (crossing n a), crossing_dot_other a b.castSucc (ne a b hab).1 (ne a b hab).2]
    simp only [neg_mul, mul_neg, mul_assoc]
  rw [key i j h, key j i (by omega), dot_anticommute i.castSucc j.castSucc (ne j i (by omega)).1,
    crossing_distant i j h, neg_mul_neg]

/-- EKL (3.18): the braid relation for adjacent indices. -/
theorem zeroHecke_braid (i j : Fin (n+1)) (h : j.val = i.val+1) :
    zeroHecke n i * zeroHecke n j * zeroHecke n i =
      zeroHecke n j * zeroHecke n i * zeroHecke n j := by
  have hij : j.castSucc = i.succ := Fin.ext (by simp [h])
  have h1 : ∀ x, crossing n j * (dot n i.castSucc * x) =
      -(dot n i.castSucc * (crossing n j * x)) := by
    intro x
    have hl : i.castSucc ≠ j.castSucc := by
      intro e; have hv := congrArg Fin.val e; simp only [Fin.coe_castSucc] at hv; omega
    have hr : i.castSucc ≠ j.succ := by
      intro e; have hv := congrArg Fin.val e
      simp only [Fin.coe_castSucc, Fin.val_succ] at hv; omega
    rw [← mul_assoc, crossing_dot_other j _ hl hr, neg_mul, mul_assoc]
  have h2 : ∀ x, crossing n i * (dot n i.castSucc * x) =
      x - dot n i.succ * (crossing n i * x) := by
    intro x; rw [← mul_assoc, crossing_dot_left, sub_mul, one_mul, mul_assoc]
  have h3 : ∀ x, crossing n i * (dot n i.succ * x) =
      x - dot n i.castSucc * (crossing n i * x) := by
    intro x; rw [← mul_assoc, crossing_dot_right, sub_mul, one_mul, mul_assoc]
  have h4 : ∀ x, dot n i.succ * (dot n i.castSucc * x) =
      -(dot n i.castSucc * (dot n i.succ * x)) := by
    intro x
    rw [← mul_assoc, dot_anticommute _ _ (AllRankDivided.adjacent_ne i).symm, neg_mul, mul_assoc]
  have h5 : ∀ x, crossing n j * (crossing n j * x) = 0 := by
    intro x; rw [← mul_assoc, crossing_square, zero_mul]
  have h6 : crossing n j * (crossing n i * crossing n j) =
      crossing n i * (crossing n j * crossing n i) := by
    simpa only [mul_assoc] using (crossing_braid i j h).symm
  simp only [zeroHecke, hij, mul_assoc, h1, h2, h3, h4, h5, h6, mul_sub, sub_mul, mul_neg,
    neg_mul, neg_neg, mul_zero, sub_zero, neg_zero, crossing_square]
  abel

/-! ## Matsumoto for 0-Hecke products -/

private theorem join_distant (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j)
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧
        zeroHeckeProduct a * zeroHecke n i = zeroHeckeProduct b * zeroHecke n j := by
  obtain ⟨u, hu, hul⟩ := exists_reduced (p * simple i * simple j)
  have hpi : permutation (u++[j]) = p * simple i := by simp [hu, mul_assoc]
  have hpj : permutation (u++[i]) = p * simple j := by
    simp only [permutation_append, permutation_singleton, hu]
    calc
      p * simple i * simple j * simple i = p * (simple i * simple j) * simple i := by
        simp [mul_assoc]
      _ = p * (simple j * simple i) * simple i := by rw [simple_distant i j h]
      _ = p * simple j := by simp [mul_assoc]
  have hli := length_descend p i hi
  have hlj := length_descend p j hj
  have hlq := length_descend (p * simple i) j ((descent_distant p i j h).mpr hj)
  refine ⟨u++[j], u++[i], hpi, hpj, ?_, ?_, ?_⟩
  · unfold Reduced; rw [hpi]; simp only [List.length_append, List.length_singleton]; omega
  · unfold Reduced; rw [hpj]; simp only [List.length_append, List.length_singleton]; omega
  · simp only [zeroHeckeProduct_append, zeroHeckeProduct_singleton, mul_assoc]
    rw [zeroHecke_distant j i (by omega)]

private theorem join_adjacent (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j) (h : j.val = i.val+1) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧
        zeroHeckeProduct a * zeroHecke n i = zeroHeckeProduct b * zeroHecke n j := by
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
  · unfold Reduced; rw [hpi]
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · unfold Reduced; rw [hpj]
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · simpa only [zeroHeckeProduct_append, zeroHeckeProduct_cons, zeroHeckeProduct_nil, mul_one,
      mul_assoc] using congrArg (zeroHeckeProduct u * ·) (zeroHecke_braid i j h)

/-- Local descent joins for 0-Hecke products: exact equalities, no signs. -/
theorem zeroHecke_join (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧
        zeroHeckeProduct a * zeroHecke n i = zeroHeckeProduct b * zeroHecke n j := by
  by_cases he : i = j
  · subst j
    obtain ⟨u, hu, hl⟩ := exists_reduced (p * simple i)
    exact ⟨u, u, hu, hu, by simpa [Reduced, hu] using hl, by simpa [Reduced, hu] using hl, rfl⟩
  · by_cases h₁ : j.val = i.val+1
    · exact join_adjacent p i j hi hj h₁
    · by_cases h₂ : i.val = j.val+1
      · obtain ⟨a, b, ha, hb, hra, hrb, hs⟩ := join_adjacent p j i hj hi h₂
        exact ⟨b, a, hb, ha, hrb, hra, hs.symm⟩
      · apply join_distant p i j hi hj
        have : i.val ≠ j.val := fun h => he (Fin.ext h)
        omega

/-- 0-Hecke Matsumoto: reduced words of one permutation have EQUAL 0-Hecke products. -/
theorem zeroHeckeProduct_reduced_eq (w v : Word n) (hw : Reduced w) (hv : Reduced v)
    (hp : permutation w = permutation v) : zeroHeckeProduct w = zeroHeckeProduct v := by
  induction h : w.length using Nat.strong_induction_on generalizing w v with
  | h k ih =>
    cases w using List.reverseRecOn with
    | nil =>
        have hv0 : v.length = 0 := by simpa [Reduced, ← hp, permutation] using hv
        have : v = [] := List.length_eq_zero_iff.mp hv0
        subst v
        rfl
    | append_singleton w i =>
        cases v using List.reverseRecOn with
        | nil => simp [Reduced, hp, permutation] at hw
        | append_singleton v j =>
            obtain ⟨hwr, hwi⟩ := reduced_prefix w i hw
            obtain ⟨hvr, hvj⟩ := reduced_prefix v j hv
            let p := permutation (w++[i])
            have hpi : p * simple i = permutation w := by simp [p, mul_assoc]
            have hpj : p * simple j = permutation v := by simp [p, hp, mul_assoc]
            have hd₁ : Descent p i := by
              simpa [p] using descent_after_ascend (permutation w) i hwi
            have hd₂ : Descent p j := by
              simpa [p, hp] using descent_after_ascend (permutation v) j hvj
            obtain ⟨a, b, ha, hb, hra, hrb, hs⟩ := zeroHecke_join p i j hd₁ hd₂
            have hwa := ih w.length
              (by simp only [List.length_append, List.length_singleton] at h; omega)
              w a hwr hra (by rw [ha, hpi]) rfl
            have hvb := ih v.length (by
                have he : v.length = w.length := by
                  unfold Reduced at hw hv
                  rw [← hp] at hv
                  simp only [List.length_append, List.length_singleton] at hw hv
                  omega
                simp only [List.length_append, List.length_singleton] at h
                omega) v b hvr hrb (by rw [hb, hpj]) rfl
            simp only [zeroHeckeProduct_append, zeroHeckeProduct_singleton, hwa, hvb, hs]

/-- `e_{n+2}` is the 0-Hecke product along ANY reduced word of the longest permutation. -/
theorem projector_eq_of_reduced (w : Word n) (hw : Reduced w)
    (hp : permutation w = LongestElementary.longest (n+2)) :
    projector n = zeroHeckeProduct w :=
  zeroHeckeProduct_reduced_eq _ w (sourceWord_reduced n) hw
    ((sourceWord_permutation n).trans hp.symm)

theorem projector_eq_of_length (w : Word n) (hw : Reduced w) (hl : w.length = (n+2).choose 2) :
    projector n = zeroHeckeProduct w :=
  projector_eq_of_reduced w hw (eq_longest_of_length _ (hw.symm.trans hl))

/-! ## Absorption: Prop 3.6 -/

theorem longest_mul_simple_rev (i : Fin (n+1)) :
    LongestElementary.longest (n+2) * simple i.rev = simple i * LongestElementary.longest (n+2) := by
  have hl : i.rev.castSucc = i.succ.rev := by rw [Fin.rev_succ]
  have hr : i.rev.succ = i.castSucc.rev := by rw [Fin.rev_castSucc]
  rw [simple, hl, hr, Equiv.mul_swap_eq_swap_mul, LongestElementary.longest_apply,
    LongestElementary.longest_apply, Fin.rev_rev, Fin.rev_rev, Equiv.swap_comm]
  rfl

/-- A reduced word of the longest permutation beginning with any prescribed letter. -/
theorem exists_reduced_starting (i : Fin (n+1)) :
    ∃ w : Word n, Reduced (i :: w) ∧ permutation (i :: w) = LongestElementary.longest (n+2) := by
  obtain ⟨u, hr, hl⟩ := LongestFactor.exists_reduced_ending n i.rev
  have hp : permutation (u ++ [i.rev]) = LongestElementary.longest (n+2) :=
    eq_longest_of_length _ (hr.symm.trans hl)
  have hu : permutation u = simple i * LongestElementary.longest (n+2) := by
    rw [← longest_mul_simple_rev, ← hp, permutation_append, permutation_singleton,
      mul_simple_cancel]
  have hpi : permutation (i :: u) = LongestElementary.longest (n+2) := by
    rw [permutation, hu, ← mul_assoc, simple_square, one_mul]
  refine ⟨u, ?_, hpi⟩
  unfold Reduced
  rw [hpi, LongestFactor.length_longest, ← hl]
  simp

theorem exists_reduced_ending' (i : Fin (n+1)) :
    ∃ w : Word n, Reduced (w ++ [i]) ∧
      permutation (w ++ [i]) = LongestElementary.longest (n+2) := by
  obtain ⟨w, hr, hl⟩ := LongestFactor.exists_reduced_ending n i
  exact ⟨w, hr, eq_longest_of_length _ (hr.symm.trans hl)⟩

/-- Prop 3.6: `∂̄_i e = e`. -/
theorem zeroHecke_mul_projector (i : Fin (n+1)) :
    zeroHecke n i * projector n = projector n := by
  obtain ⟨w, hr, hp⟩ := exists_reduced_starting i
  rw [projector_eq_of_reduced _ hr hp, zeroHeckeProduct_cons, ← mul_assoc, zeroHecke_sq]

/-- Prop 3.6: `e ∂̄_i = e`. -/
theorem projector_mul_zeroHecke (i : Fin (n+1)) :
    projector n * zeroHecke n i = projector n := by
  obtain ⟨w, hr, hp⟩ := exists_reduced_ending' i
  rw [projector_eq_of_reduced _ hr hp, zeroHeckeProduct_append, zeroHeckeProduct_singleton,
    mul_assoc, zeroHecke_sq]

theorem projector_mul_zeroHeckeProduct (w : Word n) :
    projector n * zeroHeckeProduct w = projector n := by
  induction w with
  | nil => exact mul_one _
  | cons i w ih => rw [zeroHeckeProduct_cons, ← mul_assoc, projector_mul_zeroHecke, ih]

/-- Prop 3.6(3): `e` is idempotent. -/
theorem projector_mul_projector : projector n * projector n = projector n :=
  projector_mul_zeroHeckeProduct _

/-- Prop 3.6(1): `D ∂̄_i = D` for every `i`. -/
theorem DElem_mul_zeroHecke (i : Fin (n+1)) : DElem n * zeroHecke n i = DElem n := by
  obtain ⟨w, hr, hp⟩ := exists_reduced_ending' i
  rcases reduced_signed _ (w ++ [i]) (sourceWord_reduced n) hr
      ((sourceWord_permutation n).trans hp.symm) with h | h <;>
    rw [DElem, h] <;>
    simp only [product_append, product_singleton, mul_assoc, crossing_mul_zeroHecke, neg_mul]

theorem DElem_mul_zeroHeckeProduct (w : Word n) : DElem n * zeroHeckeProduct w = DElem n := by
  induction w with
  | nil => exact mul_one _
  | cons i w ih => rw [zeroHeckeProduct_cons, ← mul_assoc, DElem_mul_zeroHecke, ih]

/-- Prop 3.6(2): `D e = D`. -/
theorem DElem_mul_projector : DElem n * projector n = DElem n :=
  DElem_mul_zeroHeckeProduct _

/-! ## Prop 3.5: moving the dots of `∂̄_{w₀}` to the left -/

/-- Commutation up to one global sign. -/
def SComm (x y : Presented n) : Prop := Signed (x * y) (y * x)

theorem SComm.mul_right {x y z : Presented n} (hy : SComm x y) (hz : SComm x z) :
    SComm x (y * z) := by
  unfold SComm at *
  have h1 := hy.mul (Signed.refl z)
  have h2 := (Signed.refl y).mul hz
  simp only [mul_assoc] at h1 h2 ⊢
  exact h1.trans h2

theorem SComm.mul_left {x y z : Presented n} (hx : SComm x z) (hy : SComm y z) :
    SComm (x * y) z := by
  unfold SComm at *
  have h1 := (Signed.refl x).mul hy
  have h2 := hx.mul (Signed.refl y)
  simp only [mul_assoc] at h1 h2 ⊢
  exact h1.trans h2

theorem signed_neg (a : Presented n) : Signed (-a) a := Or.inr rfl

theorem signed_sign_smul (e : ℕ) (a : Presented n) : Signed ((-1 : ℤ)^e • a) a := by
  rcases neg_one_pow_eq_or ℤ e with h | h
  · exact Or.inl (by rw [h, one_smul])
  · exact Or.inr (by rw [h, neg_one_smul])

theorem dotWord_append (u v : List (Fin (n+2))) :
    dotWord (u ++ v) = dotWord u * dotWord v := by
  simp [dotWord, List.map_append, List.prod_append]

theorem sComm_crossing_dot (i : Fin (n+1)) (j : Fin (n+2))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) : SComm (crossing n i) (dot n j) := by
  unfold SComm
  rw [crossing_dot_other i j hl hr]
  exact signed_neg _

theorem sComm_crossing_dotWord (i : Fin (n+1)) (v : List (Fin (n+2)))
    (hv : ∀ j ∈ v, j ≠ i.castSucc ∧ j ≠ i.succ) : SComm (crossing n i) (dotWord v) := by
  induction v with
  | nil => simpa [SComm] using Signed.refl (crossing n i)
  | cons j v ih =>
      rw [dotWord_cons]
      exact (sComm_crossing_dot i j (hv j (by simp)).1 (hv j (by simp)).2).mul_right
        (ih fun k hk => hv k (by simp [hk]))

theorem sComm_crossing_pair (i : Fin (n+1)) :
    SComm (crossing n i) (dot n i.succ * dot n i.castSucc) := by
  unfold SComm
  have h : crossing n i * (dot n i.succ * dot n i.castSucc) =
      -(dot n i.succ * dot n i.castSucc * crossing n i) := by
    rw [← mul_assoc, crossing_dot_right, sub_mul, one_mul, mul_assoc, crossing_dot_left,
      mul_sub, mul_one, sub_sub_cancel, ← mul_assoc,
      dot_anticommute _ _ (AllRankDivided.adjacent_ne i), neg_mul]
  rw [h]
  exact signed_neg _

theorem sComm_product {X : Presented n} (w : Word n)
    (hw : ∀ i ∈ w, SComm (crossing n i) X) : SComm (product w) X := by
  induction w with
  | nil => simpa [SComm, product] using Signed.refl X
  | cons i w ih =>
      exact (hw i (by simp)).mul_left (ih fun k hk => hw k (by simp [hk]))

/-- The dots `x_{k-1}, …, x_1, x_0` in written order. -/
def downDots (n : ℕ) : (k : ℕ) → k ≤ n+2 → List (Fin (n+2))
  | 0, _ => []
  | k+1, h => ⟨k, by omega⟩ :: downDots n k (by omega)

/-- The crossings `∂_{k-1}, …, ∂_1, ∂_0` in written order. -/
def sweepWord (n : ℕ) : (k : ℕ) → k ≤ n+1 → Word n
  | 0, _ => []
  | k+1, h => ⟨k, by omega⟩ :: sweepWord n k (by omega)

/-- The dots of the partial staircase `x_0^{k-1} ⋯ x_{k-2}`, in an unsorted order. -/
def stairDots (n : ℕ) : (k : ℕ) → k ≤ n+2 → List (Fin (n+2))
  | 0, _ => []
  | k+1, h => stairDots n k (by omega) ++ downDots n k (by omega)

theorem mem_downDots {k : ℕ} {h : k ≤ n+2} {j : Fin (n+2)} (hj : j ∈ downDots n k h) :
    j.val < k := by
  induction k with
  | zero => simp [downDots] at hj
  | succ k ih =>
      simp only [downDots, List.mem_cons] at hj
      rcases hj with rfl | hj
      · simp
      · have := ih hj; omega

theorem count_downDots (k : ℕ) (h : k ≤ n+2) (j : Fin (n+2)) :
    (downDots n k h).count j = if j.val < k then 1 else 0 := by
  induction k with
  | zero => simp [downDots]
  | succ k ih =>
      rw [downDots, List.count_cons, ih]
      by_cases hj : j.val = k
      · have : (⟨k, by omega⟩ : Fin (n+2)) = j := Fin.ext hj.symm
        simp [this, hj]
      · have : (⟨k, by omega⟩ : Fin (n+2)) ≠ j := fun e => hj (by rw [← e])
        simp only [beq_iff_eq, this, if_false, add_zero]
        split_ifs <;> omega

theorem count_stairDots (k : ℕ) (h : k ≤ n+2) (j : Fin (n+2)) :
    (stairDots n k h).count j = if j.val < k then k - 1 - j.val else 0 := by
  induction k with
  | zero => simp [stairDots]
  | succ k ih =>
      rw [stairDots, List.count_append, ih, count_downDots]
      split_ifs <;> omega

theorem sweepWord_values (k : ℕ) (h : k ≤ n+1) :
    (sweepWord n k h).map Fin.val = (List.range k).reverse := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sweepWord, ih, List.range_succ]

theorem wordIn_succ (k : ℕ) (h : k+1 ≤ n+2) :
    LongestDivided.wordIn n (k+1) h =
      LongestDivided.wordIn n k (by omega) ++ sweepWord n k (by omega) := by
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [List.map_append, LongestDivided.wordIn_values, LongestDivided.wordIn_values,
    sweepWord_values]
  rfl

theorem sComm_downDots (k : ℕ) (h : k ≤ n+2) (i : Fin (n+1)) (hi : i.val+1 < k) :
    SComm (crossing n i) (dotWord (downDots n k h)) := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [downDots, dotWord_cons]
      by_cases hk : i.val+1 < k
      · apply SComm.mul_right _ (ih (by omega) hk)
        apply sComm_crossing_dot <;> intro e <;> have hv := congrArg Fin.val e <;>
          simp only [Fin.coe_castSucc, Fin.val_succ] at hv <;> omega
      · obtain ⟨m, rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩
        have hm : i.val = m := by omega
        rw [downDots, dotWord_cons, ← mul_assoc]
        have e1 : (⟨m+1, by omega⟩ : Fin (n+2)) = i.succ := Fin.ext (by simp [hm])
        have e2 : (⟨m, by omega⟩ : Fin (n+2)) = i.castSucc := Fin.ext (by simp [hm])
        rw [e1, e2]
        apply (sComm_crossing_pair i).mul_right
        apply sComm_crossing_dotWord
        intro j hj
        have := mem_downDots hj
        constructor <;> intro e <;> have hv := congrArg Fin.val e <;>
          simp only [Fin.coe_castSucc, Fin.val_succ] at hv <;> omega

theorem sweep_signed (k : ℕ) (h : k ≤ n+1) :
    Signed (zeroHeckeProduct (sweepWord n k h))
      (dotWord (downDots n k (by omega)) * product (sweepWord n k h)) := by
  induction k with
  | zero => simpa [sweepWord, downDots, product] using Signed.refl (1 : Presented n)
  | succ k ih =>
      rw [sweepWord, zeroHeckeProduct_cons, downDots, dotWord_cons, product]
      have hs : SComm (crossing n ⟨k, by omega⟩) (dotWord (downDots n k (by omega))) := by
        apply sComm_crossing_dotWord
        intro j hj
        have := mem_downDots hj
        constructor <;> intro e <;> have hv := congrArg Fin.val e <;>
          simp only [Fin.coe_castSucc, Fin.val_succ] at hv <;> omega
      have h1 := (Signed.refl (zeroHecke n ⟨k, by omega⟩)).mul (ih (by omega))
      have h2 := ((Signed.refl (dot n ⟨k, by omega⟩)).mul hs).mul
        (Signed.refl (product (sweepWord n k (by omega))))
      simp only [zeroHecke, Fin.castSucc_mk, mul_assoc] at h1 h2 ⊢
      exact h1.trans h2

theorem wordIn_bound {k : ℕ} {h : k ≤ n+2} {i : Fin (n+1)}
    (hi : i ∈ LongestDivided.wordIn n k h) : i.val+1 < k := by
  apply LongestDivided.coxeterWord_bound
  rw [← LongestDivided.wordIn_values n k h]
  exact List.mem_map_of_mem hi

theorem partial_signed (k : ℕ) (h : k ≤ n+2) :
    Signed (zeroHeckeProduct (LongestDivided.wordIn n k h))
      (dotWord (stairDots n k h) * product (LongestDivided.wordIn n k h)) := by
  induction k with
  | zero => simpa [stairDots, product] using Signed.refl (1 : Presented n)
  | succ k ih =>
      rw [wordIn_succ, zeroHeckeProduct_append, product_append, stairDots, dotWord_append]
      have hc : SComm (product (LongestDivided.wordIn n k (by omega)))
          (dotWord (downDots n k (by omega))) :=
        sComm_product _ fun i hi => sComm_downDots k _ i (wordIn_bound hi)
      have h1 := (ih (by omega)).mul (sweep_signed k (by omega))
      have h2 := ((Signed.refl (dotWord (stairDots n k (by omega)))).mul hc).mul
        (Signed.refl (product (sweepWord n k (by omega))))
      simp only [mul_assoc] at h1 h2 ⊢
      exact h1.trans h2

/-- Prop 3.5 up to one global sign. -/
theorem projector_signed : Signed (projector n) (staircaseElem n * DElem n) := by
  have h := partial_signed (n := n) (n+2) le_rfl
  rw [dotWord_normalize, smul_mul_assoc] at h
  have hc : (fun j => (stairDots n (n+2) le_rfl).count j) = fun j : Fin (n+2) => n+1-j.val := by
    funext j
    rw [count_stairDots, if_pos j.isLt]
    omega
  rw [hc] at h
  exact h.trans (signed_sign_smul _ _)

/-! ## Prop 3.5 with its exact sign -/

theorem action_DElem : action n (DElem n) = LongestDivided.D (n+2) := by
  rw [DElem, action_product]
  rfl

theorem action_staircaseElem_apply (f : SkewPolynomial (n+2)) :
    action n (staircaseElem n) f = LongestDivided.staircase (n+2) * f := by
  rw [staircaseElem, action_dotMonomial]
  rfl

private theorem sign_sq (e : ℕ) : ((-1 : ℤ)^e) * (-1)^e = 1 := by
  rw [← mul_pow]; norm_num

/-- The global sign in `e = ε x^δ D` is forced by `D e = D` on the staircase. -/
theorem sign_of_projector_eq (ε : ℤ) (h : projector n = ε • (staircaseElem n * DElem n)) :
    ε = (-1 : ℤ)^((n+2).choose 3) := by
  have he := congrArg (fun x => action n x (LongestDivided.staircase (n+2)))
    (DElem_mul_projector (n := n))
  simp only [h, action_mul_apply, mul_smul_comm, map_zsmul, LinearMap.smul_apply,
    action_DElem, action_staircaseElem_apply, LongestDivided.D_staircase, mul_one] at he
  rw [smul_smul, smul_smul, mul_assoc, sign_sq, mul_one, ← sub_eq_zero, ← sub_smul] at he
  rcases smul_eq_zero.mp he with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 one_ne_zero

/-- EKL Prop 3.5: `e_{n+2} = (-1)^{C(n+2,3)} x^δ D_{n+2}`. -/
theorem prop_3_5 :
    projector n = (-1 : ℤ)^((n+2).choose 3) • (staircaseElem n * DElem n) := by
  rcases projector_signed (n := n) with h | h
  · have hε := sign_of_projector_eq 1 (by rw [h, one_smul])
    rw [← hε, one_smul, h]
  · have hε := sign_of_projector_eq (-1) (by rw [h, neg_one_smul])
    rw [← hε, neg_one_smul, h]

/-- Operator form of Prop 3.5: `e f = (-1)^{C(n+2,3)} x^δ D f`. -/
theorem action_projector (f : SkewPolynomial (n+2)) :
    action n (projector n) f =
      (-1 : ℤ)^((n+2).choose 3) •
        (LongestDivided.staircase (n+2) * LongestDivided.D (n+2) f) := by
  rw [prop_3_5, map_zsmul, LinearMap.smul_apply, action_mul_apply, action_DElem,
    action_staircaseElem_apply]

/-- `∂̄_i x^δ D = x^δ D` for every `i`. -/
theorem zeroHecke_mul_staircase_DElem (i : Fin (n+1)) :
    zeroHecke n i * (staircaseElem n * DElem n) = staircaseElem n * DElem n := by
  have h := zeroHecke_mul_projector (n := n) i
  rw [prop_3_5, mul_smul_comm] at h
  have h' := congrArg (fun x => (-1 : ℤ)^((n+2).choose 3) • x) h
  simpa only [smul_smul, sign_sq, one_smul] using h'

/-- `x^δ D ∂̄_i = x^δ D` for every `i`. -/
theorem staircase_DElem_mul_zeroHecke (i : Fin (n+1)) :
    staircaseElem n * DElem n * zeroHecke n i = staircaseElem n * DElem n := by
  rw [mul_assoc, DElem_mul_zeroHecke]

end
end OddMath.Frontier.ZeroHecke
