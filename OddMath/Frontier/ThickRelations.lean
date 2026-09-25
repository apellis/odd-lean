import OddMath.Frontier.ThickMatrixUnits
import OddMath.Frontier.ElementaryBranching

/-! # Relations of the odd thin and thick calculus

EKL arXiv:1111.1320v1, §3.2.2–§3.2.4 (3.19)–(3.44), §4.1.1 (4.1)–(4.6), §4.2 (4.12)–(4.23),
(4.42), (4.46), Remark 3.4 and Remark 4.12; pp. 23–34, 38, 40–41.

Ambient ring `ONH_{n+2} = NilHeckeAction.Presented n`, strands `0, …, n+1` (0-based); a written
product `x * y` is `x` drawn on top of `y` (the rightmost factor acts first).  Blocks sit on
strand windows `[p, p+k)`: `blockD`, `blockE` are `D_k`, `e_k` (`ThickBubble`),
`downWord p k = ∂_{p+k-1} ⋯ ∂_p` is one strand descending from position `p+k` to `p`,
`upWord p k = ∂_p ⋯ ∂_{p+k-1}` one strand descending from `p` to `p+k`, and `crossWord p a b` is
the crossing `X_{a,b}` of (3.41).

* §3.2.2: Lemma 3.1 (3.19) `lemma_3_1` and Lemma 3.2 (3.22) `lemma_3_2` hold with no sign;
  Lemma 3.3 (3.24) `lemma_3_3` with the printed sign `(-1)^{C(a,3)}`.  Each crossing of `D_a`
  slides through the strand with sign `(-1)^a` (`cross_down_shift`), and
  `a C(a,2) ≡ C(a,3) (mod 2)`.
* §3.2.3: (3.28) `eq_3_28`, (3.31) `eq_3_31`, and (3.29) `eq_3_29`: `e_a` slides from the bottom
  right to the top left through a strand descending from the right, exactly.  Remark 3.4 (3.30):
  the mirror slide fails already in `ONH_3` (`remark_3_4`).  (3.40) `eq_3_40`.
* §3.2.4: (3.42) on windows (`crossWord_add`, `crossWord_split`), (3.43) `eq_3_43`, (3.44)
  `eq_3_44` (any window) and `eq_3_44_full`.  The proof of (3.44) writes
  `(e_a ⊗ e_b) X_{a,b} = c · M · D_{a+b}` (Props 3.5, 3.7) and uses `D e = D`.
* §4.1.1: splitters, mergers and thick crossings (4.1)–(4.2) on windows (`splitAt`, `mergeAt`,
  `thickCross`, `eq_4_2`); Prop 4.1 (4.3) `prop_4_1_split` with the printed sign
  `(-1)^{ab C(c,2)}` and (4.4) `prop_4_1_merge`; Prop 4.2 (4.5) `prop_4_2_left` and (4.6)
  `prop_4_2_right` with the printed sign `(-1)^{C(a,2) bc}`, for all `a, b, c ≥ 0`.
* §4.2: with the exploders (4.12) `D_a` and `e_a`: (4.13) `eq_4_13`, (4.14) `eq_4_14`, (4.15)
  `eq_4_15`, (4.16) `eq_4_16`, (4.23) `eq_4_23`.
* §4.3–4.4: (4.42) `eq_4_42` (with `eq_4_42_zero`), from EKL (2.23) and (4.9); (4.46) `eq_4_46`,
  from Prop 4.11 with `b = 1`; Remark 4.12 `remark_4_12`: `D_4(x_0^3 x_2^3) = -2`
  (`remark_4_12_value`) and `D_4(x_0^3 x_3^3) = 0`. -/
namespace OddMath.Frontier.ThickRelations
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords NilHeckeBasis LongestDivided LongestReversal
open ZeroHecke OnhWindow StrandCrossing ThickBubble

noncomputable section

/-! ## Operator identities -/

section Operators
variable (n : ℕ)

/-- One crossing slides down through a strand descending from the right. -/
theorem cross_down_shift (j : ℕ) : ∀ (p a : ℕ), j + 2 ≤ a → ∀ f : SkewPolynomial (n+2),
    cross n (p+j) (down n p a f) = (-1 : ℤ)^a • down n p a (cross n (p+j+1) f) := by
  induction j with
  | zero =>
      intro p a ha f
      obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
      have hs := (right_down n (x := cross n p) (e := 1) (p+1+1) a
        fun i _ => cross_far n (by unfold Far; omega)).apply
      change cross n p (down n (p+1+1) a (cross n (p+1) (cross n p f))) =
        (-1 : ℤ)^(a+2) • down n (p+1+1) a (cross n (p+1) (cross n p (cross n (p+1) f)))
      rw [hs, cross_braid_apply, pow_add, neg_one_sq, mul_one, mul_one]
  | succ j ih =>
      intro p a ha f
      obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have hf := (cross_far n (i := p+1+j+1) (j := p) (by unfold Far; omega)).apply
      change cross n (p+(j+1)) (down n (p+1) a (cross n p f)) =
        (-1 : ℤ)^(a+1) • down n (p+1) a (cross n p (cross n (p+(j+1)+1) f))
      rw [show p+(j+1) = p+1+j by omega, ih (p+1) a (by omega), hf, map_smul, smul_smul,
        pow_one, ← pow_succ, show p+1+j+1 = p+1+j+1 from rfl]

theorem mem_triList_ge {p k j : ℕ} (h : j ∈ triList p k) : p ≤ j := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  omega

theorem triList_map_succ (p k : ℕ) : (triList p k).map (· + 1) = triList (p+1) k := by
  rw [triList, triList, List.map_map]
  congr 1
  funext i
  simp only [Function.comp_apply]
  omega

theorem length_triList (p k : ℕ) : (triList p k).length = k.choose 2 := by
  rw [triList, List.length_map, coxeterWord_length]

/-- A word on the strands `[p, p+a)` slides down through a strand descending from the right. -/
theorem actNat_down_shift (p a : ℕ) (l : List ℕ) (hl : ∀ j ∈ l, p ≤ j ∧ j + 2 ≤ p + a)
    (f : SkewPolynomial (n+2)) :
    actNat n l (down n p a f) =
      (-1 : ℤ)^(a * l.length) • down n p a (actNat n (l.map (· + 1)) f) := by
  induction l with
  | nil => simp [actNat]
  | cons j l ih =>
      obtain ⟨hj, hl⟩ := List.forall_mem_cons.mp hl
      have hs := cross_down_shift n (j-p) p a (by omega)
      rw [show p + (j-p) = j by omega] at hs
      change cross n j (actNat n l (down n p a f)) =
        (-1 : ℤ)^(a * (l.length+1)) • down n p a (cross n (j+1) (actNat n (l.map (· + 1)) f))
      rw [ih hl, map_smul, hs, smul_smul, ← pow_add]
      congr 2

/-- `a C(a,2) ≡ C(a,3) (mod 2)`. -/
theorem neg_one_pow_mul_choose (a : ℕ) : (-1 : ℤ)^(a * a.choose 2) = (-1 : ℤ)^(a.choose 3) := by
  rw [ThickMatrixUnits.mul_choose_two, pow_add, pow_mul, pow_mul, neg_one_sq, one_pow, mul_one]
  norm_num

/-- Operator form of EKL Lemma 3.3 (3.24). -/
theorem triangle_down (p a : ℕ) :
    triangle n p a * down n p a = (-1 : ℤ)^(a.choose 3) • (down n p a * triangle n (p+1) a) := by
  apply LinearMap.ext
  intro f
  have h := actNat_down_shift n p a (triList p a) (fun j hj => ⟨mem_triList_ge hj, by
    have := mem_triList hj; omega⟩) f
  rw [triList_map_succ, actNat_triList, actNat_triList, length_triList,
    neg_one_pow_mul_choose] at h
  simpa only [Module.End.mul_apply, LinearMap.smul_apply] using h

/-- The ascending word `∂_p ∂_{p+1} ⋯ ∂_{p+k-1}`. -/
theorem actNat_upList (p k : ℕ) : actNat n (List.range' p k) = up n p k := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
      apply LinearMap.ext
      intro f
      rw [List.range'_succ]
      change cross n p (actNat n (List.range' (p+1) k) f) = (cross n p * up n (p+1) k) f
      rw [ih]
      rfl

end Operators

/-! ## Words in the odd nilHecke algebra -/

variable {n : ℕ}

/-- The descending word `∂_{p+k-1} ⋯ ∂_{p+1} ∂_p` (written order): one strand descending from
position `p+k` to position `p`. -/
abbrev downWord (n p k : ℕ) : Word n := natWord n (downList p k)

/-- The ascending word `∂_p ∂_{p+1} ⋯ ∂_{p+k-1}` (written order): one strand descending from
position `p` to position `p+k`. -/
abbrev upWord (n p k : ℕ) : Word n := natWord n (List.range' p k)

theorem action_downWord (p k : ℕ) (h : p + k + 1 ≤ n + 2) :
    action n (product (downWord n p k)) = down n p k := by
  rw [action_natWord n _ fun j hj => by have := mem_downList hj; omega, actNat_downList]

theorem action_upWord (p k : ℕ) (h : p + k + 1 ≤ n + 2) :
    action n (product (upWord n p k)) = up n p k := by
  rw [action_natWord n _ fun j hj => by
    have := List.mem_range'_1.mp hj; omega, actNat_upList]

/-- EKL Lemma 3.1 (3.19), crossing slide lemma, on the strands `[p, p+k+2)`.  For `p = 0`,
`k = a-2` this is, in the paper's 1-based indices,
`(∂_{a-2} ⋯ ∂_1)(∂_{a-1} ⋯ ∂_1) = (∂_{a-1} ∂_{a-2} ⋯ ∂_1)(∂_{a-1} ⋯ ∂_2)`; no sign. -/
theorem lemma_3_1 (p k : ℕ) (h : p + k + 2 ≤ n + 2) :
    product (downWord n p k) * product (downWord n p (k+1)) =
      product (downWord n p (k+1)) * product (downWord n (p+1) k) := by
  apply action_injective n
  rw [map_mul, map_mul, action_downWord p k (by omega), action_downWord p (k+1) (by omega),
    action_downWord (p+1) k (by omega), down_pair, down_last]

/-- EKL Lemma 3.2 (3.22), on the strands `[p, p+k+1)`: `D_{k+1} = (1 ⊗ D_k)(∂_p ∂_{p+1} ⋯
∂_{p+k-1})`, the leftmost strand descending to the right below `D_k`; no sign. -/
theorem lemma_3_2 (p k : ℕ) (h : p + k + 1 ≤ n + 2) :
    product (triWord n p (k+1)) = product (triWord n (p+1) k) * product (upWord n p k) := by
  apply action_injective n
  rw [map_mul, action_triWord n p (k+1) (by omega), action_triWord n (p+1) k (by omega),
    action_upWord p k (by omega), triangle_other n p k (by omega)]

/-- EKL Lemma 3.3 (3.24), `D_a` slide, on the strands `[p, p+a+1)`: the strand descending from
position `p+a` to `p` moves from below `D_a ⊗ 1` to above `1 ⊗ D_a`, with sign `(-1)^{C(a,3)}`. -/
theorem lemma_3_3 (p a : ℕ) (h : p + a + 1 ≤ n + 2) :
    product (triWord n p a) * product (downWord n p a) =
      (-1 : ℤ)^(a.choose 3) • (product (downWord n p a) * product (triWord n (p+1) a)) := by
  apply action_injective n
  rw [map_mul, map_zsmul, map_mul, action_triWord n p a (by omega),
    action_triWord n (p+1) a (by omega), action_downWord p a (by omega), triangle_down]

/-! ## 0-Hecke crossings and strands (§3.2.3) -/

theorem product_natWord_cons (j : ℕ) (l : List ℕ) (hj : j < n+1) :
    product (natWord n (j :: l)) = crossing n ⟨j, hj⟩ * product (natWord n l) := by
  simp only [natWord, List.filterMap_cons, dif_pos hj]
  rfl

theorem zeroHeckeProduct_natWord_cons (j : ℕ) (l : List ℕ) (hj : j < n+1) :
    zeroHeckeProduct (natWord n (j :: l)) =
      zeroHecke n ⟨j, hj⟩ * zeroHeckeProduct (natWord n l) := by
  simp only [natWord, List.filterMap_cons, dif_pos hj]
  rfl

theorem natWord_append (l₁ l₂ : List ℕ) : natWord n (l₁ ++ l₂) = natWord n l₁ ++ natWord n l₂ :=
  List.filterMap_append

theorem downList_succ (p k : ℕ) : downList p (k+1) = downList (p+1) k ++ [p] := by
  simp [downList, List.range'_succ]

/-- Distant crossings commute exactly with the 0-Hecke generators. -/
theorem zeroHecke_crossing_far (i j : Fin (n+1)) (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    zeroHecke n i * crossing n j = crossing n j * zeroHecke n i := by
  have hl : i.castSucc ≠ j.castSucc := by
    intro e; have := congrArg Fin.val e; simp only [Fin.coe_castSucc] at this; omega
  have hr : i.castSucc ≠ j.succ := by
    intro e; have := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at this; omega
  have hc : dot n i.castSucc * crossing n j = -(crossing n j * dot n i.castSucc) := by
    rw [crossing_dot_other j _ hl hr, neg_neg]
  rw [zeroHecke, mul_assoc, crossing_distant i j h, mul_neg, ← mul_assoc, hc, neg_mul, neg_neg,
    mul_assoc]

/-- EKL (3.28): `∂_{i+1} ∂_i ∂̄_{i+1} = ∂̄_i ∂_{i+1} ∂_i`: the 0-Hecke crossing moves from the
bottom to the top of the braid. -/
theorem eq_3_28 (i j : Fin (n+1)) (h : j.val = i.val+1) :
    crossing n j * crossing n i * zeroHecke n j = zeroHecke n i * crossing n j * crossing n i := by
  have hij : j.castSucc = i.succ := Fin.ext (by simp [h])
  have hl : i.castSucc ≠ j.castSucc := by
    intro e; have := congrArg Fin.val e; simp only [Fin.coe_castSucc] at this; omega
  have hr : i.castSucc ≠ j.succ := by
    intro e; have := congrArg Fin.val e; simp only [Fin.coe_castSucc, Fin.val_succ] at this; omega
  calc crossing n j * crossing n i * zeroHecke n j
        = crossing n j * (crossing n i * dot n i.succ) * crossing n j := by
          rw [zeroHecke, hij]; simp only [mul_assoc]
    _ = crossing n j * crossing n j - crossing n j * dot n i.castSucc * crossing n i *
          crossing n j := by
          rw [crossing_dot_right]; simp only [mul_sub, sub_mul, mul_one, mul_assoc]
    _ = dot n i.castSucc * (crossing n j * crossing n i * crossing n j) := by
          rw [crossing_square, crossing_dot_other j _ hl hr]; simp only [neg_mul, sub_neg_eq_add,
            zero_add, mul_assoc]
    _ = zeroHecke n i * crossing n j * crossing n i := by
          rw [← crossing_braid i j h, zeroHecke]; simp only [mul_assoc]

/-- EKL (3.31): `∂_i ∂̄_i = ∂_i`. -/
theorem eq_3_31 (i : Fin (n+1)) : crossing n i * zeroHecke n i = crossing n i :=
  crossing_mul_zeroHecke i

theorem zeroHecke_comm_natWord (i : Fin (n+1)) (l : List ℕ)
    (hl : ∀ j ∈ l, j < n+1 ∧ (i.val+1 < j ∨ j+1 < i.val)) :
    zeroHecke n i * product (natWord n l) = product (natWord n l) * zeroHecke n i := by
  induction l with
  | nil => simp [natWord, product]
  | cons j l ih =>
      obtain ⟨⟨hj, hf⟩, hl⟩ := List.forall_mem_cons.mp hl
      rw [product_natWord_cons j l hj, ← mul_assoc, zeroHecke_crossing_far i ⟨j, hj⟩ hf,
        mul_assoc, ih hl, mul_assoc]

/-- One 0-Hecke generator slides down through a strand descending from the right. -/
theorem zeroHecke_down (a : ℕ) : ∀ (p i : ℕ), p ≤ i → ∀ (hi : i + 2 ≤ p + a)
    (ha : p + a + 1 ≤ n + 2),
    zeroHecke n ⟨i, by omega⟩ * product (downWord n p a) =
      product (downWord n p a) * zeroHecke n ⟨i+1, by omega⟩ := by
  induction a with
  | zero => intro p i hp hi; omega
  | succ a ih =>
      intro p i hp hi ha
      rw [downWord, downList_succ, natWord_append, product_append]
      by_cases hip : i = p
      · subst hip
        obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        have e1 : product (natWord n [i+1]) = crossing n ⟨i+1, by omega⟩ := by
          rw [product_natWord_cons _ _ (by omega)]; exact mul_one _
        have e2 : product (natWord n [i]) = crossing n ⟨i, by omega⟩ := by
          rw [product_natWord_cons _ _ (by omega)]; exact mul_one _
        rw [downList_succ, natWord_append, product_append, e1, e2]
        have hc := zeroHecke_comm_natWord (n := n) ⟨i, by omega⟩ (downList (i+1+1) a)
          fun j hj => by have := mem_downList hj; simp only; omega
        calc zeroHecke n ⟨i, _⟩ * (product (natWord n (downList (i+1+1) a)) *
              crossing n ⟨i+1, _⟩ * crossing n ⟨i, _⟩)
            = (zeroHecke n ⟨i, by omega⟩ * product (natWord n (downList (i+1+1) a))) *
              crossing n ⟨i+1, by omega⟩ * crossing n ⟨i, by omega⟩ := by simp only [mul_assoc]
          _ = product (natWord n (downList (i+1+1) a)) * (zeroHecke n ⟨i, by omega⟩ *
              crossing n ⟨i+1, by omega⟩ * crossing n ⟨i, by omega⟩) := by
                rw [hc]; simp only [mul_assoc]
          _ = _ := by rw [← eq_3_28 ⟨i, by omega⟩ ⟨i+1, by omega⟩ rfl]; simp only [mul_assoc]
      · rw [← mul_assoc, ih (p+1) i (by omega) (by omega) (by omega), mul_assoc]
        have e2 : product (natWord n [p]) = crossing n ⟨p, by omega⟩ := by
          rw [product_natWord_cons _ _ (by omega)]; exact mul_one _
        rw [e2, zeroHecke_crossing_far _ _ (Or.inr (by simp only; omega)), mul_assoc]

/-- A 0-Hecke word on the strands `[p, p+a)` slides down through a strand descending from the
right, landing on `[p+1, p+a+1)`. -/
theorem zeroHeckeProduct_down (p a : ℕ) (ha : p + a + 1 ≤ n + 2) (l : List ℕ)
    (hl : ∀ j ∈ l, p ≤ j ∧ j + 2 ≤ p + a) :
    zeroHeckeProduct (natWord n l) * product (downWord n p a) =
      product (downWord n p a) * zeroHeckeProduct (natWord n (l.map (· + 1))) := by
  induction l with
  | nil => simp [natWord]
  | cons j l ih =>
      obtain ⟨hj, hl⟩ := List.forall_mem_cons.mp hl
      rw [List.map_cons, zeroHeckeProduct_natWord_cons j l (by omega),
        zeroHeckeProduct_natWord_cons (j+1) _ (by omega), mul_assoc, ih hl, ← mul_assoc,
        zeroHecke_down a p j hj.1 hj.2 ha, mul_assoc]

/-- EKL (3.29): `e_a` slides from the bottom right to the top left through a strand descending
from the right, on the strands `[p, p+a+1)`: `(∂_{p+a-1} ⋯ ∂_p) (1 ⊗ e_a) = (e_a ⊗ 1)
(∂_{p+a-1} ⋯ ∂_p)`; no sign. -/
theorem eq_3_29 (p a : ℕ) (h : p + a + 1 ≤ n + 2) :
    product (downWord n p a) * blockE n (p+1) a = blockE n p a * product (downWord n p a) := by
  rw [blockE, blockE, triWord, triWord, ← triList_map_succ,
    zeroHeckeProduct_down p a h _ fun j hj => ⟨mem_triList_ge hj, by
      have := mem_triList hj; omega⟩]

/-- Remark 3.4 (3.30): the mirror slide fails already for `a = 2` in `ONH_3`:
`(∂_0 ∂_1)(e_2 ⊗ 1) ≠ (1 ⊗ e_2)(∂_0 ∂_1)` (0-based).  This is the reflection of (3.28) in a
horizontal axis.  Evaluated on `x_1 x_2` the left side gives `-1`, the right side `0`. -/
theorem remark_3_4 :
    product (upWord 1 0 2) * blockE 1 0 2 ≠ blockE 1 1 2 * product (upWord 1 0 2) := by
  have hL : product (upWord 1 0 2) * blockE 1 0 2 =
      crossing 1 0 * crossing 1 1 * zeroHecke 1 0 := by
    rw [show upWord 1 0 2 = [0, 1] from rfl, blockE, show triWord 1 0 2 = [0] from rfl]
    simp [product, mul_assoc]
  have hR : blockE 1 1 2 * product (upWord 1 0 2) =
      zeroHecke 1 1 * crossing 1 0 * crossing 1 1 := by
    rw [show upWord 1 0 2 = [0, 1] from rfl, blockE, show triWord 1 1 2 = [1] from rfl]
    simp [product, mul_assoc]
  intro h
  rw [hL, hR] at h
  have e := congrArg (fun x => action 1 x
    (OddMath.SkewPolynomial.generator 1 * OddMath.SkewPolynomial.generator 2)) h
  simp only [zeroHecke, map_mul, Module.End.mul_apply, action_crossing_apply,
    action_dot_apply] at e
  simp [AllRankDivided.divided_mul, AllRankDivided.divided_generator, AllRankDivided.s_generator,
    Equiv.swap_apply_def, Fin.ext_iff, AllRankDivided.divided_one,
    ThickDecomposition.skew_mul_zero, ThickDecomposition.skew_zero_mul] at e

/-! ## Blocks on strand windows -/

theorem val_mem_of_mem_natWord {l : List ℕ} {i : Fin (n+1)} (hi : i ∈ natWord n l) :
    i.val ∈ l := by
  simp only [natWord, List.mem_filterMap] at hi
  obtain ⟨j, hj, hji⟩ := hi
  split_ifs at hji with hjn
  cases hji
  exact hj

theorem mem_crossList_ge {p a b j : ℕ} (h : j ∈ crossList p a b) : p ≤ j := by
  induction b generalizing p with
  | zero => simp [crossList] at h
  | succ b ih =>
      rcases List.mem_append.mp h with h | h
      · exact (mem_downList h).1
      · have := ih h; omega

theorem length_natWord (l : List ℕ) (hl : ∀ j ∈ l, j < n+1) : (natWord n l).length = l.length := by
  rw [← List.length_map (f := Fin.val), natWord_values n l hl]

theorem length_crossWord (p a b : ℕ) (h : p + a + b ≤ n+2) :
    (crossWord n p a b).length = a * b := by
  rw [length_natWord _ fun j hj => by have := mem_crossList hj; omega,
    ThickDecomposition.length_crossList]

/-- `e_k` on `[p, p+k)` has even degree in any window containing `[p, p+k)`. -/
theorem homog_blockE_in {l r p k : ℕ} (hl : l ≤ p) (hr : p + k ≤ r) :
    Homog l r (2 * (triWord n p k).length) (blockE n p k) :=
  homog_zeroHeckeProduct _ fun _ hi => by have := mem_triWord hi; omega

theorem homog_crossWord_in {l r p a b : ℕ} (hl : l ≤ p) (hr : p + a + b ≤ r) :
    Homog l r (crossWord n p a b).length (product (crossWord n p a b)) :=
  homog_product _ fun i hi => by
    have h := val_mem_of_mem_natWord hi
    have := mem_crossList h
    have := mem_crossList_ge h
    omega

theorem homog_crossWord (p a b : ℕ) (h : p + a + b ≤ n+2) :
    Homog p (p+a+b) (a*b) (product (crossWord n p a b)) :=
  homog_of_eq (homog_crossWord_in le_rfl le_rfl) (length_crossWord p a b h)

/-- Elements on disjoint windows commute when one of them is even. -/
theorem comm_of_even_left {l r l' r' k k' : ℕ} {u v : Presented n} (hu : Homog l r (2*k) u)
    (hv : Homog l' r' k' v) (h : r ≤ l') : u * v = v * u :=
  homog_comm_of_even hu hv h (Nat.even_mul.mpr (Or.inl (even_two_mul k)))

theorem comm_of_even_right {l r l' r' k k' : ℕ} {u v : Presented n} (hu : Homog l r k u)
    (hv : Homog l' r' (2*k') v) (h : r ≤ l') : u * v = v * u :=
  homog_comm_of_even hu hv h (Nat.even_mul.mpr (Or.inr (even_two_mul k')))

theorem natWord_map_shift_gen {m p : ℕ} (h : p + (m+2) ≤ n+2) (l : List ℕ)
    (hl : ∀ j ∈ l, j < m+1) : (natWord m l).map (shiftIndex h) = natWord n (l.map (· + p)) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      obtain ⟨hj, hl⟩ := List.forall_mem_cons.mp hl
      have hj' : j + p < n+1 := by omega
      change (List.filterMap _ (j :: l)).map _ = List.filterMap _ ((j + p) :: l.map (· + p))
      simp only [List.filterMap_cons, dif_pos hj, dif_pos hj', List.map_cons]
      exact congrArg₂ List.cons (Fin.ext rfl) (ih hl)

theorem windowHom_blockE_gen {m p : ℕ} (h : p + (m+2) ≤ n+2) (q k : ℕ) (hk : q + k ≤ m+2) :
    windowHom m n p h (blockE m q k) = blockE n (p+q) k := by
  rw [blockE, ThickBubble.windowHom_zeroHeckeProduct, blockE, triWord, triWord,
    natWord_map_shift_gen h _ fun j hj => by have := mem_triList hj; omega]
  congr 2
  rw [triList, triList, List.map_map]
  congr 1
  funext i
  simp only [Function.comp_apply]
  omega

theorem zeroHeckeProduct_mul_projector {m : ℕ} (w : Word m) :
    zeroHeckeProduct w * projector m = projector m := by
  induction w with
  | nil => exact one_mul _
  | cons i w ih => rw [zeroHeckeProduct_cons, mul_assoc, ih, zeroHecke_mul_projector]

/-- EKL (3.40) and Prop 3.6 on nested windows `[q, q+k) ⊂ [p, p+K)`: `e_k e_K = e_K = e_K e_k`. -/
theorem blockE_absorb {p K q k : ℕ} (hq : p ≤ q) (hk : q + k ≤ p + K) (hK : p + K ≤ n+2) :
    blockE n q k * blockE n p K = blockE n p K ∧ blockE n p K * blockE n q k = blockE n p K := by
  match K, hk, hK with
  | 0, hk, _ =>
      obtain rfl : k = 0 := by omega
      exact ⟨one_mul _, mul_one _⟩
  | 1, hk, _ =>
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> exact ⟨one_mul _, mul_one _⟩
  | m+2, hk, hK =>
      have hw := windowHom_blockE_gen hK (q-p) k (by omega)
      rw [show p + (q-p) = q by omega] at hw
      rw [blockE_eq hK, ← hw, ← map_mul, ← map_mul, blockE, zeroHeckeProduct_mul_projector,
        projector_mul_zeroHeckeProduct]
      exact ⟨rfl, rfl⟩

/-- Prop 3.5 on the strands `[p, p+k)`: `e_k = (-1)^{C(k,3)} x^{δ_k} D_k`. -/
theorem blockE_eq_stair (p k : ℕ) (h : p + k ≤ n+2) :
    blockE n p k = (-1 : ℤ)^(k.choose 3) •
      (blockMono n p k h (fun i => k-1-i.val) * blockD n p k) := by
  match k, h with
  | 0, h => simp [blockE_zero, blockD_zero, blockMono]
  | 1, h => rw [show Nat.choose 1 3 = 0 from rfl]; simp [blockE_one, blockD_one, blockMono]
  | m+2, h =>
      have hA : (fun i : Fin (m+2) => m+2-1-i.val) = fun i => m+1-i.val := by
        funext i; omega
      rw [hA, blockE_eq h, blockD_eq h, ← blockMono_eq h, prop_3_5, map_zsmul, map_mul,
        staircaseElem]

/-- EKL Prop 3.7 (3.45) on the strands `[p, p+a+b)`: `(D_a ⊗ D_b) X_{a,b} = D_{a+b}`. -/
theorem blockD_crossing (p a b : ℕ) (h : p + a + b ≤ n+2) :
    blockD n p a * blockD n (p+a) b * product (crossWord n p a b) = blockD n p (a+b) := by
  apply action_injective n
  rw [map_mul, map_mul, blockD, blockD, blockD, action_triWord n p a (by omega),
    action_triWord n (p+a) b (by omega), action_crossWord n p a b h,
    action_triWord n p (a+b) (by omega), triangle_crossing]

/-- EKL (3.42), first identity, on the strands `[p, p+a+b+c)`. -/
theorem crossWord_add (p a b c : ℕ) (h : p + a + (b+c) ≤ n+2) :
    product (crossWord n p a (b+c)) =
      product (crossWord n p a b) * product (crossWord n (p+b) a c) := by
  apply action_injective n
  rw [map_mul, action_crossWord n p a (b+c) h, action_crossWord n p a b (by omega),
    action_crossWord n (p+b) a c (by omega), crossAt_add]

/-- EKL (3.42), second identity, on the strands `[p, p+a+b+c)`, with sign `(-1)^{ab C(c,2)}`. -/
theorem crossWord_split (p a b c : ℕ) (h : p + (a+b) + c ≤ n+2) :
    product (crossWord n p (a+b) c) = (-1 : ℤ)^(a*b*c.choose 2) •
      (product (crossWord n (p+a) b c) * product (crossWord n p a c)) := by
  apply action_injective n
  rw [map_zsmul, map_mul, action_crossWord n p (a+b) c h, action_crossWord n (p+a) b c (by omega),
    action_crossWord n p a c (by omega), crossAt_split]

/-! ## Splitters, mergers and thick crossings (§4.1.1) -/

/-- EKL (4.1), left, on the strands `[p, p+a+b)`: the splitter `(e_a ⊗ e_b) X_{a,b}` of a thick
`a+b` strand into `a` (left) and `b` (right). -/
def splitAt (n p a b : ℕ) : Presented n :=
  blockE n p a * blockE n (p+a) b * product (crossWord n p a b)

/-- EKL (4.1), right, on the strands `[p, p+a+b)`: the merger `e_{a+b}` of `a` and `b`. -/
def mergeAt (n p a b : ℕ) : Presented n := blockE n p (a+b)

/-- EKL (4.2): the thick crossing with `a` at the bottom left and `b` at the bottom right,
defined as the merger into `a+b` followed by the splitter into `b` (left) and `a` (right). -/
def thickCross (n p a b : ℕ) : Presented n := splitAt n p b a * mergeAt n p a b

theorem splitAt_def (p a b : ℕ) :
    splitAt n p a b = blockE n p a * blockE n (p+a) b * product (crossWord n p a b) := rfl

theorem splitAt_zero (a b : ℕ) : splitAt n 0 a b = splitter n a b := by
  rw [splitAt, splitter, Nat.zero_add]

section Abstract
variable {R : Type*} [Ring R]

theorem split_abstract {Ma Mb Da Db X : R} {sa sb σ : ℤ} (hc : Da * Mb = σ • (Mb * Da)) :
    (sa • (Ma * Da)) * (sb • (Mb * Db)) * X = (sa * sb * σ) • (Ma * Mb * (Da * Db * X)) :=
  calc (sa • (Ma * Da)) * (sb • (Mb * Db)) * X = (sa * sb) • (Ma * ((Da * Mb) * (Db * X))) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
        congr 1; ring
    _ = _ := by
        rw [hc]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]

theorem triple_abstract {Ma Mb Mc Da Db Dc : R} {sa sb sc s1 s2 s3 : ℤ}
    (h1 : Da * Mb = s1 • (Mb * Da)) (h2 : Da * Mc = s2 • (Mc * Da))
    (h3 : Db * Mc = s3 • (Mc * Db)) :
    (sa • (Ma * Da)) * (sb • (Mb * Db)) * (sc • (Mc * Dc)) =
      (sa * sb * sc * s1 * s3 * s2) • (Ma * Mb * Mc * (Da * Db * Dc)) :=
  calc (sa • (Ma * Da)) * (sb • (Mb * Db)) * (sc • (Mc * Dc))
        = (sa * sb * sc) • (Ma * ((Da * Mb) * (Db * Mc) * Dc)) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
        congr 1; ring
    _ = (sa * sb * sc * s1 * s3) • (Ma * (Mb * ((Da * Mc) * Db) * Dc)) := by
        rw [h1, h3]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
        congr 1; ring
    _ = _ := by
        rw [h2]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]

end Abstract

/-- The splitter is a multiple of `D_{a+b}` on the right. -/
theorem splitAt_eq_D (p a b : ℕ) (h : p + a + b ≤ n+2) :
    ∃ (c : ℤ) (M : Presented n), splitAt n p a b = c • (M * blockD n p (a+b)) := by
  have hL : p + a ≤ n+2 := by omega
  have hR : p + a + b ≤ n+2 := h
  rw [splitAt, blockE_eq_stair p a hL, blockE_eq_stair (p+a) b hR,
    split_abstract (homog_supercomm_zsmul (homog_blockD hL) (homog_blockMono hR _) le_rfl),
    mul_assoc (blockD n p a), ← mul_assoc (blockD n p a), blockD_crossing p a b h]
  exact ⟨_, _, rfl⟩

/-- EKL (3.44) on the strands `[p, p+a+b)`: `(e_a ⊗ e_b) X_{a,b} e_{a+b} = (e_a ⊗ e_b) X_{a,b}`. -/
theorem eq_3_44 (p a b : ℕ) (h : p + a + b ≤ n+2) :
    splitAt n p a b * blockE n p (a+b) = splitAt n p a b := by
  obtain ⟨c, M, hS⟩ := splitAt_eq_D p a b h
  rw [hS, smul_mul_assoc, mul_assoc, blockD_mul_blockE (by omega)]

/-- A splitter absorbs every block projector inside its window. -/
theorem splitAt_mul_blockE {p a b q k : ℕ} (hq : p ≤ q) (hk : q + k ≤ p + (a+b))
    (h : p + a + b ≤ n+2) : splitAt n p a b * blockE n q k = splitAt n p a b := by
  rw [← eq_3_44 p a b h, mul_assoc, (blockE_absorb hq hk (by omega)).2]

/-- EKL (4.2): the thick crossing equals the splitter, by (3.44). -/
theorem eq_4_2 (p a b : ℕ) (h : p + a + b ≤ n+2) : thickCross n p a b = splitAt n p b a := by
  rw [thickCross, mergeAt, Nat.add_comm a b, eq_3_44 p b a (by omega)]

/-- EKL (3.40) on the strands `[p, p+a+b+c)`:
`e_{a+b+c} = (1 ⊗ e_b ⊗ 1) e_{a+b+c} = e_{a+b+c} (1 ⊗ e_b ⊗ 1)`. -/
theorem eq_3_40 (p a b c : ℕ) (h : p + (a+b+c) ≤ n+2) :
    blockE n (p+a) b * blockE n p (a+b+c) = blockE n p (a+b+c) ∧
      blockE n p (a+b+c) * blockE n (p+a) b = blockE n p (a+b+c) :=
  blockE_absorb (by omega) (by omega) h

/-- EKL (3.43): the heights of `e_a` and `e_b` above the crossing `X_{a,b}` are irrelevant. -/
theorem eq_3_43 (p a b : ℕ) :
    blockE n (p+a) b * blockE n p a * product (crossWord n p a b) = splitAt n p a b := by
  rw [splitAt, comm_of_even_left (homog_blockE_in (n := n) (p := p) (k := a) le_rfl le_rfl)
    (homog_blockE_in (n := n) (p := p+a) (k := b) le_rfl le_rfl) le_rfl]

/-- EKL (3.44) in `ONH_{a+b}`, with the splitter of (4.1). -/
theorem eq_3_44_full {a b : ℕ} (hab : a + b = n+2) :
    splitter n a b * projector n = splitter n a b := by
  have h := eq_3_44 (n := n) 0 a b (by omega)
  rwa [splitAt_zero, hab, ThickMatrixUnits.blockE_n] at h

theorem neg_one_pow_swap {M : Type*} [AddCommGroup M] {x y : M} (e : ℕ)
    (h : x = (-1 : ℤ)^e • y) : y = (-1 : ℤ)^e • x := by
  rw [h, neg_one_smul_smul]

theorem homog_splitAt (p a b : ℕ) :
    ∃ d, Homog p (p+a+b) d (splitAt n p a b) :=
  ⟨_, ((homog_blockE_in (n := n) (p := p) (k := a) le_rfl (by omega)).mul
    (homog_blockE_in (n := n) (p := p+a) (k := b) (by omega) le_rfl)).mul
    (homog_crossWord_in le_rfl le_rfl)⟩

/-- `e_a ⊗ e_b ⊗ e_c` is a multiple of `D_a ⊗ D_b ⊗ D_c` on the right. -/
theorem blockE_triple (p a b c : ℕ) (h : p + a + b + c ≤ n+2) :
    ∃ (c₀ : ℤ) (M : Presented n), blockE n p a * blockE n (p+a) b * blockE n (p+a+b) c =
      c₀ • (M * (blockD n p a * blockD n (p+a) b * blockD n (p+a+b) c)) := by
  have h1 : p + a ≤ n+2 := by omega
  have h2 : p + a + b ≤ n+2 := by omega
  rw [blockE_eq_stair p a h1, blockE_eq_stair (p+a) b h2, blockE_eq_stair (p+a+b) c h,
    triple_abstract (homog_supercomm_zsmul (homog_blockD h1) (homog_blockMono h2 _) le_rfl)
      (homog_supercomm_zsmul (homog_blockD h1) (homog_blockMono h _) (by omega))
      (homog_supercomm_zsmul (homog_blockD h2) (homog_blockMono h _) le_rfl)]
  exact ⟨_, _, rfl⟩

/-- EKL Prop 4.1 (4.3), associativity of splitters, on the strands `[p, p+a+b+c)`:
`(S_{a,b} ⊗ 1_c) S_{a+b,c} = (-1)^{ab C(c,2)} (1_a ⊗ S_{b,c}) S_{a,b+c}`. -/
theorem prop_4_1_split (p a b c : ℕ) (h : p + a + b + c ≤ n+2) :
    splitAt n p a b * splitAt n p (a+b) c =
      (-1 : ℤ)^(a*b*c.choose 2) • (splitAt n (p+a) b c * splitAt n p a (b+c)) := by
  have h2 : p + a + b ≤ n+2 := by omega
  have eL : splitAt n p a b * splitAt n p (a+b) c = blockE n p a * blockE n (p+a) b *
      blockE n (p+a+b) c * (product (crossWord n p a b) * product (crossWord n p (a+b) c)) :=
    calc splitAt n p a b * splitAt n p (a+b) c
        = splitAt n p a b * blockE n p (a+b) * blockE n (p+a+b) c *
            product (crossWord n p (a+b) c) := by
          rw [splitAt_def p (a+b) c, show p + (a+b) = p+a+b by omega]
          simp only [mul_assoc]
      _ = blockE n p a * blockE n (p+a) b * (product (crossWord n p a b) *
            blockE n (p+a+b) c) * product (crossWord n p (a+b) c) := by
          rw [eq_3_44 p a b h2, splitAt]; simp only [mul_assoc]
      _ = _ := by
          rw [comm_of_even_right (homog_crossWord_in (n := n) (l := p) (r := p+a+b) le_rfl le_rfl)
            (homog_blockE_in (n := n) (p := p+a+b) (k := c) le_rfl le_rfl) le_rfl]
          simp only [mul_assoc]
  have eR : splitAt n (p+a) b c * splitAt n p a (b+c) = blockE n p a * blockE n (p+a) b *
      blockE n (p+a+b) c * (product (crossWord n (p+a) b c) * product (crossWord n p a (b+c))) := by
    obtain ⟨d, hS⟩ := homog_splitAt (n := n) (p+a) b c
    calc splitAt n (p+a) b c * splitAt n p a (b+c)
        = (splitAt n (p+a) b c * blockE n p a) * blockE n (p+a) (b+c) *
            product (crossWord n p a (b+c)) := by rw [splitAt_def p a (b+c)]; simp only [mul_assoc]
      _ = blockE n p a * (splitAt n (p+a) b c * blockE n (p+a) (b+c)) *
            product (crossWord n p a (b+c)) := by
          rw [← comm_of_even_left (homog_blockE_in (n := n) (p := p) (k := a) le_rfl le_rfl) hS
            le_rfl]
          simp only [mul_assoc]
      _ = _ := by
          rw [eq_3_44 (p+a) b c (by omega), splitAt]; simp only [mul_assoc]
  obtain ⟨c₀, M, hE⟩ := blockE_triple (n := n) p a b c h
  have hsw := neg_one_pow_swap _ (homog_supercomm_zsmul (homog_crossWord (n := n) p a b h2)
    (homog_blockD (p := p+a+b) (k := c) h) le_rfl)
  have dL : blockD n p a * blockD n (p+a) b * blockD n (p+a+b) c *
      (product (crossWord n p a b) * product (crossWord n p (a+b) c)) =
      (-1 : ℤ)^(a*b*c.choose 2) • blockD n p (a+b+c) := by
    have e := blockD_crossing (n := n) p (a+b) c (by omega)
    rw [show p + (a+b) = p+a+b by omega] at e
    rw [mul_assoc (blockD n p a * blockD n (p+a) b), ← mul_assoc (blockD n (p+a+b) c), hsw,
      smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc, blockD_crossing p a b h2, mul_assoc,
      e]
  have dR : blockD n p a * blockD n (p+a) b * blockD n (p+a+b) c *
      (product (crossWord n (p+a) b c) * product (crossWord n p a (b+c))) =
      blockD n p (a+b+c) := by
    have e := blockD_crossing (n := n) p a (b+c) (by omega)
    rw [show a + (b+c) = a+b+c by omega] at e
    rw [← e, ← blockD_crossing (n := n) (p+a) b c (by omega)]
    simp only [mul_assoc]
  rw [eL, eR, hE, smul_mul_assoc, smul_mul_assoc, mul_assoc M, mul_assoc M, dL, dR,
    mul_smul_comm, smul_comm]

/-- EKL Prop 4.1 (4.4), associativity of mergers, on the strands `[p, p+a+b+c)`. -/
theorem prop_4_1_merge (p a b c : ℕ) (h : p + (a+b+c) ≤ n+2) :
    blockE n p (a+b+c) * blockE n p (a+b) = blockE n p (a+b+c) * blockE n (p+a) (b+c) := by
  rw [(blockE_absorb le_rfl (by omega) h).2, (blockE_absorb (by omega) (by omega) h).2]

/-- EKL Prop 4.2 (4.5), on the strands `[p, p+a+b+c)`: a thick strand `a` crossing over the
left leg `c` of a bubble. -/
theorem prop_4_2_left (p a b c : ℕ) (h : p + a + b + c ≤ n+2) :
    blockE n (p+a) (b+c) * thickCross n p c a * splitAt n (p+c) a b =
      splitAt n p a (b+c) * blockE n p (a+b+c) := by
  have hac : p + a + c ≤ n+2 := by omega
  rw [eq_4_2 p c a (by omega), show a+b+c = a+(b+c) by omega, eq_3_44 p a (b+c) (by omega)]
  -- absorb the lower `e_a`
  have e1 : splitAt n p a c * splitAt n (p+c) a b =
      splitAt n p a c * blockE n (p+c+a) b * product (crossWord n (p+c) a b) := by
    rw [splitAt_def (p+c) a b, ← mul_assoc, ← mul_assoc,
      splitAt_mul_blockE (by omega) (by omega) hac]
  rw [mul_assoc, e1, splitAt_def p a c, show p + c + a = p + a + c by omega]
  have hX := comm_of_even_right (homog_crossWord_in (n := n) (l := p) (r := p+a+c) (p := p)
    (a := a) (b := c) le_rfl le_rfl) (homog_blockE_in (n := n) (p := p+a+c) (k := b) le_rfl le_rfl)
    le_rfl
  have hA := comm_of_even_left (homog_blockE_in (n := n) (p := p) (k := a) le_rfl le_rfl)
    (homog_blockE_in (n := n) (l := p+a) (r := p+a+(b+c)) (p := p+a) (k := b+c) le_rfl le_rfl)
    le_rfl
  calc blockE n (p+a) (b+c) * (blockE n p a * blockE n (p+a) c * product (crossWord n p a c) *
        blockE n (p+a+c) b * product (crossWord n (p+c) a b))
      = blockE n p a * (blockE n (p+a) (b+c) * blockE n (p+a) c) *
          (product (crossWord n p a c) * blockE n (p+a+c) b) *
          product (crossWord n (p+c) a b) := by
        simp only [mul_assoc]
        rw [← mul_assoc (blockE n (p+a) (b+c)) (blockE n p a), ← hA]
        simp only [mul_assoc]
    _ = blockE n p a * (blockE n (p+a) (b+c) * blockE n (p+a+c) b) *
          (product (crossWord n p a c) * product (crossWord n (p+c) a b)) := by
        rw [(blockE_absorb le_rfl (by omega) (by omega)).2, hX]; simp only [mul_assoc]
    _ = _ := by
        rw [(blockE_absorb (by omega) (by omega) (by omega)).2, splitAt, Nat.add_comm b c,
          crossWord_add p a c b (by omega)]

/-- EKL Prop 4.2 (4.6), on the strands `[p, p+a+b+c)`: a thick strand `c` crossing over the
right leg `a` of a bubble, with sign `(-1)^{C(a,2) bc}`. -/
theorem prop_4_2_right (p a b c : ℕ) (h : p + a + b + c ≤ n+2) :
    blockE n p (b+c) * thickCross n (p+b) a c * splitAt n p b a =
      (-1 : ℤ)^(a.choose 2 * b * c) • (splitAt n p (b+c) a * blockE n p (a+b+c)) := by
  obtain ⟨d, hS⟩ := homog_splitAt (n := n) (p+b) c a
  have hB := comm_of_even_left (homog_blockE_in (n := n) (p := p) (k := b) le_rfl le_rfl) hS le_rfl
  have eL : blockE n p (b+c) * splitAt n (p+b) c a * splitAt n p b a =
      blockE n p (b+c) * blockE n (p+b+c) a *
        (product (crossWord n (p+b) c a) * product (crossWord n p b a)) :=
    calc blockE n p (b+c) * splitAt n (p+b) c a * splitAt n p b a
        = blockE n p (b+c) * (splitAt n (p+b) c a * blockE n p b) * blockE n (p+b) a *
            product (crossWord n p b a) := by rw [splitAt_def p b a]; simp only [mul_assoc]
      _ = blockE n p (b+c) * blockE n p b * (splitAt n (p+b) c a * blockE n (p+b) a) *
            product (crossWord n p b a) := by rw [← hB]; simp only [mul_assoc]
      _ = blockE n p (b+c) * blockE n (p+b) c * blockE n (p+b+c) a *
            (product (crossWord n (p+b) c a) * product (crossWord n p b a)) := by
          rw [(blockE_absorb le_rfl (by omega) (by omega)).2,
            splitAt_mul_blockE (by omega) (by omega) (by omega), splitAt_def (p+b) c a]
          simp only [mul_assoc]
      _ = _ := by rw [(blockE_absorb (by omega) (by omega) (by omega)).2]
  rw [eq_4_2 (p+b) a c (by omega), eL, show a+b+c = (b+c)+a by omega,
    eq_3_44 p (b+c) a (by omega), splitAt_def, crossWord_split p b c a (by omega),
    show p + (b+c) = p+b+c by omega, mul_smul_comm, smul_smul, ← pow_add,
    show a.choose 2 * b * c + b * c * a.choose 2 = 2 * (a.choose 2 * b * c) by ring, pow_mul,
    neg_one_sq, one_pow, one_smul]

/-! ## Explosions (§4.2) -/

/-- EKL (4.13) on the strands `[p, p+a+b)`, with the exploders (4.12) `D_a`, `D_b`:
`D_{a+b} = (D_a ⊗ D_b) S_{a,b} = (-1)^{C(a,2) C(b,2)} (1 ⊗ D_b)(D_a ⊗ 1) S_{a,b}`. -/
theorem eq_4_13 (p a b : ℕ) (h : p + a + b ≤ n+2) :
    blockD n p (a+b) = blockD n p a * blockD n (p+a) b * splitAt n p a b ∧
      blockD n p (a+b) = (-1 : ℤ)^(a.choose 2 * b.choose 2) •
        (blockD n (p+a) b * blockD n p a * splitAt n p a b) := by
  have hL : p + a ≤ n+2 := by omega
  have hc := comm_of_even_left (homog_blockE_in (n := n) (p := p) (k := a) le_rfl le_rfl)
    (homog_blockD (n := n) (p := p+a) (k := b) h) le_rfl
  have h1 : blockD n p (a+b) = blockD n p a * blockD n (p+a) b * splitAt n p a b :=
    calc blockD n p (a+b) = (blockD n p a * blockE n p a) * (blockD n (p+a) b * blockE n (p+a) b) *
          product (crossWord n p a b) := by
          rw [blockD_mul_blockE hL, blockD_mul_blockE h, blockD_crossing p a b h]
      _ = _ := by
          rw [splitAt_def]
          simp only [mul_assoc]
          rw [← mul_assoc (blockE n p a) (blockD n (p+a) b), hc, mul_assoc]
  refine ⟨h1, ?_⟩
  rw [h1, homog_supercomm_zsmul (homog_blockD (n := n) hL) (homog_blockD (n := n) (p := p+a) h)
    le_rfl, smul_mul_assoc]

/-- EKL (4.14), one step, on the strands `[p, p+k+1)`: exploding `k+1` strands equals splitting
off the last (resp. first) strand and exploding the remaining `k`. -/
theorem eq_4_14 (p k : ℕ) (h : p + k + 1 ≤ n+2) :
    blockD n p (k+1) = blockD n p k * splitAt n p k 1 ∧
      blockD n p (1+k) = blockD n (p+1) k * splitAt n p 1 k := by
  constructor
  · have := (eq_4_13 (n := n) p k 1 h).1
    rwa [blockD_one, mul_one] at this
  · have := (eq_4_13 (n := n) p 1 k (by omega)).1
    rwa [blockD_one, one_mul] at this

/-- EKL (4.15) on the strands `[p, p+a+b)`: merging exploded strands into `a` and `b` and then
into `a+b` is the exploder `e_{a+b}`, independently of heights. -/
theorem eq_4_15 (p a b : ℕ) (h : p + (a+b) ≤ n+2) :
    blockE n p (a+b) * (blockE n p a * blockE n (p+a) b) = blockE n p (a+b) ∧
      blockE n p (a+b) * (blockE n (p+a) b * blockE n p a) = blockE n p (a+b) := by
  have hA := (blockE_absorb (n := n) (q := p) (k := a) le_rfl (by omega) h).2
  have hB := (blockE_absorb (n := n) (q := p+a) (k := b) (by omega) (by omega) h).2
  exact ⟨by rw [← mul_assoc, hA, hB], by rw [← mul_assoc, hB, hA]⟩

/-- EKL (4.16) on the strands `[p, p+K)`: any sequence of mergers inside `[p, p+K)` below
`e_K` is absorbed. -/
theorem eq_4_16 (p K : ℕ) (hK : p + K ≤ n+2) (L : List (ℕ × ℕ))
    (hL : ∀ w ∈ L, p ≤ w.1 ∧ w.1 + w.2 ≤ p + K) :
    blockE n p K * (L.map fun w => blockE n w.1 w.2).prod = blockE n p K := by
  induction L with
  | nil => exact mul_one _
  | cons w L ih =>
      obtain ⟨hw, hL⟩ := List.forall_mem_cons.mp hL
      rw [List.map_cons, List.prod_cons, ← mul_assoc, (blockE_absorb hw.1 hw.2 hK).2, ih hL]

/-- EKL (4.23) on the strands `[p, p+k)`: `e_k s_α e_k = (-1)^{χ^k_α} e_k x^{α+δ_k} D_k`, the
exploded bubble with `α'_j = α_j + k - j` dots on its `j`-th strand. -/
theorem eq_4_23 {p k : ℕ} (h : p + k ≤ n+2) (α : Fin k → ℕ) :
    blockE n p k * blockSchur n p k h α * blockE n p k =
      (-1 : ℤ)^(blockChi k α) • (blockE n p k * blockMono n p k h (BoxComplement.expA α) *
        blockD n p k) :=
  blockE_schur_blockE h α

/-- EKL (4.46) on the strands `[0, ν+1)`: a thick `ν+1` strand split into `ν` and a thin strand
carrying `x` dots and merged again vanishes for `x < ν`. -/
theorem eq_4_46 {ν x : ℕ} (hν : 1 ≤ ν) (h : ν + 1 ≤ n+2) (hx : x < ν) :
    blockE n 0 (ν+1) * ThickMatrixUnits.dotAt n ν ^ x * ThickMatrixUnits.splitOne n ν = 0 := by
  have h0 : 0 + ν ≤ n+2 := by omega
  have H := ThickMatrixUnits.prop_4_11_one (n := n) hν h (ThickMatrixUnits.col_antitone ν 0)
    (ThickMatrixUnits.col_le ν 0) hx.le
  have hS : blockSchur n 0 ν h0 (ThickMatrixUnits.col ν 0) = 1 := by
    have e := ThickMatrixUnits.epsWin_eq (n := n) hν h0 (Nat.zero_le ν)
    rw [ThickMatrixUnits.epsWin, dif_pos h0, FiniteCompleteElementary.elementaryPoly_zero,
      map_one, map_one, Nat.choose_zero_succ, pow_zero, one_smul] at e
    exact e.symm
  rw [ThickMatrixUnits.hat_col, if_neg (fun e => by have := congrFun e 0; simp only at this; omega),
    zero_smul, hS, mul_one, blockE_mul_blockE h0,
    (blockE_absorb (n := n) (q := 0) (k := ν) le_rfl (by omega) (by omega)).2] at H
  exact H

/-- EKL Remark 4.12, second half (`a = b = 2`, `α = β = (2,0)`, 0-based variables):
`D_4(x_0^3 x_3^3) = 0`, by Lemma 4.9 since `β̂ = (1,1) ≠ α`. -/
theorem remark_4_12_zero :
    D 4 (OddMath.SkewPolynomial.monomial ![3, 0, 0, 3] 1) = 0 := by
  have hα : Antitone (![2, 0] : Fin 2 → ℕ) := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have h := StaircaseEvaluation.lemma_4_9 (a := 2) (b := 2) hα (by intro k; fin_cases k <;> simp)
    hα (by intro k; fin_cases k <;> simp)
  have hne : (![2, 0] : Fin 2 → ℕ) ≠ BoxComplement.hat 2 ![2, 0] := by
    intro e
    have := congrFun e 0
    revert this
    decide
  rw [if_neg hne, zero_smul] at h
  have hx : StaircaseEvaluation.exps (![2, 0] : Fin 2 → ℕ) ![2, 0] = ![3, 0, 0, 3] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at h
  exact h

open AllRankDivided in
/-- EKL Remark 4.12, first half (0-based variables): `D_4(x_0^3 x_2^3) = -2`.  Factor
`D_4 = ± L ∂_1`, apply the Shuffle Lemma 4.4 to `∂_1(x_2^3)` and `∂_1(x_1 x_2^2)`, and evaluate
`D_4(x_0^3 x_1^3) = 0`, `D_4(x_0^3 x_1^2 x_2) = D_4(x^{δ_4}) = 1`. -/
theorem remark_4_12_value : D 4 (monomial ![3, 0, 3, 0] 1) = (-2 : ℤ) • 1 := by
  obtain ⟨L, ε, -, hD⟩ := LongestFactor.D_factor_first 2 (1 : Fin 3)
  obtain ⟨L', ε', -, hD'⟩ := LongestFactor.D_factor_first 2 (2 : Fin 3)
  let T : SkewPolynomial 4 →+ SkewPolynomial 4 :=
    AddMonoidHom.mk' (fun g => s (1 : Fin 3) (monomial ![3, 0, 0, 0] 1) * (g * monomial 0 1))
      (fun a b => by
        simp only
        rw [ThickDecomposition.skew_add_mul, ThickDecomposition.skew_mul_add])
  have hγ : ∀ (γ : Fin 4 → ℕ) (p q : ℕ), γ 0 = 3 → γ 3 = 0 → γ 1 = p → γ 2 = q →
      divided (1 : Fin 3) (monomial γ 1) =
        T (divided (1 : Fin 3) (generator 1 ^ p * generator 2 ^ q)) := by
    intro γ p q h0 h3 hp hq
    rw [ShuffleLemma.divided_monomial_eq, show (1 : Fin 3).castSucc = 1 from rfl,
      show (1 : Fin 3).succ = 2 from rfl, hp, hq]
    have hl : ShuffleLemma.lowPart (1 : Fin 3) γ = ![3, 0, 0, 0] := by
      funext j; fin_cases j <;> simp [ShuffleLemma.lowPart, h0]
    have hh : ShuffleLemma.highPart (1 : Fin 3) γ = 0 := by
      funext j; fin_cases j <;> simp [ShuffleLemma.highPart, h3]
    rw [hl, hh]
    rfl
  have h1 := ShuffleLemma.shuffle_odd (1 : Fin 3) 0 3 ⟨1, rfl⟩ le_rfl
  have h2 := ShuffleLemma.shuffle_one (1 : Fin 3) 1
  norm_num at h1 h2
  have e1 := hγ ![3, 0, 3, 0] 0 3 rfl rfl rfl rfl
  have e2 := hγ ![3, 3, 0, 0] 3 0 rfl rfl rfl rfl
  have e3 := hγ ![3, 2, 1, 0] 2 1 rfl rfl rfl rfl
  norm_num at e1 e2 e3
  have hdiv : divided (1 : Fin 3) (monomial ![3, 0, 3, 0] 1) =
      divided (1 : Fin 3) (monomial ![3, 3, 0, 0] 1) -
        (2 : ℤ) • divided (1 : Fin 3) (monomial ![3, 2, 1, 0] 1) := by
    rw [e1, h1, h2, e2, e3, map_add, map_sub, map_neg]
    abel
  have hD1 : ∀ f : SkewPolynomial 4, D 4 f = ε • L (divided (1 : Fin 3) f) := fun f =>
    LinearMap.congr_fun hD f
  have hD2 : ∀ f : SkewPolynomial 4, D 4 f = ε' • L' (divided (2 : Fin 3) f) := fun f =>
    LinearMap.congr_fun hD' f
  have hz : D 4 (monomial ![3, 3, 0, 0] 1) = 0 := by
    rw [hD2, ShuffleLemma.divided_monomial_spectator (2 : Fin 3) 6 _ rfl rfl rfl, map_zero,
      smul_zero]
  have hst : D 4 (monomial ![3, 2, 1, 0] 1) = 1 := by
    have e : (monomial ![3, 2, 1, 0] 1 : SkewPolynomial 4) = staircase 4 := by
      rw [staircase]; congr 1; funext j; fin_cases j <;> rfl
    rw [e, D_staircase]
    norm_num
  rw [hD1, hdiv, map_sub, map_zsmul, smul_sub, smul_comm ε (2 : ℤ), ← hD1, ← hD1, hz, hst]
  norm_num

/-- EKL Remark 4.12 (`a = b = 2`, `α = β = (2,0)`, 0-based variables): the ordering of the
variables matters, `D_4(x_0^3 x_2^3) ≠ 0` while `D_4(x_0^3 x_3^3) = 0`. -/
theorem remark_4_12 :
    D 4 (monomial ![3, 0, 3, 0] 1) ≠ 0 ∧ D 4 (monomial ![3, 0, 0, 3] 1) = 0 := by
  refine ⟨fun h => ?_, remark_4_12_zero⟩
  have e := congrArg (fun f : SkewPolynomial 4 => f 0) (remark_4_12_value.symm.trans h)
  simp only [StaircaseValley.smul_one_apply_zero] at e
  norm_num at e

/-! ## Sliding `ε_k` through a merger: (4.42) -/

section Elementary
open ThickMatrixUnits

theorem place_prefix {ν : ℕ} (h₀ : 0 + ν ≤ n+2) (h₁ : 0 + (ν+1) ≤ n+2) (f : SkewPolynomial ν) :
    ProjectorRank.place 0 h₁ (ElementaryBranching.prefix ν f) = ProjectorRank.place 0 h₀ f := by
  obtain ⟨x, rfl⟩ := (PbwEquivalence.presentedEquiv ν).surjective f
  have key : ((ProjectorRank.place 0 h₁).comp (ElementaryBranching.prefix ν)).comp
      (PbwEquivalence.presentedEquiv ν).toRingHom =
      (ProjectorRank.place 0 h₀).comp (PbwEquivalence.presentedEquiv ν).toRingHom := by
    apply SignedPermutation.presentedHom_ext
    intro j
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, PbwEquivalence.presentedEquiv_apply]
    rw [OddMath.PbwL3.Phi_q, ElementaryBranching.prefix_generator, ProjectorRank.place_generator,
      ProjectorRank.place_generator]
    rfl
  exact congrArg (fun φ => φ x) key

/-- EKL (4.9) on the strands `[0, μ)`: `e_μ ε_k e_μ = e_μ ε_k`. -/
theorem thickElem_eq_left (μ k : ℕ) (h : 0 + μ ≤ n+2) :
    thickElem n μ k = blockE n 0 μ * epsWin n μ k := by
  match μ, h with
  | 0, h => rw [thickElem, blockE_zero, mul_one]
  | 1, h => rw [thickElem, blockE_one, mul_one]
  | m+2, h =>
      rw [thickElem, epsWin, dif_pos h, ← windowHom_polyElem h, blockE_eq h, ← map_mul, ← map_mul,
        ThickDots.projector_poly_projector_eq _ (OddSymmetricKernel.elementary_mem m k)]

/-- The odd elementary polynomials split off the last strand (EKL (2.23)), inside `ONH`:
`ε_{k+1}(x_0, …, x_ν) = ε_{k+1}(x_0, …, x_{ν-1}) + (-1)^ν ε_k(x_0, …, x_{ν-1}) x_ν`. -/
theorem epsWin_succ (ν k : ℕ) (h : ν + 1 ≤ n+2) :
    epsWin n (ν+1) (k+1) = epsWin n ν (k+1) + (-1 : ℤ)^ν • (epsWin n ν k * dotAt n ν) := by
  have h₀ : 0 + ν ≤ n+2 := by omega
  have h₁ : 0 + (ν+1) ≤ n+2 := by omega
  rw [epsWin, dif_pos h₁, epsWin, dif_pos h₀, epsWin, dif_pos h₀, dotAt, dif_pos (by omega),
    ElementaryBranching.elementary_succ, map_add, map_add, map_mul, map_mul, place_prefix h₀ h₁,
    place_prefix h₀ h₁, ElementaryBranching.lastTilde, PlacticEvaluation.tildeGenerator,
    map_zsmul, map_zsmul, ProjectorRank.place_generator, OnhPolynomial.polyElem_generator,
    Fin.val_last, mul_smul_comm]
  rfl

/-- EKL (4.42), `1 ≤ k+1 ≤ c = ν+1`, on the strands `[0, ν+1)`: `ε_{k+1}` on the thick strand
`c` slides below the merger of `c-1` and `1`:
`ε_{k+1} e_c = e_c ε_{k+1} + (-1)^{c-1} e_c ε_k x_{c-1}`, with `ε_{k+1}, ε_k` on the thick strand
`c-1` and the dot on the thin strand drawn lowest.  For `k+1 = c` the first term vanishes. -/
theorem eq_4_42 (ν k : ℕ) (h : ν + 1 ≤ n+2) :
    thickElem n (ν+1) (k+1) * blockE n 0 (ν+1) =
      blockE n 0 (ν+1) * thickElem n ν (k+1) +
        (-1 : ℤ)^ν • (blockE n 0 (ν+1) * thickElem n ν k * dotAt n ν) := by
  have h₀ : 0 + ν ≤ n+2 := by omega
  have h₁ : 0 + (ν+1) ≤ n+2 := by omega
  have hab := (blockE_absorb (n := n) (p := 0) (K := ν+1) (q := 0) (k := ν) le_rfl (by omega)
    (by omega)).2
  rw [thickElem, mul_assoc, blockE_mul_blockE h₁, ← thickElem, thickElem_eq_left _ _ h₁,
    thickElem_eq_left _ _ h₀, thickElem_eq_left _ _ h₀, ← mul_assoc, hab, ← mul_assoc, hab,
    epsWin_succ ν k h, mul_add, mul_smul_comm, mul_assoc]

/-- EKL (4.42) for `k = 0`: `e_c e_c = e_c (e_{c-1} ⊗ 1)`. -/
theorem eq_4_42_zero (ν : ℕ) (h : ν + 1 ≤ n+2) :
    thickElem n (ν+1) 0 * blockE n 0 (ν+1) = blockE n 0 (ν+1) * thickElem n ν 0 := by
  have hab := (blockE_absorb (n := n) (p := 0) (K := ν+1) (q := 0) (k := ν) le_rfl (by omega)
    (by omega)).2
  rw [thickElem_eq_left _ _ (by omega), thickElem_eq_left _ _ (by omega), epsWin,
    dif_pos (by omega),
    epsWin, dif_pos (by omega), FiniteCompleteElementary.elementaryPoly_zero,
    FiniteCompleteElementary.elementaryPoly_zero]
  simp only [map_one, mul_one]
  rw [blockE_mul_blockE (by omega), hab]

end Elementary

end
end OddMath.Frontier.ThickRelations
