import OddMath.Frontier.ThickDots
import OddMath.Frontier.OnhWindow
import OddMath.Frontier.StaircaseEvaluation
import OddMath.Frontier.StrandCrossing

/-! # Thick bubbles and the decomposition of `E^{(a)} E^{(b)}`

EKL arXiv:1111.1320v1, §4.1.1 (4.1), Prop 4.11 (4.35)–(4.36), §4.4.1 (4.51)–(4.55);
pp. 31, 38, 42–43.  Ambient ring `ONH_{a+b} = NilHeckeAction.Presented n` with `a + b = n+2`;
a written product `x * y` is `x` drawn on top of `y` (the rightmost factor acts first).

* Blocks: `blockE n p k`, `blockD n p k` are `e_k`, `D_k` on the strands `[p, p+k)` (the literal
  source word (2.36) shifted by `p`), `blockMono` an ordered monomial there, and `blockSchur`,
  `blockDualSchur` the images of `s_α` (4.17) and `ŝ_α` (Definition 4.10).  For `k ≥ 2` these
  are `OnhWindow.windowHom` images of the rank-`k` objects; for `k ≤ 1` the block `e`, `D` are
  `1`, `s_α = ŝ_α = x^α` and `χ = 0`.  The left block is `[0, a)`, the right block `[a, a+b)`,
  and `X_{a,b} = product (crossWord n 0 a b)` is the crossing (3.41).
* (4.1): `splitter = (e_a ⊗ e_b) X_{a,b}` and `merger = e_{a+b}`.
* Prop 4.11 (4.35): `e_{a+b} (e_a s_α e_a ⊗ 1)(1 ⊗ e_b ŝ_β e_b)(e_a ⊗ e_b) X_{a,b}
  = δ_{β,α̂} (-1)^{χ^a_α + χ^b_{α̂} + C(a,2)(|α̂|+C(b,2)) + Ω(α̂) + C(a+b,3)} e_{a+b}`, with the
  `s_α` factor drawn above the `ŝ_β` factor; the two factors supercommute with sign
  `(-1)^{|α||β|}` (`dual_mul_schur`).  The proof follows the paper: (4.21)–(4.22) explode the
  dotted thick strands, Prop 3.7 (`StrandCrossing.prop_3_7`) merges `D_a ⊗ D_b` with the
  crossing into `D_{a+b}`, and Lemma 4.9 evaluates the resulting top-degree monomial.
* (4.53)–(4.55): `σ_α`, `λ_α` (with the sign `X^{a,b}_α` of (4.51)), `e_α = σ_α λ_α`,
  `λ_β σ_α = δ_{αβ} e_{a+b}` and `e_β e_α = δ_{αβ} e_α` for `α, β ∈ P(a,b)`.

All statements hold for every `a, b` with `a + b = n+2`, including `a = 1` or `b = 1`. -/

namespace OddMath.Frontier.ThickBubble
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open NilHeckeAction NilCoxeterWords NilHeckeBasis LongestDivided
open ZeroHecke OnhPolynomial OnhWindow StrandCrossing BoxComplement

noncomputable section

variable {n : ℕ}

/-! ## Blocks of strands -/

/-- The 0-Hecke projector `e_k` on the strands `[p, p+k)`. -/
def blockE (n p k : ℕ) : Presented n := zeroHeckeProduct (triWord n p k)

/-- The longest divided difference `D_k` on the strands `[p, p+k)`. -/
def blockD (n p k : ℕ) : Presented n := product (triWord n p k)

/-- The strand `p + i` of the block `[p, p+k)`. -/
def shiftFin {p k : ℕ} (h : p + k ≤ n+2) (i : Fin k) : Fin (n+2) :=
  ⟨i.val + p, by have := i.isLt; omega⟩

/-- The ordered monomial `x_p^{A_0} ⋯ x_{p+k-1}^{A_{k-1}}` on the strands `[p, p+k)`. -/
def blockMono (n p k : ℕ) (h : p + k ≤ n+2) (A : Fin k → ℕ) : Presented n :=
  ((List.finRange k).map fun i => dot n (shiftFin h i) ^ A i).prod

theorem triWord_zero (p : ℕ) : triWord n p 0 = [] := rfl

theorem triWord_one (p : ℕ) : triWord n p 1 = [] := rfl

theorem blockE_zero (p : ℕ) : blockE n p 0 = 1 := rfl
theorem blockE_one (p : ℕ) : blockE n p 1 = 1 := rfl
theorem blockD_zero (p : ℕ) : blockD n p 0 = 1 := rfl
theorem blockD_one (p : ℕ) : blockD n p 1 = 1 := rfl

theorem windowHom_zeroHeckeProduct {m p : ℕ} (h : p + (m+2) ≤ n+2) (w : Word m) :
    windowHom m n p h (zeroHeckeProduct w) = zeroHeckeProduct (w.map (shiftIndex h)) := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [zeroHeckeProduct_cons, map_mul, ih, List.map_cons, zeroHecke, windowHom_dot,
        windowHom_crossing]
      rfl

theorem wordIn_map_shift {m p : ℕ} (h : p + (m+2) ≤ n+2) :
    (wordIn m (m+2) le_rfl).map (shiftIndex h) = triWord n p (m+2) := by
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [natWord_values n _ fun j hj => by have := mem_triList hj; omega, List.map_map]
  have : Fin.val ∘ shiftIndex h = (· + p) ∘ Fin.val := rfl
  rw [this, ← List.map_map, wordIn_values, triList]
  simp only [Nat.add_comm p]

theorem blockE_eq {m p : ℕ} (h : p + (m+2) ≤ n+2) :
    blockE n p (m+2) = windowHom m n p h (projector m) := by
  rw [projector, windowHom_zeroHeckeProduct, wordIn_map_shift, blockE]

theorem blockD_eq {m p : ℕ} (h : p + (m+2) ≤ n+2) :
    blockD n p (m+2) = windowHom m n p h (DElem m) := by
  rw [DElem, windowHom_product, wordIn_map_shift, blockD]

theorem blockMono_eq {m p : ℕ} (h : p + (m+2) ≤ n+2) (A : Fin (m+2) → ℕ) :
    windowHom m n p h (dotMonomial A) = blockMono n p (m+2) h A := by
  rw [dotMonomial, map_list_prod, List.map_map, blockMono]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, map_pow, windowHom_dot]
  rfl

/-! ## Degrees of block elements -/

theorem homog_of_eq {l r k k' : ℕ} {u : Presented n} (hu : Homog l r k u) (e : k = k') :
    Homog l r k' u := e ▸ hu

theorem mem_triWord {p k : ℕ} {i : Fin (n+1)} (hi : i ∈ triWord n p k) :
    p ≤ i.val ∧ i.val + 1 < p + k := by
  simp only [triWord, natWord, List.mem_filterMap, triList, List.mem_map] at hi
  obtain ⟨_, ⟨c, hc, rfl⟩, hji⟩ := hi
  have := coxeterWord_bound hc
  split_ifs at hji with hjn
  cases hji
  simp only
  omega

theorem length_triWord {p k : ℕ} (h : p + k ≤ n+2) : (triWord n p k).length = k.choose 2 := by
  rw [← List.length_map (f := Fin.val), natWord_values n _ fun j hj => by
    have := mem_triList hj; omega, triList, List.length_map, coxeterWord_length]

theorem homog_product {l r : ℕ} (w : Word n) (hw : ∀ i ∈ w, l ≤ i.val ∧ i.val + 1 < r) :
    Homog l r w.length (product w) := by
  induction w with
  | nil => exact Homog.one
  | cons i w ih =>
      obtain ⟨h₁, h₂⟩ := hw i (List.mem_cons_self)
      exact homog_of_eq ((Homog.gen (IsGen.crossing i h₁ h₂)).mul
        (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))) (by simp; omega)

theorem homog_zeroHeckeProduct {l r : ℕ} (w : Word n)
    (hw : ∀ i ∈ w, l ≤ i.val ∧ i.val + 1 < r) :
    Homog l r (2 * w.length) (zeroHeckeProduct w) := by
  induction w with
  | nil => exact Homog.one
  | cons i w ih =>
      obtain ⟨h₁, h₂⟩ := hw i (List.mem_cons_self)
      have hx : Homog l r 2 (zeroHecke n i) :=
        (Homog.gen (IsGen.dot i.castSucc h₁ (by simp; omega))).mul
          (Homog.gen (IsGen.crossing i h₁ h₂))
      exact homog_of_eq (hx.mul (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))) (by simp; omega)

theorem homog_blockD {p k : ℕ} (h : p + k ≤ n+2) :
    Homog p (p+k) (k.choose 2) (blockD n p k) :=
  homog_of_eq (homog_product _ fun _ hi => mem_triWord hi) (length_triWord h)

theorem homog_blockE {p k : ℕ} (h : p + k ≤ n+2) :
    Homog p (p+k) (2 * k.choose 2) (blockE n p k) :=
  homog_of_eq (homog_zeroHeckeProduct _ fun _ hi => mem_triWord hi) (by rw [length_triWord h])

theorem homog_pow {l r : ℕ} {x : Presented n} (hx : IsGen l r x) (e : ℕ) :
    Homog l r e (x ^ e) := by
  induction e with
  | zero => rw [pow_zero]; exact Homog.one
  | succ e ih => rw [pow_succ]; exact ih.mul (Homog.gen hx)

theorem homog_blockMono {p k : ℕ} (h : p + k ≤ n+2) (A : Fin k → ℕ) :
    Homog p (p+k) (∑ i, A i) (blockMono n p k h A) := by
  have key : ∀ l : List (Fin k), Homog p (p+k) (l.map A).sum
      ((l.map fun i => dot n (shiftFin h i) ^ A i).prod) := by
    intro l
    induction l with
    | nil => exact Homog.one
    | cons i l ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        exact (homog_pow (IsGen.dot _ (by simp [shiftFin]) (by simp [shiftFin]; omega)) _).mul ih
  rw [Fin.sum_univ_def]
  exact key _

theorem homog_comm_of_even {l r l' r' k k' : ℕ} {u v : Presented n} (hu : Homog l r k u)
    (hv : Homog l' r' k' v) (hrl : r ≤ l') (he : Even (k * k')) : u * v = v * u := by
  rw [hu.supercomm hv hrl, he.neg_one_pow, one_mul]

theorem homog_supercomm_zsmul {l r l' r' k k' : ℕ} {u v : Presented n} (hu : Homog l r k u)
    (hv : Homog l' r' k' v) (hrl : r ≤ l') : u * v = (-1 : ℤ)^(k * k') • (v * u) := by
  rw [hu.supercomm hv hrl, zsmul_eq_mul]
  simp

/-! ## Block identities -/

/-- Case analysis on the size of a block: `0`, `1`, or at least `2`. -/
theorem block_cases {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) (h2 : ∀ m, P (m+2)) : ∀ k, P k
  | 0 => h0
  | 1 => h1
  | m+2 => h2 m

theorem blockE_mul_blockE {p k : ℕ} (h : p + k ≤ n+2) :
    blockE n p k * blockE n p k = blockE n p k := by
  induction k using block_cases with
  | h0 => exact mul_one _
  | h1 => exact mul_one _
  | h2 m => rw [blockE_eq h, ← map_mul, projector_mul_projector]

theorem blockD_mul_blockE {p k : ℕ} (h : p + k ≤ n+2) :
    blockD n p k * blockE n p k = blockD n p k := by
  induction k using block_cases with
  | h0 => exact mul_one _
  | h1 => exact mul_one _
  | h2 m => rw [blockE_eq h, blockD_eq h, ← map_mul, DElem_mul_projector]

/-- `e_{a+b}` absorbs every block projector (Prop 3.6, EKL (3.40)). -/
theorem projector_mul_blockE (p k : ℕ) : projector n * blockE n p k = projector n :=
  projector_mul_zeroHeckeProduct _

/-- EKL Prop 3.7 (3.45): `D_{a+b} = (D_a ⊗ D_b) X_{a,b}`. -/
theorem blockD_mul_blockD_crossing {a b : ℕ} (hab : a + b = n+2) :
    blockD n 0 a * blockD n a b * product (crossWord n 0 a b) = DElem n :=
  (prop_3_7 n a b hab).1.symm

/-! ## Dotted blocks -/

/-- The odd Schur polynomial `s_α` (4.17) on the strands `[p, p+k)`; on one strand `x^α`. -/
def blockSchur (n p : ℕ) : (k : ℕ) → p + k ≤ n+2 → (Fin k → ℕ) → Presented n
  | 0, h, α => blockMono n p 0 h α
  | 1, h, α => blockMono n p 1 h α
  | m+2, h, α => windowHom m n p h (polyElem m (ThickDots.schur α))

/-- The dual Schur polynomial `ŝ_α` (Definition 4.10) on the strands `[p, p+k)`. -/
def blockDualSchur (n p : ℕ) : (k : ℕ) → p + k ≤ n+2 → (Fin k → ℕ) → Presented n
  | 0, h, α => blockMono n p 0 h α
  | 1, h, α => blockMono n p 1 h α
  | m+2, h, α => windowHom m n p h (polyElem m (ThickDots.dualSchur α))

/-- The exponent `χ^k_α` of (4.20); it vanishes for `k ≤ 1`. -/
def blockChi : (k : ℕ) → (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | _+2, α => ThickDots.chi α

theorem blockSchur_eq {m p : ℕ} (h : p + (m+2) ≤ n+2) (α : Fin (m+2) → ℕ) :
    blockSchur n p (m+2) h α = windowHom m n p h (polyElem m (ThickDots.schur α)) := rfl

theorem blockDualSchur_eq {m p : ℕ} (h : p + (m+2) ≤ n+2) (α : Fin (m+2) → ℕ) :
    blockDualSchur n p (m+2) h α = windowHom m n p h (polyElem m (ThickDots.dualSchur α)) := rfl

theorem blockChi_eq {m : ℕ} (α : Fin (m+2) → ℕ) : blockChi (m+2) α = ThickDots.chi α := rfl

/-- On one strand, `s_α = ŝ_α = x_p^{α_0}`. -/
theorem blockSchur_one {p : ℕ} (h : p + 1 ≤ n+2) (α : Fin 1 → ℕ) :
    blockSchur n p 1 h α = dot n ⟨p, by omega⟩ ^ α 0 ∧
      blockDualSchur n p 1 h α = dot n ⟨p, by omega⟩ ^ α 0 := by
  constructor <;>
  · simp only [blockSchur, blockDualSchur, blockMono, List.finRange_succ, List.finRange_zero]
    simp [shiftFin]

theorem expA_small {k : ℕ} (hk : k ≤ 1) (α : Fin k → ℕ) : expA α = α := by
  funext i
  have := i.isLt
  simp only [expA]
  omega

theorem expB_small {k : ℕ} (hk : k ≤ 1) (α : Fin k → ℕ) : expB α = α := by
  funext i
  have hi := i.isLt
  have : Fin.rev i = i := Fin.ext (by rw [Fin.val_rev]; omega)
  simp only [expB, this]
  omega

/-- EKL (4.21)–(4.22) on a block: `e s_α e = (-1)^{χ_α} e x^{α+δ} D`. -/
theorem blockE_schur_blockE {p k : ℕ} (h : p + k ≤ n+2) (α : Fin k → ℕ) :
    blockE n p k * blockSchur n p k h α * blockE n p k =
      (-1 : ℤ)^(blockChi k α) • (blockE n p k * blockMono n p k h (expA α) * blockD n p k) := by
  match k, h, α with
  | 0, h, α =>
      rw [expA_small (by omega)]
      simp [blockSchur, blockChi, blockE_zero, blockD_zero]
  | 1, h, α =>
      rw [expA_small le_rfl]
      simp [blockSchur, blockChi, blockE_one, blockD_one]
  | m+2, h, α =>
      have hA : expA α = α + ThickDots.delta m := by
        funext i
        simp only [expA, ThickDots.delta, Pi.add_apply]
        omega
      rw [blockE_eq h, blockD_eq h, hA, ← blockMono_eq h, ← polyElem_monomial, blockSchur,
        blockChi, ← map_mul, ← map_mul, ThickDots.projector_schur_projector, map_zsmul, map_mul,
        map_mul]

/-- EKL, after Definition 4.10, on a block: `e ŝ_β e = (-1)^{χ_β} e x^{B} D`. -/
theorem blockE_dualSchur_blockE {p k : ℕ} (h : p + k ≤ n+2) (β : Fin k → ℕ) :
    blockE n p k * blockDualSchur n p k h β * blockE n p k =
      (-1 : ℤ)^(blockChi k β) • (blockE n p k * blockMono n p k h (expB β) * blockD n p k) := by
  match k, h, β with
  | 0, h, β =>
      rw [expB_small (by omega)]
      simp [blockDualSchur, blockChi, blockE_zero, blockD_zero]
  | 1, h, β =>
      rw [expB_small le_rfl]
      simp [blockDualSchur, blockChi, blockE_one, blockD_one]
  | m+2, h, β =>
      rw [blockE_eq h, blockD_eq h, ← blockMono_eq h, ← polyElem_monomial, blockDualSchur,
        blockChi, ← map_mul, ← map_mul, ThickDots.projector_dualSchur_projector, map_zsmul,
        map_mul, map_mul]
      rfl

theorem blockSchur_mem {p k : ℕ} (h : p + k ≤ n+2) (α : Fin k → ℕ) :
    blockSchur n p k h α ∈ Supported n p (p+k) := by
  match k, h, α with
  | 0, h, α => exact (homog_blockMono h α).mem_supported
  | 1, h, α => exact (homog_blockMono h α).mem_supported
  | m+2, h, α => exact windowHom_mem_supported _

theorem blockDualSchur_mem {p k : ℕ} (h : p + k ≤ n+2) (α : Fin k → ℕ) :
    blockDualSchur n p k h α ∈ Supported n p (p+k) := by
  match k, h, α with
  | 0, h, α => exact (homog_blockMono h α).mem_supported
  | 1, h, α => exact (homog_blockMono h α).mem_supported
  | m+2, h, α => exact windowHom_mem_supported _

theorem blockE_mem_even {p k : ℕ} (h : p + k ≤ n+2) :
    blockE n p k ∈ SupportedEven n p (p+k) :=
  (homog_blockE h).mem_even (even_two_mul _)

/-! ## The monomial of (4.32)–(4.33) and Lemma 4.9 -/

/-- Adjacent blocks: `x^A ⊗ x^B = x^{A ⊕ B}` (no sign, `A` sits on the earlier strands). -/
theorem blockMono_mul_blockMono {a b : ℕ} (hab : a + b = n+2) (A : Fin a → ℕ) (B : Fin b → ℕ) :
    blockMono n 0 a (by omega) A * blockMono n a b (by omega) B =
      polyElem n (monomial (fun j => Fin.append A B (Fin.cast hab.symm j)) 1) := by
  rw [polyElem_monomial, dotMonomial, blockMono, blockMono, ← List.ofFn_eq_map,
    ← List.ofFn_eq_map, ← List.ofFn_eq_map, List.ofFn_congr hab.symm, List.ofFn_add,
    List.prod_append]
  congr 2
  · congr 1
    funext i
    simp only [Fin.cast_trans, Fin.cast_eq_self, Fin.append_left]
    congr 2
  · congr 1
    funext j
    simp only [Fin.cast_trans, Fin.cast_eq_self, Fin.append_right]
    congr 2
    all_goals exact Fin.ext (by simp [shiftFin, Nat.add_comm])

open StaircaseEvaluation in
/-- EKL Lemma 4.9 in the ambient rank `n+2 = a+b`. -/
theorem D_exps {a b : ℕ} (hab : a + b = n+2) {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    D (n+2) (monomial (fun j => exps α β (Fin.cast hab.symm j)) 1) =
      (if α = hat a β then (-1 : ℤ)^(omega β + (a+b).choose 3) else 0) • 1 := by
  have key : ∀ N (hN : a + b = N),
      D N (monomial (fun j => exps α β (Fin.cast hN.symm j)) 1) =
        (if α = hat a β then (-1 : ℤ)^(omega β + (a+b).choose 3) else 0) • 1 := by
    rintro N rfl
    exact lemma_4_9 hα hαb hβ hβa
  exact key (n+2) hab

/-! ## Box combinatorics -/

theorem sum_expA {a : ℕ} (α : Fin a → ℕ) : ∑ k, expA α k = a.choose 2 + ∑ k, α k := by
  have hrev : ∀ k : Fin a, a - 1 - k.val = (Fin.rev k).val := by
    intro k
    rw [Fin.val_rev]
    omega
  simp only [expA, hrev]
  rw [Finset.sum_add_distrib, show ∑ k : Fin a, k.rev.val = ∑ k : Fin a, k.val from
    Equiv.sum_comp Fin.revPerm (fun k : Fin a => k.val), sum_val_fin]

theorem sum_expB {b : ℕ} (β : Fin b → ℕ) : ∑ j, expB β j = b.choose 2 + ∑ j, β j := by
  simp only [expB]
  rw [Finset.sum_add_distrib, sum_val_fin,
    show ∑ j : Fin b, β j.rev = ∑ j, β j from Equiv.sum_comp Fin.revPerm β]

/-- `α ↦ α̂` is an involution on partitions in a box. -/
theorem hat_hat {a b : ℕ} {β : Fin b → ℕ} (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    hat b (hat a β) = β := by
  funext j
  have key : ∀ t : ℕ, t < a → (t < hat b (hat a β) j ↔ t < β j) := by
    intro t ht
    rw [lt_hat_iff hat_antitone j ⟨t, ht⟩, ← not_lt]
    have h2 := lt_hat_iff hβ (Fin.rev (⟨t, ht⟩ : Fin a)) (Fin.rev j)
    simp only [Fin.rev_rev, Fin.val_rev] at h2
    have e : b - (j.val + 1) = b - 1 - j.val := by omega
    rw [← e, h2]
    omega
  have h1 := hat_le (a := b) (β := hat a β) j
  have h2 := hβa j
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd ((key _ (by omega)).mpr hlt) (lt_irrefl _)
  · exact absurd ((key _ (by omega)).mp hlt) (lt_irrefl _)

theorem eq_hat_iff {a b : ℕ} {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    β = hat b α ↔ α = hat a β := by
  constructor
  · rintro rfl; exact (hat_hat hα hαb).symm
  · rintro rfl; exact (hat_hat hβ hβa).symm

/-! ## Ring bookkeeping -/

section Bookkeeping
variable {E eL eR DL DR xA xB X D P S T : Presented n}

private theorem core_abstract {s c : ℤ} (c1 : DL * eR = eR * DL) (c2 : DL * xB = s • (xB * DL))
    (c3 : xA * eR = eR * xA) (p37 : DL * DR * X = D) (a1 : E * eL = E) (a2 : E * eR = E)
    (hP : xA * xB = P) (hfin : E * P * D = c • E) :
    E * (eL * xA * DL) * (eR * xB * DR) * X = (s * c) • E :=
  calc E * (eL * xA * DL) * (eR * xB * DR) * X = E * eL * xA * (DL * eR) * xB * DR * X := by
        simp only [mul_assoc]
    _ = E * eL * xA * eR * (DL * xB) * DR * X := by rw [c1]; simp only [mul_assoc]
    _ = s • (E * eL * xA * eR * xB * (DL * DR * X)) := by
        rw [c2]; simp only [mul_assoc, smul_mul_assoc, mul_smul_comm]
    _ = s • (E * (xA * eR) * xB * D) := by rw [p37, a1]; simp only [mul_assoc]
    _ = s • (E * (xA * xB) * D) := by rw [c3, ← mul_assoc E eR, a2]; simp only [mul_assoc]
    _ = (s * c) • E := by rw [hP, hfin, smul_smul]

private theorem splitter_abstract (hTeL : T * eL = eL * T) (hSeL : S * eL = S)
    (hTeR : T * eR = T) : E * S * T * (eL * eR * X) = E * S * T * X :=
  calc E * S * T * (eL * eR * X) = E * S * (T * eL) * eR * X := by simp only [mul_assoc]
    _ = E * (S * eL) * (T * eR) * X := by rw [hTeL]; simp only [mul_assoc]
    _ = E * S * T * X := by rw [hSeL, hTeR]

private theorem swap_abstract {σ : ℤ} (hswap : T * S = σ • (S * T)) (hLS : eL * S = S)
    (hTeR : T * eR = T) : E * (eL * T) * (S * eR * X) = σ • (E * S * T * X) :=
  calc E * (eL * T) * (S * eR * X) = E * eL * (T * S) * eR * X := by simp only [mul_assoc]
    _ = σ • (E * (eL * S) * (T * eR) * X) := by
        rw [hswap]; simp only [mul_assoc, smul_mul_assoc, mul_smul_comm]
    _ = σ • (E * S * T * X) := by rw [hLS, hTeR]

private theorem left_abstract (hc : S * eR = eR * S) (hLS : eL * S = S) (hRR : eR * eR = eR) :
    eL * eR * (S * eR * X) = S * eR * X :=
  calc eL * eR * (S * eR * X) = eL * (eR * S) * (eR * X) := by simp only [mul_assoc]
    _ = eL * S * (eR * eR) * X := by rw [← hc]; simp only [mul_assoc]
    _ = S * eR * X := by rw [hLS, hRR]

private theorem right_abstract (hTeL : T * eL = eL * T) (hLL : eL * eL = eL) (hTeR : T * eR = T) :
    E * (eL * T) * (eL * eR) = E * (eL * T) :=
  calc E * (eL * T) * (eL * eR) = E * eL * (T * eL) * eR := by simp only [mul_assoc]
    _ = E * (eL * eL) * (T * eR) := by rw [hTeL]; simp only [mul_assoc]
    _ = E * (eL * T) := by rw [hLL, hTeR, mul_assoc]

end Bookkeeping

private theorem neg_one_pow_parity (A B x y : ℕ) :
    (-1 : ℤ)^((2*A + (A + x) + A) * (2*B + (B + y) + B)) = (-1)^(x*y) := by
  have e : (2*A + (A + x) + A) * (2*B + (B + y) + B) = x*y + 2*(8*A*B + 2*A*y + 2*B*x) := by
    ring
  rw [e, pow_add, pow_mul (-1 : ℤ) 2, neg_one_sq, one_pow, mul_one]

/-! ## The bubble of Proposition 4.11 -/

open StaircaseEvaluation in
/-- The top-degree evaluation behind (4.36): `e_{a+b} (e_a x^A D_a ⊗ e_b x^B D_b) X_{a,b}`. -/
theorem bubble_core {a b : ℕ} (hab : a + b = n+2) {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    projector n * (blockE n 0 a * blockMono n 0 a (by omega) (expA α) * blockD n 0 a) *
        (blockE n a b * blockMono n a b (by omega) (expB β) * blockD n a b) *
        product (crossWord n 0 a b) =
      ((-1 : ℤ)^(a.choose 2 * ∑ j, expB β j) *
        (if α = hat a β then (-1 : ℤ)^(omega β + (a+b).choose 3) else 0)) • projector n := by
  have hL : 0 + a ≤ n+2 := by omega
  have hR : a + b ≤ n+2 := by omega
  have hle : 0 + a ≤ a := by omega
  have hev : ∀ k, Even (k * (2 * b.choose 2)) :=
    fun k => Nat.even_mul.mpr (Or.inr (even_two_mul _))
  refine core_abstract (homog_comm_of_even (homog_blockD hL) (homog_blockE hR) hle (hev _))
    (homog_supercomm_zsmul (homog_blockD hL) (homog_blockMono hR _) hle)
    (homog_comm_of_even (homog_blockMono hL _) (homog_blockE hR) hle (hev _))
    (blockD_mul_blockD_crossing hab) (projector_mul_blockE _ _) (projector_mul_blockE _ _)
    (blockMono_mul_blockMono hab _ _) ?_
  exact ThickDots.projector_poly_DElem _ _ (D_exps hab hα hαb hβ hβa)

/-- The sign of (4.35): `χ^a_α + χ^b_{α̂} + C(a,2)(|α̂| + C(b,2)) + Ω(α̂) + C(a+b,3)`. -/
def bubbleSign (a b : ℕ) (α : Fin a → ℕ) : ℕ :=
  blockChi a α + blockChi b (hat b α) + a.choose 2 * (∑ j, hat b α j + b.choose 2) +
    StaircaseEvaluation.omega (hat b α) + (a+b).choose 3

/-- EKL (4.36): the bubble `e_{a+b} (e_a s_α e_a ⊗ e_b ŝ_β e_b) X_{a,b}`, with the `s_α` part
drawn above the `ŝ_β` part. -/
theorem bubble {a b : ℕ} (hab : a + b = n+2) {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    projector n * (blockE n 0 a * blockSchur n 0 a (by omega) α * blockE n 0 a) *
        (blockE n a b * blockDualSchur n a b (by omega) β * blockE n a b) *
        product (crossWord n 0 a b) =
      (if β = hat b α then (-1 : ℤ)^(bubbleSign a b α) else 0) • projector n := by
  rw [blockE_schur_blockE, blockE_dualSchur_blockE]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [bubble_core hab hα hαb hβ hβa, smul_smul]
  congr 1
  by_cases hc : β = hat b α
  · subst hc
    rw [if_pos rfl, if_pos (hat_hat hα hαb).symm, sum_expB]
    simp only [← pow_add, bubbleSign]
    congr 1
    ring
  · rw [if_neg hc, if_neg fun h => hc ((eq_hat_iff hα hαb hβ hβa).mpr h), mul_zero, mul_zero]

/-! ## Splitters and Proposition 4.11 -/

/-- EKL (4.1), left: the splitter of `a+b` into `a` and `b`, `(e_a ⊗ e_b) X_{a,b}`. -/
def splitter (n a b : ℕ) : Presented n := blockE n 0 a * blockE n a b * product (crossWord n 0 a b)

/-- EKL (4.1), right: the merger of `a` and `b` into `a+b`, `e_{a+b}`. -/
def merger (n : ℕ) : Presented n := projector n

theorem blockE_schur_blockE_mem {p k : ℕ} (h : p + k ≤ n+2) (α : Fin k → ℕ) :
    blockE n p k * blockSchur n p k h α * blockE n p k ∈ Supported n p (p+k) :=
  Subring.mul_mem _ (Subring.mul_mem _ (homog_blockE h).mem_supported (blockSchur_mem h α))
    (homog_blockE h).mem_supported

theorem blockE_dualSchur_blockE_mem {p k : ℕ} (h : p + k ≤ n+2) (α : Fin k → ℕ) :
    blockE n p k * blockDualSchur n p k h α * blockE n p k ∈ Supported n p (p+k) :=
  Subring.mul_mem _ (Subring.mul_mem _ (homog_blockE h).mem_supported (blockDualSchur_mem h α))
    (homog_blockE h).mem_supported

/-- EKL Prop 4.11 (4.35). -/
theorem prop_4_11 {a b : ℕ} (hab : a + b = n+2) {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    merger n * (blockE n 0 a * blockSchur n 0 a (by omega) α * blockE n 0 a) *
        (blockE n a b * blockDualSchur n a b (by omega) β * blockE n a b) * splitter n a b =
      (if β = hat b α then (-1 : ℤ)^(bubbleSign a b α) else 0) • merger n := by
  have hL : 0 + a ≤ n+2 := by omega
  have hR : a + b ≤ n+2 := by omega
  rw [merger, splitter, splitter_abstract, bubble hab hα hαb hβ hβa]
  · exact (even_commute (blockE_mem_even hL) (blockE_dualSchur_blockE_mem hR β)
      (by omega)).symm
  · rw [mul_assoc, blockE_mul_blockE hL]
  · rw [mul_assoc, blockE_mul_blockE hR]

/-! ## Decomposition of `E^{(a)} E^{(b)}` (§4.4.1) -/

/-- Supercommutation of the two thick dotted blocks:
`(e_b ŝ_β e_b)(e_a s_α e_a) = (-1)^{|α||β|} (e_a s_α e_a)(e_b ŝ_β e_b)`. -/
theorem dual_mul_schur {a b : ℕ} (hab : a + b = n+2) (α : Fin a → ℕ) (β : Fin b → ℕ) :
    (blockE n a b * blockDualSchur n a b (by omega) β * blockE n a b) *
        (blockE n 0 a * blockSchur n 0 a (by omega) α * blockE n 0 a) =
      (-1 : ℤ)^((∑ k, α k) * ∑ j, β j) •
        ((blockE n 0 a * blockSchur n 0 a (by omega) α * blockE n 0 a) *
          (blockE n a b * blockDualSchur n a b (by omega) β * blockE n a b)) := by
  have hL : 0 + a ≤ n+2 := by omega
  have hR : a + b ≤ n+2 := by omega
  rw [blockE_schur_blockE, blockE_dualSchur_blockE]
  have h := homog_supercomm_zsmul
    (((homog_blockE hL).mul (homog_blockMono hL (expA α))).mul (homog_blockD hL))
    (((homog_blockE hR).mul (homog_blockMono hR (expB β))).mul (homog_blockD hR))
    (by omega : 0 + a ≤ a)
  rw [sum_expA, sum_expB, neg_one_pow_parity] at h
  have h' : blockE n a b * blockMono n a b hR (expB β) * blockD n a b *
      (blockE n 0 a * blockMono n 0 a hL (expA α) * blockD n 0 a) =
      (-1 : ℤ)^((∑ k, α k) * ∑ j, β j) •
        (blockE n 0 a * blockMono n 0 a hL (expA α) * blockD n 0 a *
          (blockE n a b * blockMono n a b hR (expB β) * blockD n a b)) := by
    rw [h, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h', smul_smul]
  congr 1
  ring

/-- EKL (4.53): `σ_α = (e_a s_α e_a ⊗ e_b) X_{a,b}`, the `s_α`-dotted splitter. -/
def sigma (n a b : ℕ) (hab : a + b = n+2) (α : Fin a → ℕ) : Presented n :=
  blockE n 0 a * blockSchur n 0 a (by omega) α * blockE n 0 a * blockE n a b *
    product (crossWord n 0 a b)

/-- EKL (4.51): `X^{a,b}_α = |α||α̂| + χ^a_α + χ^b_{α̂} + C(a,2)(|α̂| + C(b,2)) + Ω(α̂) + C(a+b,3)`. -/
def signX (a b : ℕ) (α : Fin a → ℕ) : ℕ := (∑ k, α k) * (∑ j, hat b α j) + bubbleSign a b α

/-- EKL (4.53): `λ_α = (-1)^{X^{a,b}_α} e_{a+b} (e_a ⊗ e_b ŝ_{α̂} e_b)`, the `ŝ_{α̂}`-dotted
merger. -/
def lam (n a b : ℕ) (hab : a + b = n+2) (α : Fin a → ℕ) : Presented n :=
  (-1 : ℤ)^(signX a b α) • (projector n *
    (blockE n 0 a * (blockE n a b * blockDualSchur n a b (by omega) (hat b α) * blockE n a b)))

/-- EKL (4.53): `e_α = σ_α λ_α`. -/
def idem (n a b : ℕ) (hab : a + b = n+2) (α : Fin a → ℕ) : Presented n :=
  sigma n a b hab α * lam n a b hab α

theorem sigma_eq_splitter {a b : ℕ} (hab : a + b = n+2) (α : Fin a → ℕ) :
    sigma n a b hab α =
      blockE n 0 a * blockSchur n 0 a (by omega) α * blockE n 0 a * splitter n a b := by
  rw [sigma, splitter, ← mul_assoc, ← mul_assoc, mul_assoc _ (blockE n 0 a) (blockE n 0 a),
    blockE_mul_blockE (by omega)]

/-- `(e_a ⊗ e_b) σ_α = σ_α`. -/
theorem blockE_mul_sigma {a b : ℕ} (hab : a + b = n+2) (α : Fin a → ℕ) :
    blockE n 0 a * blockE n a b * sigma n a b hab α = sigma n a b hab α := by
  have hL : 0 + a ≤ n+2 := by omega
  rw [sigma]
  refine left_abstract (commute_even (blockE_schur_blockE_mem hL α) (blockE_mem_even (p := a)
    (k := b) (by omega)) (by omega)) ?_ (blockE_mul_blockE (by omega))
  rw [← mul_assoc, ← mul_assoc, blockE_mul_blockE hL]

/-- `λ_α (e_a ⊗ e_b) = λ_α`. -/
theorem lam_mul_blockE {a b : ℕ} (hab : a + b = n+2) (α : Fin a → ℕ) :
    lam n a b hab α * (blockE n 0 a * blockE n a b) = lam n a b hab α := by
  have hR : a + b ≤ n+2 := by omega
  rw [lam, smul_mul_assoc, right_abstract _ (blockE_mul_blockE (by omega))]
  · rw [mul_assoc, blockE_mul_blockE hR]
  · exact (even_commute (blockE_mem_even (p := 0) (k := a) (by omega))
      (blockE_dualSchur_blockE_mem hR _) (by omega)).symm

theorem projector_mul_lam {a b : ℕ} (hab : a + b = n+2) (α : Fin a → ℕ) :
    projector n * lam n a b hab α = lam n a b hab α := by
  rw [lam, mul_smul_comm, ← mul_assoc, projector_mul_projector]

/-- EKL (4.54): `λ_β σ_α = δ_{αβ} e_{a+b}` for `α, β ∈ P(a,b)`. -/
theorem eq_4_54 {a b : ℕ} (hab : a + b = n+2) {α β : Fin a → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβb : ∀ k, β k ≤ b) :
    lam n a b hab β * sigma n a b hab α = if β = α then projector n else 0 := by
  have hL : 0 + a ≤ n+2 := by omega
  have hR : a + b ≤ n+2 := by omega
  rw [lam, sigma, smul_mul_assoc, swap_abstract (dual_mul_schur hab α (hat b β)),
    bubble hab hα hαb hat_antitone hat_le]
  · by_cases hc : β = α
    · subst hc
      rw [if_pos rfl, if_pos rfl, smul_smul, smul_smul, ← pow_add, ← pow_add, signX,
        Even.neg_one_pow ⟨(∑ k, β k) * (∑ j, hat b β j) + bubbleSign a b β, by ring⟩, one_smul]
    · have hne : ¬ hat b β = hat b α := fun h => hc (by
        have := congrArg (hat a) h
        rwa [hat_hat hβ hβb, hat_hat hα hαb] at this)
      rw [if_neg hne, if_neg hc, zero_smul, smul_zero, smul_zero]
  · rw [← mul_assoc, ← mul_assoc, blockE_mul_blockE hL]
  · rw [mul_assoc, blockE_mul_blockE hR]

/-- EKL (4.55): `e_β e_α = δ_{αβ} e_α` for `α, β ∈ P(a,b)`. -/
theorem eq_4_55 {a b : ℕ} (hab : a + b = n+2) {α β : Fin a → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβb : ∀ k, β k ≤ b) :
    idem n a b hab β * idem n a b hab α = if β = α then idem n a b hab α else 0 := by
  rw [idem, idem, mul_assoc, ← mul_assoc (lam n a b hab β), eq_4_54 hab hα hαb hβ hβb]
  by_cases hc : β = α
  · subst hc
    rw [if_pos rfl, if_pos rfl, projector_mul_lam]
  · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]

end

end OddMath.Frontier.ThickBubble
