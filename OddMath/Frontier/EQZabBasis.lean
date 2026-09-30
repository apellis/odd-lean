import OddMath.Frontier.EQZabReverse

/-!
# The Schur basis of `Z_{a,b}` over `OΛ_{a+b}` (Ellis–Qi (4.21), Corollary 4.8)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, (4.21) (citing EKL Proposition 4.11) and Corollary 4.8; EKL arXiv:1111.1320v1,
Theorem 4.16 and (4.54).

Ellis–Qi use that `OΛ̃_a ⊠ OΛ̃_b` is a free right `OΛ̃_{a+b}`-module with basis
`{s̃_μ(y) : μ ∈ Par(b,a)}`. We derive this from EKL's decomposition of the idempotent
`e_a ⊗ e_b = Σ_{α ∈ P(a,b)} σ_α λ_α` with `λ_β σ_α = δ_{αβ} e_{a+b}` (Theorem 4.16 and (4.54),
`ThickDecomposition.thm_4_16`, `ThickBubble.eq_4_54`), by applying EKL's anti-automorphism `ψ`
(which fixes dots and crossings) and letting the result act on polynomials:

* `ψ(e_k)` acts as the identity on polynomials killed by the `∂_i` of its window
  (`action_reverse_zeroHeckeProduct`), `ψ(e_{a+b})` maps into `OΛ̃_{a+b}`;
* `ψ(λ_α)` acts on `c ∈ OΛ̃_{a+b}` as left multiplication by `± rev(ŝ_{α̂})(y)` (`dualQ`), and
  `rev(ŝ_{α̂}) = ± s̃_{α̂}` (`EQZabReverse.rev_twisted`);
* hence every `g` killed by the `∂_i` inside the two blocks is `Σ_α rev(ŝ_{α̂})(y) c_α`
  with `c_α ∈ OΛ̃_{a+b}` (`ps_span`), and the coefficients are unique (`ps_indep`), by applying
  `ψ(σ_β)` and `ψ(λ_α σ_β) = δ_{αβ} ψ(e_{a+b})`.
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open NilHeckeAction NilHeckeRightBasis ZeroHecke ThickBubble OnhPolynomial
open BoxComplement BoxPartitionCount
open scoped BigOperators

noncomputable section

local instance (priority := high) zabBasisNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabBasisNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-! ## `ψ` of 0-Hecke products -/

theorem reverse_zeroHecke (i : Fin (n+1)) :
    reverseLinear n (zeroHecke n i) = crossing n i * dot n i.castSucc := by
  rw [zeroHecke, reverse_mul, reverse_dot, reverse_crossing]

/-- `ψ(∂̄_{i_1} ⋯ ∂̄_{i_k})` acts as the identity on polynomials killed by every `∂_{i_j}`. -/
theorem action_reverse_zeroHeckeProduct (w : NilCoxeterWords.Word n) (f : SkewPolynomial (n+2))
    (hf : ∀ i ∈ w, AllRankDivided.divided i f = 0) :
    action n (reverseLinear n (zeroHeckeProduct w)) f = f := by
  induction w with
  | nil => simp [zeroHeckeProduct]
  | cons i w ih =>
    rw [zeroHeckeProduct, reverse_mul, action_mul_apply, reverse_zeroHecke, action_mul_apply,
      action_dot_apply, action_crossing_apply, AllRankDivided.divided_left_mul,
      hf i List.mem_cons_self, ThickDecomposition.skew_mul_zero, sub_zero]
    exact ih fun j hj => hf j (List.mem_cons_of_mem _ hj)

/-- `ψ(e_k)` on the window `[p, p+k)` acts as the identity on polynomials killed by the `∂_i`
inside the window. -/
theorem action_reverse_blockE {p k : ℕ} (g : SkewPolynomial (n+2))
    (hg : ∀ i : Fin (n+1), p ≤ i.val → i.val + 1 < p + k → AllRankDivided.divided i g = 0) :
    action n (reverseLinear n (blockE n p k)) g = g :=
  action_reverse_zeroHeckeProduct _ g fun i hi => hg i (mem_triWord hi).1 (mem_triWord hi).2

theorem action_reverse_projector_kernel {c : SkewPolynomial (n+2)}
    (hc : c ∈ OddSymmetricKernel.kernelSubring n) :
    action n (reverseLinear n (projector n)) c = c :=
  action_reverse_zeroHeckeProduct _ c fun i _ => hc i

theorem reverse_DElem_lin (n : ℕ) :
    reverseLinear n (DElem n) = (-1 : ℤ) ^ (n + 2).choose 4 • DElem n :=
  OnhReflection.reverse_DElem n

theorem action_reverse_projector_mem (h : SkewPolynomial (n+2)) :
    action n (reverseLinear n (projector n)) h ∈ OddSymmetricKernel.kernelSubring n := by
  rw [prop_3_5, map_zsmul, reverse_mul, reverse_DElem_lin, smul_mul_assoc, map_zsmul,
    map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, action_mul_apply, action_DElem]
  exact Subring.zsmul_mem _ (Subring.zsmul_mem _ (LongestKernel.D_mem_kernel n _) _) _

/-! ## `ψ` of the dotted blocks -/

theorem windowHom_polyElem {m p : ℕ} (h : p + (m+2) ≤ n+2) (f : SkewPolynomial (m+2)) :
    OnhWindow.windowHom m n p h (polyElem m f) = polyElem n (ProjectorRank.place p h f) := by
  have e : (OnhWindow.windowHom m n p h).comp (polyElem m) =
      (polyElem n).comp (ProjectorRank.place p h) := by
    apply ringHom_ext
    intro j
    simp only [RingHom.comp_apply, polyElem_generator, OnhWindow.windowHom_dot,
      ProjectorRank.place_generator]
    rfl
  exact RingHom.congr_fun e f

theorem reverse_windowHom {m p : ℕ} (h : p + (m + 2) ≤ n + 2) (y : Presented m) :
    reverseLinear n (OnhWindow.windowHom m n p h y) =
      OnhWindow.windowHom m n p h (reverseLinear m y) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction c using FreeAlgebra.induction with
  | grade0 r =>
    rw [show Ideal.Quotient.mk (relIdeal m) (algebraMap ℤ (Free m) r) = r • (1 : Presented m) by
      rw [zsmul_eq_mul, mul_one]; simp, map_zsmul, map_zsmul, map_one, reverse_one, map_zsmul,
      reverse_one, map_zsmul, map_one]
  | grade1 g =>
    cases g with
    | inl j =>
      change reverseLinear n (OnhWindow.windowHom m n p h (dot m j)) =
        OnhWindow.windowHom m n p h (reverseLinear m (dot m j))
      simp
    | inr i =>
      change reverseLinear n (OnhWindow.windowHom m n p h (crossing m i)) =
        OnhWindow.windowHom m n p h (reverseLinear m (crossing m i))
      simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | mul c d hc hd => rw [map_mul, map_mul, reverse_mul, reverse_mul, map_mul, hc, hd]

/-- The polynomial `rev(ŝ_β)` on the window `[a, a+b)` (`x_a^{β_0}` for `b = 1`, `1` for `b = 0`). -/
def dualQ (n a : ℕ) : (b : ℕ) → a + b ≤ n+2 → (Fin b → ℕ) → SkewPolynomial (n+2)
  | 0, _, _ => 1
  | 1, h, β => generator (⟨a, by omega⟩ : Fin (n+2)) ^ β 0
  | m+2, h, β => ProjectorRank.place a h (rev (ThickDots.dualSchur β))

theorem reverse_blockDualSchur {a : ℕ} : (b : ℕ) → (h : a + b ≤ n+2) → (β : Fin b → ℕ) →
    reverseLinear n (blockDualSchur n a b h β) = polyElem n (dualQ n a b h β)
  | 0, h, β => by simp [blockDualSchur, blockMono, dualQ]
  | 1, h, β => by
    simp only [blockDualSchur, blockMono, List.finRange_succ, List.finRange_zero, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, dualQ, map_pow, polyElem_generator]
    rw [show reverseLinear n (dot n (shiftFin h 0) ^ β 0) =
      MulOpposite.unop (reverseHom n (dot n (shiftFin h 0) ^ β 0)) from rfl,
      OnhReflection.unop_reverse_dot_pow]
    congr 2
    exact Fin.ext (by simp [shiftFin])
  | m+2, h, β => by
    rw [blockDualSchur, dualQ, reverse_windowHom, reverse_polyElem, windowHom_polyElem]

theorem action_reverse_blockDualSchur {a b : ℕ} (h : a + b ≤ n+2) (β : Fin b → ℕ)
    (g : SkewPolynomial (n+2)) :
    action n (reverseLinear n (blockDualSchur n a b h β)) g = dualQ n a b h β * g := by
  rw [reverse_blockDualSchur, action_polyElem]

theorem divided_dualQ {a b : ℕ} (h : a + b ≤ n+2) (β : Fin b → ℕ) (i : Fin (n+1))
    (hi1 : a ≤ i.val) (hi2 : i.val + 1 < a + b) :
    AllRankDivided.divided i (dualQ n a b h β) = 0 := by
  match b, h, β with
  | 0, _, _ => omega
  | 1, _, _ => omega
  | m+2, h, β =>
    have hi : i = OnhWindow.shiftIndex h ⟨i.val - a, by omega⟩ := Fin.ext (by simp; omega)
    rw [dualQ, hi, (ProjectorRank.place_divided_and_s h _ _).1,
      rev_mem_kernel (ThickDots.dualSchur_mem_kernel β) _, map_zero]


/-! ## Spanning and independence -/

section Decomposition

variable {a b : ℕ} (hab : a + b = n+2)

/-- `g` is killed by the `∂_i` inside the blocks `[0, a)` and `[a, a+b)`. -/
def BlockSym (n a : ℕ) (g : SkewPolynomial (n+2)) : Prop :=
  ∀ i : Fin (n+1), (i.val + 1 < a ∨ a ≤ i.val) → AllRankDivided.divided i g = 0

include hab in
theorem action_reverse_pair (g : SkewPolynomial (n+2)) (hg : BlockSym n a g) :
    action n (reverseLinear n (blockE n 0 a * blockE n a b)) g = g := by
  rw [reverse_mul, action_mul_apply,
    action_reverse_blockE g (fun i _ h2 => hg i (Or.inl (by omega))),
    action_reverse_blockE g (fun i h1 _ => hg i (Or.inr h1))]

theorem action_reverse_lam (α : Fin a → ℕ) (h : SkewPolynomial (n+2)) :
    action n (reverseLinear n (lam n a b hab α)) h =
      (-1 : ℤ) ^ signX a b α • (dualQ n a b (by omega) (hat b α) *
        action n (reverseLinear n (projector n)) h) := by
  have hck := action_reverse_projector_mem h
  rw [lam, map_zsmul, map_zsmul, LinearMap.smul_apply]
  congr 1
  simp only [reverse_mul, action_mul_apply]
  generalize action n (reverseLinear n (projector n)) h = c at hck ⊢
  rw [action_reverse_blockE (p := 0) (k := a) c (fun i _ _ => hck i),
    action_reverse_blockE (p := a) (k := b) c (fun i _ _ => hck i),
    action_reverse_blockDualSchur]
  apply action_reverse_blockE
  intro i h1 h2
  rw [AllRankDivided.divided_mul, divided_dualQ _ _ i h1 h2, hck i,
    ThickDecomposition.skew_zero_mul, ThickDecomposition.skew_mul_zero, add_zero]

/-- **Spanning** (from EKL Theorem 4.16): every `g` killed by the `∂_i` inside the two blocks is
`Σ_{α ∈ P(a,b)} rev(ŝ_{α̂})(y) c_α` with `c_α ∈ OΛ̃_{a+b}`. -/
theorem ps_span (g : SkewPolynomial (n+2)) (hg : BlockSym n a g) :
    ∃ c : (Fin a → ℕ) → SkewPolynomial (n+2),
      (∀ α, c α ∈ OddSymmetricKernel.kernelSubring n) ∧
        g = ∑ α ∈ box a b, dualQ n a b (by omega) (hat b α) * c α := by
  refine ⟨fun α => (-1 : ℤ) ^ signX a b α • action n (reverseLinear n (projector n))
      (action n (reverseLinear n (sigma n a b hab α)) g),
    fun α => Subring.zsmul_mem _ (action_reverse_projector_mem _) _, ?_⟩
  conv_lhs => rw [← action_reverse_pair hab g hg, ThickDecomposition.thm_4_16 hab]
  rw [map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [idem, reverse_mul, action_mul_apply, action_reverse_lam hab, mul_smul_comm]

/-- **Independence** (from EKL (4.54)): the coefficients in `ps_span` are unique. -/
theorem ps_indep (c : (Fin a → ℕ) → SkewPolynomial (n+2))
    (hc : ∀ α, c α ∈ OddSymmetricKernel.kernelSubring n)
    (h0 : ∑ α ∈ box a b, dualQ n a b (by omega) (hat b α) * c α = 0) :
    ∀ β ∈ box a b, c β = 0 := by
  intro β hβ
  have key : ∀ α, dualQ n a b (by omega) (hat b α) * c α =
      (-1 : ℤ) ^ signX a b α • action n (reverseLinear n (lam n a b hab α)) (c α) := by
    intro α
    rw [action_reverse_lam hab, action_reverse_projector_kernel (hc α), smul_smul, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  have h1 := congrArg (action n (reverseLinear n (sigma n a b hab β))) h0
  rw [map_zero, map_sum] at h1
  have h2 : ∀ α ∈ box a b, action n (reverseLinear n (sigma n a b hab β))
      (dualQ n a b (by omega) (hat b α) * c α) =
        if α = β then (-1 : ℤ) ^ signX a b β • c β else 0 := by
    intro α hα
    rw [key, map_zsmul, ← action_mul_apply, ← reverse_mul,
      eq_4_54 hab (α := β) (β := α) (mem_box.1 hβ).1 (mem_box.1 hβ).2 (mem_box.1 hα).1
        (mem_box.1 hα).2]
    split_ifs with he
    · subst he
      rw [action_reverse_projector_kernel (hc _)]
    · simp
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' (box a b) β] at h1
  simp only [hβ, ite_true] at h1
  have h3 := congrArg (fun x => (-1 : ℤ) ^ signX a b β • x) h1
  simpa [smul_smul, ← pow_add, ← two_mul, pow_mul] using h3

end Decomposition

end

end OddMath.Frontier.EQZab
