import OddMath.Frontier.EQZabHatFormulas

/-!
# The trace map `z^∨` (Ellis–Qi, Definition 4.9, Corollary 4.10)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, the trace `∂_{a,b}`, `z^∨ = θ ∘ ∂_{a,b}`, (4.22), (4.24), Definition 4.9 and
Corollary 4.10 (printed numbering); EKL arXiv:1111.1320v1, Proposition 4.11 (4.35).

* `rev_twisted_exact`: the exact sign relating `rev(s̃_λ)` and `s̃̂_λ`.
* `pairing`: the orthogonality (4.22) with the sign of EKL (4.35), for `∂_{a,b}` (`pdAB`).
* `cor_4_10`: Corollary 4.10 as printed, with `d(z^∨) = (-1)^{ab-1}{b} z^∨ ẽ_1(x)` of (4.26) read as
  `G z ↦ z^∨(ẽ_1(x) G z)`.
* (4.24) calls `z^∨` right `OΛ_{a+b}`-linear for the action `z · h = (θ ∘ w₀)(h) z`; it is only
  `w₀`-semilinear (`trace_mul_twistRev`) and not linear (`trace_not_linear`), while `w₀ ∘ z^∨` is
  linear (`trace_linear`). Corollary 4.10 holds for either, since `d ∘ w₀ = w₀ ∘ d`.
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open scoped BigOperators

noncomputable section

local instance (priority := high) zabTrNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabTrNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ## Exact reversal of monomials and of odd Schur polynomials -/

section Generic

variable {R : Type*} [Ring R]

theorem pow_mul_prod_pow_anti (y : R) : ∀ (L : List (R × ℕ)) (p : ℕ),
    (∀ u ∈ L, y * u.1 = -(u.1 * y)) →
      y ^ p * (L.map fun u => u.1 ^ u.2).prod =
        (-1 : ℤ) ^ (p * (L.map Prod.snd).sum) • ((L.map fun u => u.1 ^ u.2).prod * y ^ p)
  | [], p, _ => by simp
  | u :: L, p, h => by
    have ih := pow_mul_prod_pow_anti y L p (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [← mul_assoc, OnhReflection.pow_mul_pow_anti (h u List.mem_cons_self), smul_mul_assoc,
      mul_assoc, ih, mul_smul_comm, smul_smul, ← mul_assoc, ← pow_add, mul_add]

theorem pairSum_succ {m : ℕ} (c : Fin (m+1) → ℕ) :
    pairSum c = pairSum (fun i => c i.succ) + c 0 * ∑ j, c (Fin.succ j) := by
  unfold pairSum
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [lt_self_iff_false, ite_false, zero_add, Fin.succ_pos, ite_true, Fin.sum_univ_succ,
    Fin.succ_lt_succ_iff, Fin.not_lt_zero, Finset.mul_sum]
  ring

theorem reverse_ofFn_pow {m : ℕ} (x : Fin m → R)
    (hx : ∀ i j, i ≠ j → x i * x j = -(x j * x i)) (c : Fin m → ℕ) :
    (List.ofFn fun i => x i ^ c i).reverse.prod =
      (-1 : ℤ) ^ pairSum c • (List.ofFn fun i => x i ^ c i).prod := by
  induction m with
  | zero => simp [pairSum]
  | succ m ih =>
    have ih' := ih (fun i => x i.succ) (fun i j h => hx _ _ (fun e => h (Fin.succ_injective _ e)))
      (fun i => c i.succ)
    have hL : (List.ofFn fun i : Fin m => x i.succ ^ c i.succ) =
        (List.ofFn fun i : Fin m => (x i.succ, c i.succ)).map fun u => u.1 ^ u.2 := by
      rw [List.map_ofFn]; rfl
    have hsum : ((List.ofFn fun i : Fin m => (x i.succ, c i.succ)).map Prod.snd).sum =
        ∑ j, c (Fin.succ j) := by
      rw [List.map_ofFn, List.sum_ofFn]; rfl
    have hcomm := pow_mul_prod_pow_anti (x 0) (List.ofFn fun i : Fin m => (x i.succ, c i.succ))
      (c 0) (fun u hu => by
        rw [List.mem_ofFn] at hu
        obtain ⟨i, rfl⟩ := hu
        exact hx _ _ (Fin.succ_ne_zero i).symm)
    rw [← hL, hsum] at hcomm
    rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton, ih',
      List.prod_cons, hcomm, smul_mul_assoc, smul_smul, pairSum_succ, pow_add]
    congr 1
    rw [mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

end Generic

variable {N : ℕ}

/-- `rev(x^c) = (-1)^{Σ_{i<j} c_i c_j} x^c`. -/
theorem rev_monomial_exact (c : Fin N → ℕ) :
    rev (monomial c 1) = (-1 : ℤ) ^ pairSum c • monomial c 1 := by
  rw [MonomialReversal.monomial_eq_prod, rev_list_prod]
  have hmap : (List.ofFn fun i => generator i ^ c i).map rev =
      List.ofFn fun i => (generator i ^ c i : SkewPolynomial N) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply]
    induction c i with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, rev_mul, ih, rev_generator]
      exact (pow_mul_comm' _ _).symm
  rw [hmap]
  exact reverse_ofFn_pow _ (fun i j h => EQSkewDifferential.generator_anticomm i j h) c

/-- **Exact** reversal of twisted odd Schur polynomials:
`rev(s̃_λ) = (-1)^{binom(N,4) + |λ| binom(N,2)} s̃̂_λ`, for every exponent vector `λ`. -/
theorem rev_twisted_exact (l : Fin N → ℕ) :
    rev (twisted N l) = (-1 : ℤ) ^ (N.choose 4 + (∑ j, l j) * N.choose 2) • twistedHat N l := by
  set m := monomial l 1 * LongestDivided.staircase N with hm
  have hrm : rev m = (-1 : ℤ) ^ pairSum (l + delta N) • m := by
    rw [hm, staircase_eq_monomial, OddSchurPieri.mono_mul, rev_zsmul, rev_monomial_exact,
      smul_comm]
  have hDm := D_rev (N := N) m
  rw [hrm, map_zsmul] at hDm
  have hrev : rev (LongestDivided.D N m) =
      ((-1 : ℤ) ^ N.choose 4 * (-1) ^ pairSum (l + delta N)) •
        SignedPermutation.skewAction (LongestElementary.longest N) (LongestDivided.D N m) := by
    have := congrArg (fun x => ((-1 : ℤ) ^ N.choose 4) •
      SignedPermutation.skewAction (LongestElementary.longest N) x) hDm
    simp only [map_zsmul, LongestElementary.action_involutive, smul_smul,
      (IsSign.pow (N.choose 4)).mul_self, one_smul] at this
    exact this.symm
  have hpar := parityInv_D_of l m (parityInv_mul_staircase l)
  rw [skewAction_longest _ _ hpar] at hrev
  have hD : LongestDivided.D N m = (hatCorr N l * (-1) ^ pairSum l) • twistedHat N l := by
    have hsgn : IsSign (hatCorr N l * (-1) ^ pairSum l) := by
      unfold hatCorr; exact (IsSign.pow _).mul (IsSign.pow _)
    rw [twistedHat_eq_D, smul_smul, hsgn.mul_self, one_smul]
  rw [twisted, rev_zsmul, rev_longestPerm, hrev, map_zsmul, map_zsmul, longestPerm_longestPerm,
    hD, smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [hatCorr, ← pow_add]
  apply MonomialReversal.neg_one_pow_of_even_add
  have F2 := pairSum_add l (delta N)
  have F3 := crossingCount_add_swap l (delta N)
  rw [sum_delta] at F3
  obtain ⟨k5, F5⟩ := MonomialReversal.even_pairSum_add_choose_four N
  have F5' : pairSum (delta N) + N.choose 4 = k5 + k5 := F5
  have F6 : (N+1).choose 4 = N.choose 3 + N.choose 4 := Nat.choose_succ_succ' N 3
  have hsd : stairDot l = ∑ j, l j * delta N j := rfl
  rw [F2, F6, hsd]
  generalize ∑ j, l j * delta N j = S at *
  rw [mul_comm (N.choose 2)]
  generalize (∑ j, l j) * N.choose 2 = M at *
  refine ⟨N.choose 3 + 2 * M + N.choose 4 + pairSum l + k5, ?_⟩
  omega

/-! ## `ψ` of EKL Proposition 4.11 -/

section Pairing

open NilHeckeAction NilHeckeRightBasis ZeroHecke ThickBubble OnhPolynomial
open BoxComplement BoxPartitionCount

variable {n : ℕ}

/-- The polynomial `rev(s_α)` on the window `[0, a)` (`x_0^{α_0}` for `a = 1`, `1` for `a = 0`). -/
def schurQ (n : ℕ) : (a : ℕ) → 0 + a ≤ n+2 → (Fin a → ℕ) → SkewPolynomial (n+2)
  | 0, h, _ => ProjectorRank.place 0 h 1
  | 1, h, α => ProjectorRank.place 0 h (generator 0 ^ α 0)
  | _+2, h, α => ProjectorRank.place 0 h (rev (ThickDots.schur α))

theorem reverse_blockSchur : (a : ℕ) → (h : 0 + a ≤ n+2) → (α : Fin a → ℕ) →
    reverseLinear n (blockSchur n 0 a h α) = polyElem n (schurQ n a h α)
  | 0, h, α => by simp [blockSchur, blockMono, schurQ]
  | 1, h, α => by
    simp only [blockSchur, blockMono, List.finRange_succ, List.finRange_zero, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, schurQ, map_pow, polyElem_generator,
      ProjectorRank.place_generator]
    rw [show reverseLinear n (dot n (shiftFin h 0) ^ α 0) =
      MulOpposite.unop (reverseHom n (dot n (shiftFin h 0) ^ α 0)) from rfl,
      OnhReflection.unop_reverse_dot_pow]
    congr 2
  | m+2, h, α => by
    rw [blockSchur, schurQ, reverse_windowHom, reverse_polyElem, windowHom_polyElem]

theorem schurQ_place : (a : ℕ) → (h : 0 + a ≤ n+2) → (α : Fin a → ℕ) →
    ∃ f : SkewPolynomial a, schurQ n a h α = ProjectorRank.place 0 h f ∧
      (∀ i : Fin (n+1), i.val + 1 < a → AllRankDivided.divided i (schurQ n a h α) = 0)
  | 0, h, _ => ⟨1, rfl, fun i hi => by omega⟩
  | 1, h, α => ⟨_, rfl, fun i hi => by omega⟩
  | m+2, h, α => ⟨_, rfl, fun i hi => divided_place_kernel h
      (rev_mem_kernel (ThickDots.schur_mem_kernel α)) i (by omega) (by omega)⟩

theorem dualQ_place {a : ℕ} : (b : ℕ) → (h : a + b ≤ n+2) → (β : Fin b → ℕ) →
    ∃ f : SkewPolynomial b, dualQ n a b h β = ProjectorRank.place a h f
  | 0, h, _ => ⟨1, by rw [dualQ, map_one]⟩
  | 1, h, β => ⟨generator 0 ^ β 0, by
      rw [dualQ, map_pow, ProjectorRank.place_generator]
      congr 2
      exact Fin.ext (by simp)⟩
  | _+2, _, _ => ⟨_, rfl⟩

/-- `∂_{a,b}`: the action of `ψ(X_{a,b})` (the crossing `X_{a,b}` of (3.41) read backwards). -/
def pdAB (n a b : ℕ) : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) :=
  action n (reverseLinear n (NilCoxeterWords.product (StrandCrossing.crossWord n 0 a b)))

/-- **EKL (4.35) reflected by `ψ`**: for `α ∈ P(a,b)`, `β ∈ P(b,a)`,
`∂_{a,b}(rev(ŝ_β)(y) rev(s_α)(x)) = δ_{β, α̂} (-1)^{bubbleSign a b α}`. -/
theorem pairing {a b : ℕ} (hab : a + b = n+2) {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    pdAB n a b (dualQ n a b (by omega) β * schurQ n a (by omega) α) =
      (if β = hat b α then (-1 : ℤ) ^ bubbleSign a b α else 0) • 1 := by
  obtain ⟨fx, hfx, hkx⟩ := schurQ_place (n := n) a (by omega) α
  obtain ⟨fy, hfy⟩ := dualQ_place (n := n) (a := a) b (by omega) β
  have hspx : ∀ i : Fin (n+1), a ≤ i.val →
      AllRankDivided.divided i (schurQ n a (by omega) α) = 0 := fun i hi => by
    rw [hfx]; exact divided_place_spectator _ _ i (Or.inr (by omega))
  have hspy : ∀ i : Fin (n+1), i.val + 1 < a →
      AllRankDivided.divided i (dualQ n a b (by omega) β) = 0 := fun i hi => by
    rw [hfy]; exact divided_place_spectator _ _ i (Or.inl hi)
  have hQy : ∀ i : Fin (n+1), a ≤ i.val → AllRankDivided.divided i
      (dualQ n a b (by omega) β * schurQ n a (by omega) α) = 0 := fun i hi => by
    rw [AllRankDivided.divided_mul, divided_dualQ _ _ i hi (by omega), hspx i hi,
      ThickDecomposition.skew_zero_mul, ThickDecomposition.skew_mul_zero, add_zero]
  have hQx : ∀ i : Fin (n+1), i.val + 1 < a → AllRankDivided.divided i
      (dualQ n a b (by omega) β * schurQ n a (by omega) α) = 0 := fun i hi => by
    rw [AllRankDivided.divided_mul, hspy i hi, hkx i hi, ThickDecomposition.skew_zero_mul,
      ThickDecomposition.skew_mul_zero, add_zero]
  have h := congrArg (fun u => action n (reverseLinear n u) 1)
    (prop_4_11 (n := n) hab hα hαb hβ hβa)
  simp only [merger, splitter, reverse_mul, map_mul, Module.End.mul_apply, map_zsmul,
    LinearMap.smul_apply] at h
  have h1 : action n (reverseLinear n (projector n)) 1 = 1 :=
    action_reverse_projector_kernel (one_mem _)
  have hE0a1 : action n (reverseLinear n (blockE n 0 a)) 1 = 1 :=
    action_reverse_blockE 1 (fun i _ _ => AllRankDivided.divided_one i)
  have hS : action n (reverseLinear n (blockSchur n 0 a (by omega) α)) 1 =
      schurQ n a (by omega) α := by
    rw [reverse_blockSchur, action_polyElem]
    exact mul_one _
  have hE0aQ : action n (reverseLinear n (blockE n 0 a)) (schurQ n a (by omega) α) =
      schurQ n a (by omega) α := action_reverse_blockE _ (fun i _ h2 => hkx i (by omega))
  have hEabQ : action n (reverseLinear n (blockE n a b)) (schurQ n a (by omega) α) =
      schurQ n a (by omega) α := action_reverse_blockE _ (fun i h1 _ => hspx i h1)
  have hDS : action n (reverseLinear n (blockDualSchur n a b (by omega) β))
      (schurQ n a (by omega) α) = dualQ n a b (by omega) β * schurQ n a (by omega) α :=
    action_reverse_blockDualSchur _ _ _
  have hEabQQ : action n (reverseLinear n (blockE n a b))
      (dualQ n a b (by omega) β * schurQ n a (by omega) α) =
        dualQ n a b (by omega) β * schurQ n a (by omega) α :=
    action_reverse_blockE _ (fun i h1 _ => hQy i h1)
  have hE0aQQ : action n (reverseLinear n (blockE n 0 a))
      (dualQ n a b (by omega) β * schurQ n a (by omega) α) =
        dualQ n a b (by omega) β * schurQ n a (by omega) α :=
    action_reverse_blockE _ (fun i _ h2 => hQx i (by omega))
  simp only [h1, hE0a1, hS, hE0aQ, hEabQ, hDS, hEabQQ, hE0aQQ] at h
  exact h

/-! ### Specializations -/

/-- The partition `(1)` with `a` rows. -/
def eFirst (a : ℕ) : Fin a → ℕ := fun k => if k.val < 1 then 1 else 0

/-- The full rectangle `(a^b)`. -/
def boxP (a b : ℕ) : Fin b → ℕ := fun _ => a

/-- The rectangle minus its corner, `(a^{b-1}, a-1)`. -/
def cornerP (a b : ℕ) : Fin b → ℕ := fun j => if j.val + 1 < b then a else a - 1

theorem hat_zero (a b : ℕ) : hat b (0 : Fin a → ℕ) = boxP a b := by
  funext k
  simp only [hat, boxP, Pi.zero_apply, zero_le, Finset.filter_true, Finset.card_univ,
    Fintype.card_fin]

theorem hat_eFirst {a b : ℕ} (ha : 1 ≤ a) : hat b (eFirst a) = cornerP a b := by
  funext k
  have hk := k.isLt
  simp only [hat, cornerP, eFirst]
  split_ifs with h
  · rw [Finset.filter_true_of_mem (fun j _ => by split_ifs <;> omega), Finset.card_univ,
      Fintype.card_fin]
  · rw [show Finset.univ.filter (fun j : Fin a => (if j.val < 1 then 1 else 0) ≤ b - 1 - k.val) =
        Finset.univ.filter (fun j : Fin a => ¬ j.val < 1) from by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; split_ifs <;> omega]
    have : (Finset.univ.filter fun j : Fin a => j.val < 1) = {⟨0, by omega⟩} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact Fin.ext (by simp; omega)
      · rintro rfl; simp
    rw [Finset.filter_not, Finset.card_sdiff, Finset.inter_univ, this, Finset.card_singleton,
      Finset.card_univ, Fintype.card_fin]

theorem schur_zero_eq {m : ℕ} : ThickDots.schur (0 : Fin (m+2) → ℕ) = 1 := by
  rw [ThickDots.schur, show monomial (0 : Fin (m+2) → ℕ) 1 = (1 : SkewPolynomial (m+2)) from rfl,
    one_mul, LongestDivided.D_staircase, map_zsmul, map_one, smul_smul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_smul]

theorem schurQ_zero {a : ℕ} (h : 0 + a ≤ n+2) : schurQ n a h 0 = 1 := by
  match a, h with
  | 0, h => rw [schurQ, map_one]
  | 1, h => rw [schurQ, Pi.zero_apply, pow_zero, map_one]
  | m+2, h => rw [schurQ, schur_zero_eq, rev_one, map_one]

theorem schurQ_eFirst {a : ℕ} (h : 0 + a ≤ n+2) (ha : 1 ≤ a) :
    schurQ n a h (eFirst a) =
      ProjectorRank.place 0 h (FiniteCompleteElementary.elementaryPoly a 1) := by
  match a, h, ha with
  | 1, h, _ =>
    rw [schurQ, elementaryPoly_one_eq, Fin.sum_univ_one]
    simp [eFirst]
  | m+2, h, _ =>
    have hs : ThickDots.schur (eFirst (m+2)) = FiniteCompleteElementary.elementaryPoly (m+2) 1 := by
      have := OddSchurPieri.schur_column m 1 (by omega)
      rw [← ThickDots.schur_eq_oddSymmetrizer] at this
      rw [show eFirst (m+2) = (OddSchurPieri.column m 1).val from rfl, this,
        show Nat.choose 1 2 = 0 from rfl, pow_zero, one_smul]
    rw [schurQ, hs, rev_elementaryPoly, show Nat.choose 1 2 = 0 from rfl, pow_zero, one_smul]

theorem dualQ_twisted {a b : ℕ} (h : a + b ≤ n+2) (β : Fin b → ℕ) :
    dualQ n a b h β = (-1 : ℤ) ^ (b.choose 4 + (∑ j, β j) * b.choose 2) •
      ProjectorRank.place a h (twisted b β) := by
  match b, h, β with
  | 0, h, β => rw [dualQ, twisted_zero_rank, map_one]; simp
  | 1, h, β =>
    rw [dualQ, twisted_one_rank, map_pow, ProjectorRank.place_generator]
    simp only [show Nat.choose 1 4 = 0 from rfl, show Nat.choose 1 2 = 0 from rfl, mul_zero,
      add_zero, pow_zero, one_smul]
    congr 2
    exact Fin.ext (by simp)
  | m+2, h, β =>
    have h1 := rev_twisted_exact β
    have h2 : twistedHat (m+2) β =
        (-1 : ℤ) ^ ((m+2).choose 4 + (∑ j, β j) * (m+2).choose 2) • rev (twisted (m+2) β) := by
      rw [h1, smul_smul, (IsSign.pow _).mul_self, one_smul]
    rw [dualQ, ← twistedHat_eq_dualSchur, h2, rev_zsmul, rev_rev, map_zsmul]

/-! ### The sign `bubbleSign` for `α = ∅` and `α = (1)` -/

theorem blockChi_eFirst (a : ℕ) : blockChi a (eFirst a) = blockChi a 0 + 2 * a.choose 2 := by
  match a with
  | 0 => rfl
  | 1 => rfl
  | m+2 =>
    simp only [blockChi, ThickDots.chi, Pi.zero_apply, Finset.sum_const_zero, zero_mul,
      add_zero]
    have h1 : ∑ k : Fin (m+2), eFirst (m+2) k = 1 := by
      rw [Fin.sum_univ_succ]; simp [eFirst]
    have h2 : ∑ k : Fin (m+2), eFirst (m+2) k * (m+2-k.val).choose 2 = (m+2).choose 2 := by
      rw [Fin.sum_univ_succ]; simp [eFirst]
    rw [h1, h2]
    ring

theorem sum_cornerP {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∑ j, cornerP a b j + 1 = a * b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  simp only [cornerP, Fin.val_castSucc, Fin.val_last]
  rw [Finset.sum_congr rfl fun k _ => ite_eq_left (by have := k.isLt; omega : k.val + 1 < c + 1),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ite_eq_right (by omega), smul_eq_mul]
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem blockChi_box {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    blockChi b (boxP a b) = blockChi b (cornerP a b) + b.choose 2 := by
  match b, hb with
  | 1, _ => rfl
  | m+2, _ =>
    simp only [blockChi, ThickDots.chi]
    have hs := sum_cornerP (a := a) (b := m+2) ha (by omega)
    have hbox : ∑ k : Fin (m+2), boxP a (m+2) k = a * (m+2) := by simp [boxP, mul_comm]
    have hterm : ∑ k : Fin (m+2), cornerP a (m+2) k * (m+2-k.val).choose 2 =
        ∑ k : Fin (m+2), boxP a (m+2) k * (m+2-k.val).choose 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [cornerP, boxP]
      split_ifs with h
      · rfl
      · rw [show m + 2 - k.val = 1 by have := k.isLt; omega]; rfl
    rw [hterm, hbox]
    rw [show a * (m+2) = ∑ j, cornerP a (m+2) j + 1 from hs.symm]
    ring

theorem omega_box {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    StaircaseEvaluation.omega (boxP a b) = StaircaseEvaluation.omega (cornerP a b) +
      (a-1).choose 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  simp only [StaircaseEvaluation.omega]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrest : ∀ j : Fin c, cornerP a (c+1) (Fin.rev j.succ) = a := fun j => by
    simp only [cornerP, Fin.val_rev, Fin.val_succ]
    rw [ite_eq_left (by have := j.isLt; omega)]
  have h0 : cornerP a (c+1) (Fin.rev 0) = a - 1 := by
    simp only [cornerP, Fin.val_rev, Fin.val_zero]
    rw [ite_eq_right (by omega)]
  simp only [boxP, hrest, h0, Fin.val_zero, zero_add, Fin.val_succ]
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_succ_succ' d 2]
  ring

/-- `bubbleSign a b (1) ≡ bubbleSign a b ∅ + binom(b,2) + a - 1 (mod 2)`, as an identity of
naturals. -/
theorem bubbleSign_eFirst {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    bubbleSign a b 0 + 2 * a.choose 2 =
      bubbleSign a b (eFirst a) + b.choose 2 + a.choose 2 + (a-1).choose 2 := by
  unfold bubbleSign
  rw [hat_zero, hat_eFirst ha, blockChi_eFirst, blockChi_box ha hb, omega_box ha hb]
  have hs := sum_cornerP ha hb
  have hbox : ∑ k : Fin b, boxP a b k = a * b := by simp [boxP, mul_comm]
  rw [hbox, ← hs]
  ring

/-! ### `∂_{a,b}` is right `OΛ̃`-linear and odd of parity `ab` -/

theorem pdAB_eq (a b : ℕ) :
    pdAB n a b = LongestDivided.applyWord (StrandCrossing.crossWord n 0 a b).reverse := by
  rw [pdAB, reverse_product, NilCoxeterWords.action_product]

theorem pdAB_mul_kernel (a b : ℕ) (F : SkewPolynomial (n+2)) {k : SkewPolynomial (n+2)}
    (hk : k ∈ OddSymmetricKernel.kernelSubring n) : pdAB n a b (F * k) = pdAB n a b F * k := by
  rw [pdAB_eq]
  exact LongestDivided.applyWord_right_kernel _ F k hk

theorem length_crossWord {a b : ℕ} (hab : a + b = n+2) :
    (StrandCrossing.crossWord n 0 a b).length = a * b := by
  rw [← List.length_map (f := Fin.val), StrandCrossing.natWord_values n _ fun j hj => by
    have := StrandCrossing.mem_crossList hj; omega, ThickDecomposition.length_crossList]

theorem parityInv_pdAB {a b : ℕ} (hab : a + b = n+2) (F : SkewPolynomial (n+2)) :
    parityInv (n+2) (pdAB n a b F) = (-1 : ℤ) ^ (a * b) • pdAB n a b (parityInv (n+2) F) := by
  rw [pdAB_eq, parityInv_applyWord, List.length_reverse, length_crossWord hab]

end Pairing

/-! ## The trace `z^∨ = θ ∘ ∂_{a,b}` on `Z_{a,b}` -/

section Trace

open BoxComplement BoxPartitionCount ThickBubble

variable {n a b : ℕ}

theorem castHom_rfl (m : ℕ) : castHom (rfl : m = m) = RingHom.id _ :=
  ringHom_ext fun j => by simp

theorem castHom_theta {m m' : ℕ} (h : m = m') (f : SkewPolynomial m) :
    castHom h (theta m f) = theta m' (castHom h f) := by
  subst h; rw [castHom_rfl]; rfl

theorem castHom_longestPerm {m m' : ℕ} (h : m = m') (f : SkewPolynomial m) :
    castHom h (longestPerm m f) = longestPerm m' (castHom h f) := by
  subst h; rw [castHom_rfl]; rfl

theorem castHom_parityInv {m m' : ℕ} (h : m = m') (f : SkewPolynomial m) :
    castHom h (parityInv m f) = parityInv m' (castHom h f) := by
  subst h; rw [castHom_rfl]; rfl

theorem castHom_d {m m' : ℕ} (h : m = m') (f : SkewPolynomial m) :
    castHom h (d m f) = d m' (castHom h f) := by
  subst h; rw [castHom_rfl]; rfl

theorem castHom_twistRev {m m' : ℕ} (h : m = m') (f : SkewPolynomial m) :
    castHom h (twistRev m f) = twistRev m' (castHom h f) := by
  subst h; rw [castHom_rfl]; rfl

/-- Ellis–Qi's trace `z^∨ = θ ∘ ∂_{a,b}` on `Z_{a,b} = OΛ̃_a ⊠ OΛ̃_b · z` (the literal twisted
model), valued in `OPol_{a+b}` written as `OPol_{n+2}`; `∂_{a,b}` is `pdAB` (a reduced expression
of `w_{a,b}`; another reduced expression changes it by a global sign). -/
def trace (hab : a + b = n+2) (G : SkewPolynomial (a+b)) : SkewPolynomial (n+2) :=
  theta (n+2) (pdAB n a b (castHom hab G))

theorem trace_add (hab : a + b = n+2) (F G : SkewPolynomial (a+b)) :
    trace hab (F + G) = trace hab F + trace hab G := by
  simp [trace]

theorem trace_zsmul (hab : a + b = n+2) (k : ℤ) (F : SkewPolynomial (a+b)) :
    trace hab (k • F) = k • trace hab F := by
  rw [trace, map_zsmul, map_zsmul, map_zsmul, trace]

theorem trace_sum (hab : a + b = n+2) {ι : Type*} (s : Finset ι) (F : ι → SkewPolynomial (a+b)) :
    trace hab (∑ i ∈ s, F i) = ∑ i ∈ s, trace hab (F i) := by
  simp [trace, map_sum]

/-- **(4.24): `z^∨` is semilinear.** `z^∨(G z · c) = z^∨(G z) w₀(c)` for `c ∈ OΛ_{a+b}`:
the printed trace `θ ∘ ∂_{a,b}` is right `OΛ_{a+b}`-linear only up to the automorphism `w₀`. -/
theorem trace_mul_twistRev (hab : a + b = n+2) (G : SkewPolynomial (a+b))
    {c : SkewPolynomial (a+b)} (hc : c ∈ osym (a+b)) :
    trace hab (G * twistRev (a+b) c) = trace hab G * longestPerm (n+2) (castHom hab c) := by
  rw [trace, map_mul, pdAB_mul_kernel _ _ _ (castHom_twistRev_mem hab hc), map_mul,
    castHom_twistRev, twistRev, RingHom.comp_apply, theta_theta, trace]

/-- The corrected trace `w₀ ∘ θ ∘ ∂_{a,b}` is right `OΛ_{a+b}`-linear. -/
theorem trace_linear (hab : a + b = n+2) (G : SkewPolynomial (a+b))
    {c : SkewPolynomial (a+b)} (hc : c ∈ osym (a+b)) :
    longestPerm (n+2) (trace hab (G * twistRev (a+b) c)) =
      longestPerm (n+2) (trace hab G) * castHom hab c := by
  rw [trace_mul_twistRev hab G hc, map_mul, longestPerm_longestPerm]

theorem parityInv_trace (hab : a + b = n+2) (G : SkewPolynomial (a+b)) :
    parityInv (n+2) (trace hab G) = (-1 : ℤ) ^ (a * b) • trace hab (parityInv (a+b) G) := by
  rw [trace, parityInv_theta, parityInv_pdAB hab, map_zsmul, trace, castHom_parityInv]

theorem mul_anticomm_step {R : Type*} [Ring R] (x P Q P' Q' : R) (h1 : x * P = P' * x)
    (h2 : x * Q = Q' * x) : x * (P * Q) = (P' * Q') * x := by
  rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem generator_mul_place {j : Fin (n+2)} (hj : j.val < a) (h : a + b ≤ n+2)
    (g : SkewPolynomial b) :
    generator j * ProjectorRank.place a h g =
      ProjectorRank.place a h (parityInv b g) * generator j := by
  induction g using induction_generator with
  | hgen k =>
    rw [ProjectorRank.place_generator, parityInv_generator, map_neg,
      ProjectorRank.place_generator, generator_anticomm _ _ (fun e => by
        have := congrArg Fin.val e; simp at this; omega), neg_mul]
  | h0 => rw [map_zero, map_zero, map_zero, ThickDecomposition.skew_mul_zero,
      ThickDecomposition.skew_zero_mul]
  | h1 => simp
  | hadd f g hf hg => rw [map_add, map_add, map_add, mul_add, add_mul, hf, hg]
  | hneg f hf => rw [map_neg, map_neg, map_neg, mul_neg, neg_mul, hf]
  | hmul f g hf hg =>
    rw [map_mul, map_mul, map_mul]
    exact mul_anticomm_step _ _ _ _ _ hf hg

theorem castHom_eFirst_mul (hab : a + b = n+2) (g : SkewPolynomial b) :
    castHom hab (inclX a b (FiniteCompleteElementary.elementaryPoly a 1) * inclY a b g) =
      ProjectorRank.place a (by omega) (parityInv b g) *
        ProjectorRank.place 0 (by omega) (FiniteCompleteElementary.elementaryPoly a 1) := by
  rw [map_mul, castHom_inclX, castHom_inclY, elementaryPoly_one_eq, map_sum, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, ProjectorRank.place_generator, smul_mul_assoc, mul_smul_comm,
    generator_mul_place (by simp) (by omega)]

theorem theta_smul_one (k : ℤ) : theta (n+2) (k • (1 : SkewPolynomial (n+2))) = k • 1 := by
  rw [map_zsmul, map_one]

open Classical in
/-- `z^∨(s̃_μ(y) z) = δ_{μ,(a^b)} κ` with `κ = ±1` (from (4.35)). -/
theorem trace_sY (hab : a + b = n+2) {μ : Fin b → ℕ} (hμ : μ ∈ box b a) :
    trace hab (inclY a b (twisted b μ)) =
      (if μ = boxP a b then (-1 : ℤ) ^ (b.choose 4 + (a * b) * b.choose 2) *
        (-1) ^ bubbleSign a b 0 else 0) • 1 := by
  have hμb := mem_box.1 hμ
  have hq := dualQ_twisted (n := n) (a := a) (b := b) (by omega) μ
  have hp : ProjectorRank.place a (by omega) (twisted b μ) =
      (-1 : ℤ) ^ (b.choose 4 + (∑ j, μ j) * b.choose 2) •
        (dualQ n a b (by omega) μ * schurQ n a (by omega) 0) := by
    rw [schurQ_zero, mul_one, hq, smul_smul, (IsSign.pow _).mul_self, one_smul]
  rw [trace, castHom_inclY, hp, map_zsmul, pairing hab (α := 0) (fun _ _ _ => le_rfl)
    (fun _ => Nat.zero_le _) hμb.1 hμb.2, hat_zero, smul_smul, theta_smul_one]
  congr 1
  split_ifs with h
  · subst h
    simp [boxP, mul_comm]
  · rw [mul_zero]

open Classical in
/-- `z^∨(ẽ_1(x) s̃_μ(y) z) = δ_{μ,(a^{b-1},a-1)} κ'` (from (4.35)), `ẽ_1(x)` EKL's twisted `e_1`
in the variables `x`. -/
theorem trace_eFirst_sY (hab : a + b = n+2) (ha : 1 ≤ a) (hb : 1 ≤ b) {μ : Fin b → ℕ}
    (hμ : μ ∈ box b a) :
    trace hab (inclX a b (FiniteCompleteElementary.elementaryPoly a 1) *
        inclY a b (twisted b μ)) =
      (if μ = cornerP a b then (-1 : ℤ) ^ (∑ j, μ j) *
        ((-1 : ℤ) ^ (b.choose 4 + (∑ j, μ j) * b.choose 2) *
          (-1) ^ bubbleSign a b (eFirst a)) else 0) • 1 := by
  have hμb := mem_box.1 hμ
  have hq := dualQ_twisted (n := n) (a := a) (b := b) (by omega) μ
  have hα : Antitone (eFirst a) := fun i j hij => by
    have := Fin.le_def.1 hij; simp only [eFirst]; split_ifs <;> omega
  have hαb : ∀ k, eFirst a k ≤ b := fun k => by simp only [eFirst]; split_ifs <;> omega
  have hp : ProjectorRank.place a (by omega) (parityInv b (twisted b μ)) *
      ProjectorRank.place 0 (by omega) (FiniteCompleteElementary.elementaryPoly a 1) =
      ((-1 : ℤ) ^ (∑ j, μ j) * (-1 : ℤ) ^ (b.choose 4 + (∑ j, μ j) * b.choose 2)) •
        (dualQ n a b (by omega) μ * schurQ n a (by omega) (eFirst a)) := by
    rw [schurQ_eFirst _ ha, hq, parityInv_twisted, map_zsmul, smul_mul_assoc, smul_mul_assoc,
      smul_smul, mul_assoc, (IsSign.pow _).mul_self, mul_one]
  rw [trace, castHom_eFirst_mul, hp, map_zsmul, pairing hab hα hαb hμb.1 hμb.2, hat_eFirst ha,
    smul_smul, theta_smul_one]
  congr 1
  split_ifs <;> ring

theorem eq_corner_of_add {μ : Fin b → ℕ} (hμ : Antitone μ) {i : Fin b}
    (h : μ + expSingle i = boxP a b) : μ = cornerP a b ∧ i.val + 1 = b := by
  have hj : ∀ j, μ j + (if i = j then 1 else 0) = a := fun j => congrFun h j
  have hi := hj i
  simp only [ite_true] at hi
  have hlast : i.val + 1 = b := by
    by_contra hne
    have hlt : i.val + 1 < b := by have := i.isLt; omega
    have h2 := hj ⟨i.val + 1, hlt⟩
    rw [ite_eq_right (fun e => by have := congrArg Fin.val e; simp at this)] at h2
    have h3 := hμ (show i ≤ ⟨i.val + 1, hlt⟩ from Fin.le_def.2 (by simp))
    omega
  refine ⟨funext fun j => ?_, hlast⟩
  have h2 := hj j
  simp only [cornerP]
  by_cases hij : i = j
  · subst hij; rw [ite_eq_right (by omega)]; omega
  · rw [ite_eq_right hij] at h2
    rw [ite_eq_left (by
      have : j.val ≠ i.val := fun e => hij (Fin.ext e.symm)
      have := j.isLt; omega)]
    omega

theorem elementaryPoly_zero_one : FiniteCompleteElementary.elementaryPoly 0 1 = 0 := by
  rw [FiniteCompleteElementary.elementaryPoly_eq_strictSum]
  exact FiniteCompleteElementary.FiniteWords.strictSum_empty _ 0

theorem d_smul_one (k : ℤ) : d (n+2) (k • (1 : SkewPolynomial (n+2))) = 0 := by
  rw [map_zsmul, d_one, smul_zero]

open Classical in
/-- Corollary 4.10 on the basis elements `s̃_μ(y) z`. -/
theorem cor_4_10_basis (hab : a + b = n+2) {μ : Fin b → ℕ} (hμ : μ ∈ box b a) :
    d (n+2) (trace hab (inclY a b (twisted b μ))) =
      (-((-1 : ℤ) ^ (a * b) * ((b % 2 : ℕ) : ℤ))) •
          trace hab (inclX a b (FiniteCompleteElementary.elementaryPoly a 1) *
            inclY a b (twisted b μ)) +
        (-1 : ℤ) ^ (a * b) • trace hab (dT a b (inclY a b (twisted b μ))) := by
  have hμb := mem_box.1 hμ
  rw [trace_sY hab hμ, d_smul_one, lemma_4_7_box_twisted μ hμb.1 hμb.2, trace_sum]
  -- the `d`-term
  have hdT : ∀ i, trace hab (if Antitone (μ + expSingle i) ∧ μ i < a then
      ((-1 : ℤ) ^ (rowsAbove μ i + i.val) * (((a : ℤ) + content μ i) % 2)) •
        inclY a b (twisted b (μ + expSingle i)) else 0) =
      (if Antitone (μ + expSingle i) ∧ μ i < a ∧ μ + expSingle i = boxP a b then
        ((-1 : ℤ) ^ (rowsAbove μ i + i.val) * (((a : ℤ) + content μ i) % 2)) *
          ((-1 : ℤ) ^ (b.choose 4 + (a * b) * b.choose 2) * (-1) ^ bubbleSign a b 0)
       else 0) • 1 := by
    intro i
    split_ifs with h1 h2 h2
    · rw [trace_zsmul, trace_sY hab (mem_box.2 ⟨h1.1, add_box_mem hμb.2 h1⟩), ite_eq_left h2.2.2,
        smul_smul]
    · rw [trace_zsmul, trace_sY hab (mem_box.2 ⟨h1.1, add_box_mem hμb.2 h1⟩),
        ite_eq_right (fun e => h2 ⟨h1.1, h1.2, e⟩), zero_smul, smul_zero]
    · exact absurd ⟨h2.1, h2.2.1⟩ h1
    · rw [trace, map_zero, map_zero, map_zero, zero_smul]
  simp only [hdT]
  rw [← Finset.sum_smul]
  by_cases hab1 : 1 ≤ a ∧ 1 ≤ b
  · rw [trace_eFirst_sY hab hab1.1 hab1.2 hμ]
    by_cases hc : μ = cornerP a b
    · subst hc
      obtain ⟨ha, hb⟩ := hab1
      set i₀ : Fin b := ⟨b - 1, by omega⟩ with hi₀
      have hci₀ : cornerP a b i₀ = a - 1 := by
        simp only [cornerP, hi₀]; rw [ite_eq_right (by omega)]
      have hbox : cornerP a b + expSingle i₀ = boxP a b := by
        funext j
        simp only [Pi.add_apply, boxP, expSingle]
        by_cases hj : i₀ = j
        · subst hj; rw [hci₀, ite_eq_left rfl]; omega
        · rw [ite_eq_right hj]
          simp only [cornerP]
          rw [ite_eq_left (by
            have : j.val ≠ b - 1 := fun e => hj (Fin.ext (by simp [hi₀, e]))
            have := j.isLt; omega), add_zero]
      have hcond : Antitone (cornerP a b + expSingle i₀) ∧ cornerP a b i₀ < a ∧
          cornerP a b + expSingle i₀ = boxP a b :=
        ⟨by rw [hbox]; exact fun _ _ _ => le_rfl, by rw [hci₀]; omega, hbox⟩
      rw [Finset.sum_eq_single i₀ (fun i _ hi => ite_eq_right fun h => hi (Fin.ext (by
          have := (eq_corner_of_add hμb.1 h.2.2).2; simp only [hi₀]; omega)))
        (by simp), ite_eq_left hcond, ite_eq_left rfl, smul_smul, smul_smul, ← add_smul,
        eq_comm, ← zero_smul ℤ (1 : SkewPolynomial (n+2))]
      congr 1
      have hrA : rowsAbove (cornerP a b) i₀ = a * (b - 1) := by
        rw [rowsAbove, Finset.sum_congr rfl (g := fun _ => a) (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp only [cornerP]
          rw [ite_eq_left (by have := Fin.lt_def.1 hj; simp only [hi₀] at this; omega)]),
          Finset.sum_const, smul_eq_mul, mul_comm]
        congr 1
        rw [show Finset.univ.filter (· < i₀) = Finset.Iio i₀ from by ext; simp, Fin.card_Iio]
      have hct : ((a : ℤ) + content (cornerP a b) i₀) % 2 = ((b % 2 : ℕ) : ℤ) := by
        rw [content, hci₀]; simp only [hi₀]; omega
      have hi0v : i₀.val = b - 1 := rfl
      rw [hrA, hct, hi0v]
      have hbub := bubbleSign_eFirst ha hb
      have hsum := sum_cornerP ha hb
      have hC : a.choose 2 = (a-1).choose 2 + (a - 1) := by
        obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
        rw [choose_two_succ, Nat.add_sub_cancel]
      rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
      · rw [hb2]; simp
      · rw [hb2]
        have key : (-1 : ℤ) ^ (∑ j, cornerP a b j) *
            ((-1 : ℤ) ^ (b.choose 4 + (∑ j, cornerP a b j) * b.choose 2) *
              (-1) ^ bubbleSign a b (eFirst a)) =
            (-1 : ℤ) ^ (a * (b - 1) + (b - 1)) *
              ((-1 : ℤ) ^ (b.choose 4 + a * b * b.choose 2) * (-1) ^ bubbleSign a b 0) := by
          simp only [← pow_add]
          apply MonomialReversal.neg_one_pow_of_even_add
          have hS : a * (b - 1) + a = a * b := by
            obtain ⟨e, rfl⟩ : ∃ e, b = e + 1 := ⟨b - 1, by omega⟩
            simp only [Nat.add_sub_cancel]; ring
          have hR : (∑ j, cornerP a b j) * b.choose 2 + b.choose 2 = a * b * b.choose 2 := by
            rw [← hsum]; ring
          have hP : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
          generalize (∑ j, cornerP a b j) * b.choose 2 = R' at *
          generalize a * b * b.choose 2 = R at *
          generalize a * (b - 1) = S at *
          generalize a * b = P at *
          generalize ∑ j, cornerP a b j = T at *
          rw [Nat.even_iff]
          omega
        simp only [Nat.cast_one, mul_one]
        linear_combination (-(-1 : ℤ) ^ (a * b)) * key
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hc), zero_smul, smul_zero, zero_add,
        Finset.sum_eq_zero fun i _ => ite_eq_right_iff.mpr fun h =>
          absurd (eq_corner_of_add hμb.1 h.2.2).1 hc, zero_smul, smul_zero]
  · rcases not_and_or.mp hab1 with ha | hb
    · obtain rfl : a = 0 := by omega
      rw [elementaryPoly_zero_one, map_zero, ThickDecomposition.skew_zero_mul]
      simp only [trace, map_zero, smul_zero, zero_add]
      rw [Finset.sum_eq_zero fun i _ => ite_eq_right fun h => by omega, zero_smul, smul_zero]
    · obtain rfl : b = 0 := by omega
      simp

theorem cor_4_10_aux {R : Type*} [Ring R] (s t : ℤ) (A B C W W' : R) :
    (s • A + t • B) * W + (t • C) * W' = s • (A * W) + t • (B * W + C * W') := by
  simp only [add_mul, smul_mul_assoc, smul_add]
  abel

/-- **Ellis–Qi, Corollary 4.10** (exact signs, as printed): for every `G z ∈ Z_{a,b}`
(`G ∈ OΛ̃_a ⊠ OΛ̃_b`, the literal twisted model with the differential `dT` of Definition 4.6),
`d(z^∨(G z)) = d(z^∨)(G z) + (-1)^{ab} z^∨(d(G z))` with
`d(z^∨) = (-1)^{ab-1} {b} z^∨ ẽ_1(x)` (Definition 4.9), i.e.
`d(z^∨(G z)) = -(-1)^{ab}{b} z^∨(ẽ_1(x) G z) + (-1)^{ab} z^∨(d(G z))`, where `z^∨ = θ ∘ ∂_{a,b}`
(`trace`) and `ẽ_1(x)` is EKL's twisted `e_1` in the variables `x`. -/
theorem cor_4_10 (hab : a + b = n+2) {G : SkewPolynomial (a+b)} (hG : G ∈ tosymAB a b) :
    d (n+2) (trace hab G) =
      (-((-1 : ℤ) ^ (a * b) * ((b % 2 : ℕ) : ℤ))) •
          trace hab (inclX a b (FiniteCompleteElementary.elementaryPoly a 1) * G) +
        (-1 : ℤ) ^ (a * b) • trace hab (dT a b G) := by
  obtain ⟨c, hc, rfl⟩ := zab_span_twisted hG
  rw [Finset.mul_sum, map_sum, trace_sum, trace_sum, trace_sum, map_sum, Finset.smul_sum,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  set F := inclY a b (twisted b μ)
  have hF : F ∈ tosymAB a b := ⟨inclY a b (untwisted b μ), sY_mem μ, tauAB_inclY_untwisted μ⟩
  have hassoc : inclX a b (FiniteCompleteElementary.elementaryPoly a 1) *
      (F * twistRev (a+b) (c μ)) =
      inclX a b (FiniteCompleteElementary.elementaryPoly a 1) * F * twistRev (a+b) (c μ) :=
    (OddMath.SkewPolynomial.mul_assoc _ _ _).symm
  rw [hassoc, trace_mul_twistRev hab _ (hc μ), trace_mul_twistRev hab _ (hc μ), dT_right,
    trace_add, trace_mul_twistRev hab _ (hc μ), trace_mul_twistRev hab _ (d_mem_osym (hc μ)),
    d_mul, d_longestPerm_N, ← castHom_d, cor_4_10_basis hab hμ, parityInv_trace hab]
  exact cor_4_10_aux _ _ _ _ _ _ _

/-! ### The printed `z^∨` is not right linear -/

theorem longestPerm_elementary (N k : ℕ) :
    longestPerm N (elementary N k) = (-1 : ℤ) ^ k.choose 2 • elementary N k := by
  open PlacticEvaluation SignedPermutation LongestElementary in
  have hc : (fun j : Fin N => twistRev N (generator j)) = fun j =>
      (-1 : ℤ) ^ ((N-1).choose 2) • (skewAction (longest N)).toRingHom (tildeGenerator j) := by
    funext j
    change _ = _ • skewAction (longest N) (tildeGenerator j)
    rw [action_tilde, smul_smul, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_smul, twistRev_generator]
    rfl
  open PlacticEvaluation SignedPermutation LongestElementary in
  have htw : twistRev N (elementary N k) =
      ((-1 : ℤ) ^ ((N-1).choose 2)) ^ k •
        skewAction (longest N) (FiniteCompleteElementary.elementaryPoly N k) := by
    rw [elementary, ringHom_strictSum, hc, strictSum_zsmul, ← ringHom_strictSum,
      ← FiniteCompleteElementary.elementaryPoly_eq_strictSum]
    rfl
  have hw : longestPerm N (elementary N k) = theta N (twistRev N (elementary N k)) := by
    rw [twistRev, RingHom.comp_apply, EQSchur.theta_theta]
  rw [hw, htw, LongestElementary.action_elementary, smul_smul, map_zsmul, ← theta_elementary,
    EQSchur.theta_theta]
  congr 1
  rw [← pow_mul, ← pow_add, show (N-1).choose 2 * k + (k.choose 2 + k * (N-1).choose 2) =
    k.choose 2 + 2 * (k * (N-1).choose 2) by ring, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- The Pauli-type matrices `X`, `Z` anticommute and `X Z ≠ 0`. -/
def pauli (N : ℕ) (j : Fin N) : Matrix (Fin 2) (Fin 2) ℤ :=
  if j.val = 0 then !![0, 1; 1, 0] else if j.val = 1 then !![1, 0; 0, -1] else 0

theorem pauli_anticomm {N : ℕ} (i j : Fin N) (h : i ≠ j) :
    pauli N i * pauli N j + pauli N j * pauli N i = 0 := by
  have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
  unfold pauli
  split_ifs <;> first | omega | (ext p q; fin_cases p <;> fin_cases q <;> simp)

theorem elementary_two_ne_zero {N : ℕ} (hN : 2 ≤ N) : elementary N 2 ≠ (0 : SkewPolynomial N) := by
  intro h
  have h1 := congrArg (skewLift (pauli N) pauli_anticomm) h
  rw [elementary, ringHom_strictSum, map_zero] at h1
  simp only [skewLift_generator] at h1
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hz : ∀ k, FiniteCompleteElementary.FiniteWords.strictSum
      (fun i : Fin m => pauli (m+2) i.succ.succ) (k+1) = 0 := fun k => by
    have e : (fun i : Fin m => pauli (m+2) i.succ.succ) =
        fun i : Fin m => (0 : ℤ) • pauli (m+2) i.succ.succ := by
      funext i; simp [pauli]
    rw [e, strictSum_zsmul, zero_pow (Nat.succ_ne_zero k), zero_smul]
  have hs1 : FiniteCompleteElementary.FiniteWords.strictSum
      (fun i : Fin (m+1) => pauli (m+2) i.succ) 1 = pauli (m+2) 1 := by
    rw [FiniteCompleteElementary.FiniteWords.strictSum_succ, hz 0,
      FiniteCompleteElementary.FiniteWords.strictSum_zero, mul_one, add_zero]
    rfl
  have hs2 : FiniteCompleteElementary.FiniteWords.strictSum
      (fun i : Fin (m+1) => pauli (m+2) i.succ) 2 = 0 := by
    rw [FiniteCompleteElementary.FiniteWords.strictSum_succ, hz 0, hz 1, mul_zero, add_zero]
  rw [FiniteCompleteElementary.FiniteWords.strictSum_succ, hs1, hs2, add_zero] at h1
  have := congrFun (congrFun h1 0) 1
  simp [pauli, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- **(4.24): the printed trace `z^∨ = θ ∘ ∂_{a,b}` is not right `OΛ_{a+b}`-linear**:
`z^∨(s̃_{(a^b)}(y) z · e_2) ≠ z^∨(s̃_{(a^b)}(y) z) e_2`. By `trace_mul_twistRev`
it is semilinear, and by `trace_linear` the trace `w₀ ∘ θ ∘ ∂_{a,b}` is linear. -/
theorem trace_not_linear (hab : a + b = n+2) :
    ¬ ∀ G ∈ tosymAB a b, ∀ c ∈ osym (a+b),
      trace hab (G * twistRev (a+b) c) = trace hab G * castHom hab c := by
  intro h
  have hbox : boxP a b ∈ box b a := mem_box.2 ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have hG : inclY a b (twisted b (boxP a b)) ∈ tosymAB a b :=
    ⟨inclY a b (untwisted b (boxP a b)), sY_mem _, tauAB_inclY_untwisted _⟩
  have h1 := h _ hG (elementary (a+b) 2) (elementary_mem _ 2)
  rw [trace_mul_twistRev hab _ (elementary_mem _ 2), trace_sY hab hbox, ite_eq_left rfl,
    ← castHom_longestPerm, longestPerm_elementary,
    show Nat.choose 2 2 = 1 from rfl, pow_one, neg_one_smul, map_neg] at h1
  set K : ℤ := (-1 : ℤ) ^ (b.choose 4 + a * b * b.choose 2) * (-1) ^ bubbleSign a b 0
  have hK : K * K = 1 := ((IsSign.pow _).mul (IsSign.pow _)).mul_self
  have h2 : castHom hab (elementary (a+b) 2) = 0 := by
    have h3 : (K • (1 : SkewPolynomial (n+2))) * -castHom hab (elementary (a+b) 2) =
        (K • 1) * castHom hab (elementary (a+b) 2) := h1
    rw [smul_mul_assoc, smul_mul_assoc, one_mul, one_mul] at h3
    have h4 := congrArg (fun x => K • x) h3
    simp only [smul_smul, hK, one_smul] at h4
    ext m
    have := congrArg (fun f : SkewPolynomial (n+2) => f m) h4
    simp at this
    simp
    omega
  exact elementary_two_ne_zero (by omega) (castHom_injective hab (h2.trans (map_zero _).symm))

end Trace

end

end OddMath.Frontier.EQZab
