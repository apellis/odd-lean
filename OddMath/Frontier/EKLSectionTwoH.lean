import OddMath.Frontier.IntervalAnnihilation
import OddMath.Frontier.EKLSectionTwoE
import OddMath.Frontier.MonomialReversal
import OddMath.Frontier.SchubertBasis
import OddMath.Frontier.NilHeckeGradedEnd
import OddMath.Frontier.ElementaryBasis
import Mathlib.LinearAlgebra.FreeModule.PID

/-! EKL arXiv:1111.1320v1, §2.1–2.3: Corollary 2.6 at `a = 2` (p.8), the displays (2.49)–(2.51)
in the proof of Proposition 2.13 (p.12), the rank formula (2.53) (p.13) for `OPol_a` over `OΛ_a`,
and the subclaim (2.63) in the proof of Lemma 2.20 (p.16).

* (2.63) holds for all `g, h ∈ OΛ_a` and `1 ≤ ℓ ≤ j-i` (`eq_2_63`), from (2.62)
  (`IntervalAnnihilation.annihilate`) by the recursion of Step 3.
* (2.49) as printed (`Σ_{k=1}^{a-1}`) fails: `1` is not in the span (`eq_2_49_printed_fails`);
  likewise the printed (2.50) (`eq_2_50_printed_fails`). With the sums starting at `0` both hold
  (`eq_2_49_sum_from_zero`, `eq_2_50_sum_from_zero`); the first equality of (2.50) holds
  (`eq_2_50_first`), and (2.51) holds as printed (`eq_2_51`).
* The printed step (2.50) → (2.51) uses `h x_{a-1}^i ∈ H_{a-1}` for `h ∈ H_{a-2}`, false for
  (2.46) (`x_2 ∉ H_2 = span{1, x_1}`), true for the reversed staircase
  `H'_m = span{x^A : A_i ≤ i-1}` (one-based), with which (2.49) and (2.50) also hold
  (`eq_2_49_reversed`, `eq_2_50_reversed`). `eq_2_49_sum_from_zero` is instead obtained by
  first-variable elimination over the reversed staircase (`first_span_general`), transported by
  the longest element and the reversal anti-automorphism.
* (2.53) is a general statement about graded free modules; for `A = OΛ_a`, `M = OPol_a`
  (right module, Schubert basis in degrees `2ℓ(w)`) its coefficientwise form is `eq_2_53`.
* Corollary 2.6 at `a = 2`, with `OΛ₂ = ker ∂₁` and `OΛ₁ = OPol₁` (`cor_2_6_rank_two`). -/

namespace OddMath.Frontier.EKLSectionTwo
open OddMath.SkewPolynomial (SkewPolynomial generator)
open NonadjacentDivided
noncomputable section

/-! ### (2.63) -/

section Subclaim
variable {n : ℕ}

/-- The adjacent sign action `s_t` on `x_t, x_{t+1}` (zero-based), identity out of range. -/
def sN (t : ℕ) : SkewPolynomial (n+2) ≃+* SkewPolynomial (n+2) :=
  if h : t + 1 < n + 2 then s ⟨t, by omega⟩ ⟨t+1, h⟩ else RingEquiv.refl _

/-- The adjacent divided difference `∂_t` on `x_t, x_{t+1}` (zero-based), zero out of range. -/
def dN (t : ℕ) : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) :=
  if h : t + 1 < n + 2 then
    dividedPair ⟨t, by omega⟩ ⟨t+1, h⟩ (fun e => by simp [Fin.ext_iff] at e)
  else 0

/-- `s_a s_{a+1} ⋯ s_{a+k-1}`, the last acting first. -/
def sChain (a : ℕ) : ℕ → (SkewPolynomial (n+2) ≃+* SkewPolynomial (n+2))
  | 0 => RingEquiv.refl _
  | k+1 => (sChain (a+1) k).trans (sN a)

/-- `∂_a ∂_{a+1} ⋯ ∂_{a+k-1}`, the last acting first. -/
def dChain (a : ℕ) : ℕ → (SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2))
  | 0 => LinearMap.id
  | k+1 => (dN a).comp (dChain (a+1) k)

@[simp] theorem sChain_zero (a : ℕ) (f : SkewPolynomial (n+2)) : sChain a 0 f = f := rfl
@[simp] theorem sChain_succ (a k : ℕ) (f : SkewPolynomial (n+2)) :
    sChain a (k+1) f = sN a (sChain (a+1) k f) := rfl
@[simp] theorem dChain_zero (a : ℕ) (f : SkewPolynomial (n+2)) : dChain a 0 f = f := rfl
@[simp] theorem dChain_succ (a k : ℕ) (f : SkewPolynomial (n+2)) :
    dChain a (k+1) f = dN a (dChain (a+1) k f) := rfl

theorem dChain_succ' (a k : ℕ) (f : SkewPolynomial (n+2)) :
    dChain a (k+1) f = dChain a k (dN (a+k) f) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [dChain_succ, ih (a+1), dChain_succ, show a + 1 + k = a + (k+1) by omega]

theorem dN_eq (t : ℕ) (h : t + 1 < n + 2) :
    (dN t : SkewPolynomial (n+2) →ₗ[ℤ] _) =
      dividedPair ⟨t, by omega⟩ ⟨t+1, h⟩ (fun e => by simp [Fin.ext_iff] at e) := by
  rw [dN, dif_pos h]

theorem sN_eq (t : ℕ) (h : t + 1 < n + 2) :
    (sN t : SkewPolynomial (n+2) ≃+* _) = s ⟨t, by omega⟩ ⟨t+1, h⟩ := by
  rw [sN, dif_pos h]

theorem dN_eq_divided (t : ℕ) (h : t < n + 1) :
    (dN t : SkewPolynomial (n+2) →ₗ[ℤ] _) = AllRankDivided.divided ⟨t, h⟩ := by
  rw [dN_eq t (by omega), ← adjacent]
  rfl

theorem dChain_eq_ascending (a k : ℕ) (h : a + k ≤ n + 1) (f : SkewPolynomial (n+2)) :
    dChain a k f = IntervalAnnihilation.ascending a k h f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [dChain_succ', ih, IntervalAnnihilation.ascending_succ, dN_eq_divided]

/-- The Leibniz rule for `∂_t`. -/
theorem dN_mul (t : ℕ) (h : t + 1 < n + 2) (f g : SkewPolynomial (n+2)) :
    dN t (f * g) = dN t f * g + sN t f * dN t g := by
  rw [dN_eq t h, sN_eq t h, divided_mul]

/-- `∂_p (s_c ⋯ s_{c+k-1} Y) = (-1)^k s_c ⋯ s_{c+k-1} ∂_{p,c+k} Y` for `p < c`. -/
theorem divided_sChain (p c k : ℕ) (hpc : p < c) (hk : c + k < n + 2)
    (Y : SkewPolynomial (n+2)) :
    dividedPair ⟨p, by omega⟩ ⟨c, by omega⟩ (fun e => by simp [Fin.ext_iff] at e; omega)
        (sChain c k Y) =
      (-1 : ℤ) ^ k • sChain c k
        (dividedPair ⟨p, by omega⟩ ⟨c+k, hk⟩ (fun e => by simp [Fin.ext_iff] at e; omega) Y) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    rw [sChain_succ, sN_eq c (by omega), covariance _ _ _ _ _ (by simp [Fin.ext_iff])]
    have h1 : Equiv.swap (⟨c, by omega⟩ : Fin (n+2)) ⟨c+1, by omega⟩ ⟨p, by omega⟩ = ⟨p, by omega⟩ :=
      Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
    have h2 : Equiv.swap (⟨c, by omega⟩ : Fin (n+2)) ⟨c+1, by omega⟩ ⟨c, by omega⟩ =
        ⟨c+1, by omega⟩ := Equiv.swap_apply_left _ _
    simp only [h1, h2]
    rw [ih (c+1) (by omega) (by omega), map_zsmul, sChain_succ, sN_eq c (by omega),
      pow_succ, mul_neg_one, neg_smul]
    simp only [show c + 1 + k = c + (k+1) by omega]

/-- `∂_q` anticommutes with a disjoint `s_{u,v}`. -/
theorem dN_s (q : ℕ) (hq : q + 1 < n + 2) (u v : Fin (n+2))
    (hu : u.val ≠ q) (hu' : u.val ≠ q + 1) (hv : v.val ≠ q) (hv' : v.val ≠ q + 1)
    (huv : u ≠ v) (Y : SkewPolynomial (n+2)) :
    dN q (s u v Y) = -s u v (dN q Y) := by
  rw [dN_eq q hq]
  exact covariance_disjoint _ _ _ _ _ huv (by simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega) Y

/-- `∂_q` anticommutes with a disjoint `∂_{u,v}`. -/
theorem dN_divided (q : ℕ) (hq : q + 1 < n + 2) (u v : Fin (n+2))
    (hu : u.val ≠ q) (hu' : u.val ≠ q + 1) (hv : v.val ≠ q) (hv' : v.val ≠ q + 1)
    (huv : u ≠ v) (Y : SkewPolynomial (n+2)) :
    dN q (dividedPair u v huv Y) = -dividedPair u v huv (dN q Y) := by
  rw [dN_eq q hq]
  exact anticommutation _ _ _ _ _ huv (by simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega) Y

theorem dN_sChain (q c k : ℕ) (hqc : q + 1 < c) (hk : c + k < n + 2) (Y : SkewPolynomial (n+2)) :
    dN q (sChain c k Y) = (-1 : ℤ) ^ k • sChain c k (dN q Y) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    rw [sChain_succ, sN_eq c (by omega), dN_s q (by omega) _ _ (by simp; omega) (by simp; omega)
      (by simp; omega) (by simp; omega) (by simp [Fin.ext_iff]), ← sN_eq c (by omega),
      ih (c+1) (by omega) (by omega), map_zsmul, sChain_succ, pow_succ, mul_neg_one, neg_smul]

theorem dN_dChain (q c k : ℕ) (hqc : q + 1 < c) (hk : c + k < n + 2) (Y : SkewPolynomial (n+2)) :
    dN q (dChain c k Y) = (-1 : ℤ) ^ k • dChain c k (dN q Y) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    rw [dChain_succ, dN_eq c (by omega), dN_divided q (by omega) _ _ (by simp; omega)
      (by simp; omega) (by simp; omega) (by simp; omega), ← dN_eq c (by omega),
      ih (c+1) (by omega) (by omega), map_zsmul, dChain_succ, pow_succ, mul_neg_one, neg_smul]

/-- Chains of divided differences pass through a factor they annihilate. -/
theorem dChain_mul_right (a m : ℕ) (ha : a + m < n + 2) (Z D : SkewPolynomial (n+2))
    (hD : ∀ q, a ≤ q → q < a + m → dN q D = 0) :
    dChain a m (Z * D) = dChain a m Z * D := by
  induction m generalizing Z with
  | zero => rfl
  | succ m ih =>
    rw [dChain_succ', dN_mul (a+m) (by omega), hD (a+m) (by omega) (by omega), mul_zero, add_zero,
      ih (by omega) _ (fun q h1 h2 => hD q h1 (by omega)), dChain_succ']

theorem dividedPair_congr {a a' b b' : Fin (n+2)} (ha : a = a') (hb : b = b') (h : a ≠ b)
    (h' : a' ≠ b') : dividedPair a b h = dividedPair a' b' h' := by
  subst ha; subst hb; rfl

/-- A chain of divided differences disjoint from `s_{u,v}` and `s_c ⋯ s_{c+r-1}` passes through
them up to sign. -/
theorem dChain_sChain_s (a m c r : ℕ) (u v : Fin (n+2)) (huv : u ≠ v) (hac : a + m < c)
    (hcr : c + r < n + 2) (hu : u.val < a) (hv : a + m < v.val) (Z : SkewPolynomial (n+2)) :
    ∃ ε : ℤ, dChain a m (sChain c r (s u v Z)) = ε • sChain c r (s u v (dChain a m Z)) := by
  induction m generalizing Z with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨ε, hε⟩ := ih (by omega) (by omega) (dN (a+m) Z)
    refine ⟨-((-1 : ℤ) ^ r) * ε, ?_⟩
    rw [dChain_succ', dN_sChain (a+m) c r (by omega) hcr,
      dN_s (a+m) (by omega) u v (by omega) (by omega) (by omega) (by omega) huv,
      map_neg (sChain c r), map_zsmul (dChain a m), map_neg (dChain a m), hε, dChain_succ']
    simp only [smul_neg, smul_smul, neg_mul, neg_smul]

theorem dN_kernel (q : ℕ) (hq : q + 1 < n + 2) (f : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) : dN q f = 0 := by
  rw [dN_eq_divided q (by omega)]
  exact hf _

/-- EKL (2.63), zero-based: for `g, h ∈ OΛ_a` (`a = n+2`), zero-based indices `U < V` and
`U + 1 + m + r = V` (the source's one-based `i = U+1`, `j = V+1`, `ℓ = r+1`, `1 ≤ ℓ ≤ j-i`):
`∂_{i+1}⋯∂_{j-ℓ}(s_{j-ℓ+1}⋯s_{j-1}s_{i,j}(g) · ∂_{j-ℓ+1}⋯∂_{j-1}∂_{i,j}(h)) = 0`. -/
theorem eq_2_63 (U V : Fin (n+2)) (hUV : U ≠ V) (g h : SkewPolynomial (n+2))
    (hg : g ∈ OddSymmetricKernel.kernelSubring n) (hh : h ∈ OddSymmetricKernel.kernelSubring n)
    (m r : ℕ) (hmr : U.val + 1 + m + r = V.val) :
    dChain (U.val+1) m
      (sChain (U.val+1+m) r (s U V g) * dChain (U.val+1+m) r (dividedPair U V hUV h)) = 0 := by
  have hV := V.isLt
  induction m generalizing r with
  | zero =>
    have hi := IntervalAnnihilation.annihilate U V (by rw [Fin.lt_def]; omega) h hh
    simp only [IntervalAnnihilation.interval, LinearMap.comp_apply] at hi
    rw [← dChain_eq_ascending] at hi
    simp only [show V.val - (U.val + 1) = r by omega] at hi
    simp only [dChain_zero, add_zero]
    rw [hi, mul_zero]
  | succ m ih =>
    have hp : U.val + 1 + m + 1 < n + 2 := by omega
    rw [dChain_succ', dN_mul (U.val+1+m) hp, map_add]
    have h2 := ih (r+1) (by omega)
    rw [sChain_succ, dChain_succ] at h2
    rw [show U.val + 1 + (m + 1) = U.val + 1 + m + 1 by omega, h2, add_zero]
    have hD : ∀ q, U.val + 1 ≤ q → q < U.val + 1 + m →
        dN q (dChain (U.val+1+m+1) r (dividedPair U V hUV h)) = 0 := by
      intro q hq1 hq2
      rw [dN_dChain q _ r (by omega) (by omega), dN_divided q (by omega) U V
        (by omega) (by omega) (by omega) (by omega),
        dN_kernel q (by omega) h hh, map_zero, neg_zero, map_zero, smul_zero]
    rw [dChain_mul_right (U.val+1) m (by omega) _ _ hD]
    have hPU : (⟨U.val+1+m, by omega⟩ : Fin (n+2)) ≠ U := fun e => by
      have := congrArg Fin.val e; simp only [Fin.val_mk] at this; omega
    have hS : dN (U.val+1+m) (sChain (U.val+1+m+1) r (s U V g)) =
        (-1 : ℤ) ^ r • sChain (U.val+1+m+1) r (-s U V (dividedPair _ U hPU g)) := by
      rw [dN_eq (U.val+1+m) hp, divided_sChain (U.val+1+m) (U.val+1+m+1) r (by omega) (by omega)]
      congr 2
      have hPV : (⟨U.val+1+m, by omega⟩ : Fin (n+2)) ≠ V := fun e => by
        have := congrArg Fin.val e; simp only [Fin.val_mk] at this; omega
      rw [dividedPair_congr rfl (show (⟨U.val+1+m+1+r, by omega⟩ : Fin (n+2)) = V from
        Fin.ext (by simp only [Fin.val_mk]; omega)) _ hPV]
      rw [covariance _ _ _ _ _ hUV]
      have h1 : Equiv.swap U V ⟨U.val+1+m, by omega⟩ = ⟨U.val+1+m, by omega⟩ :=
        Equiv.swap_apply_of_ne_of_ne hPU hPV
      simp only [h1, Equiv.swap_apply_right]
    rw [hS, map_zsmul, map_neg]
    obtain ⟨ε, hε⟩ := dChain_sChain_s (U.val+1) m (U.val+1+m+1) r U V hUV (by omega) (by omega)
      (by omega) (by omega) (dividedPair _ U hPU g)
    have hz : dChain (U.val+1) m (dividedPair _ U hPU g) = 0 := by
      have hi := IntervalAnnihilation.annihilate U ⟨U.val+1+m, by omega⟩
        (by rw [Fin.lt_def]; simp only [Fin.val_mk]; omega) g hg
      simp only [IntervalAnnihilation.interval, LinearMap.comp_apply] at hi
      rw [← dChain_eq_ascending] at hi
      simp only [Fin.val_mk, show U.val + 1 + m - (U.val + 1) = m by omega] at hi
      rw [symmetric]
      exact hi
    rw [map_neg, hε, hz, map_zero, map_zero, smul_zero, neg_zero, smul_zero, zero_mul]

end Subclaim

/-! ### Corollary 2.6 at `a = 2` -/

/-- `OPol_N` is generated as a ring by `x_1, …, x_N`. -/
theorem closure_generators (N : ℕ) :
    Subring.closure (Set.range (generator : Fin N → SkewPolynomial N)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  clear ‹f ∈ ⊤›
  induction f using Finsupp.induction_linear with
  | zero => exact Subring.zero_mem _
  | add f g hf hg => exact Subring.add_mem _ hf hg
  | single a c =>
    change OddMath.SkewPolynomial.monomial a c ∈ _
    rw [MonomialReversal.monomial_eq_smul_prod]
    refine Subring.zsmul_mem _ (Subring.list_prod_mem _ fun x hx => ?_) c
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact Subring.pow_mem _ (Subring.subset_closure (Set.mem_range_self j)) _

/-- EKL Corollary 2.6 at `a = 2`, with `OΛ₂` the kernel of `∂₁` and `OΛ₁ = OPol₁`:
`OΛ₂[x₂] = OΛ₁[x₂]` inside `OPol₂` (both are all of `OPol₂`). -/
theorem cor_2_6_rank_two :
    Subring.closure ((OddSymmetricKernel.kernelSubring 0 : Set (SkewPolynomial 2)) ∪
        {generator (Fin.last 1)}) =
      Subring.closure (Set.range (ElementaryBranching.«prefix» 1) ∪ {generator (Fin.last 1)}) := by
  have hR : Subring.closure (Set.range (ElementaryBranching.«prefix» 1) ∪
      {generator (Fin.last 1)}) = ⊤ := by
    rw [eq_top_iff, ← closure_generators 2, Subring.closure_le]
    rintro _ ⟨j, rfl⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact Subring.subset_closure (Or.inr rfl)
    · rw [← ElementaryBranching.prefix_generator]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  have hL : Subring.closure ((OddSymmetricKernel.kernelSubring 0 : Set (SkewPolynomial 2)) ∪
      {generator (Fin.last 1)}) = ⊤ := by
    rw [eq_top_iff, ← closure_generators 2, Subring.closure_le]
    have h1 : generator (Fin.last 1) ∈ Subring.closure
        ((OddSymmetricKernel.kernelSubring 0 : Set (SkewPolynomial 2)) ∪
          {generator (Fin.last 1)}) := Subring.subset_closure (Or.inr rfl)
    have he : FiniteCompleteElementary.elementaryPoly 2 1 ∈ Subring.closure
        ((OddSymmetricKernel.kernelSubring 0 : Set (SkewPolynomial 2)) ∪
          {generator (Fin.last 1)}) :=
      Subring.subset_closure (Or.inl (OddSymmetricKernel.elementary_mem 0 1))
    rw [elementary_one_eq, Fin.sum_univ_two] at he
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · have h0 : generator (0 : Fin 2) = (PlacticEvaluation.tildeGenerator 0 +
          PlacticEvaluation.tildeGenerator 1) + generator (Fin.last 1) := by
        simp [PlacticEvaluation.tildeGenerator, Fin.last]
      change generator (0 : Fin 2) ∈ _
      rw [h0]
      exact Subring.add_mem _ he h1
    · exact h1
  rw [hL, hR]

/-! ### (2.49)–(2.51) -/

open ElementaryBranching («prefix» E)

/-- Every product ending in `x_j^k`, `k ≥ 1`, has zero constant coefficient. -/
theorem mul_pow_generator_zero {N : ℕ} (p : SkewPolynomial N) (j : Fin N) (k : ℕ) (hk : 1 ≤ k) :
    (p * generator j ^ k) 0 = 0 := by
  rw [PbwL4.pow_form, ElementaryGeneration.mul_coeff]
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v hv => ?_
  have hv' : v = k • OddMath.SkewPolynomial.expSingle j := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp hv) (Finsupp.single_eq_of_ne (Ne.symm hne))
  rw [if_neg]
  intro he
  have := congrFun he j
  simp [hv', OddMath.SkewPolynomial.expSingle] at this
  omega

theorem mul_pow_last_zero {N : ℕ} (p : SkewPolynomial (N+1)) (k : ℕ) (hk : 1 ≤ k) :
    (p * generator (Fin.last N) ^ k) 0 = 0 :=
  mul_pow_generator_zero p _ k hk

theorem one_apply_zero (N : ℕ) : (1 : SkewPolynomial N) 0 ≠ 0 := by
  change (OddMath.SkewPolynomial.monomial 0 1 : SkewPolynomial N) 0 ≠ 0
  simp [OddMath.SkewPolynomial.monomial]

/-- The printed (2.49) (sum over `1 ≤ k ≤ a-1`) fails for `f = 1`, in every rank `a = n+2`:
`1 ∉ Σ_{k=1}^{a-1} OΛ_a · H_{a-1} · x_a^k`. -/
theorem eq_2_49_printed_fails (n : ℕ) :
    (1 : SkewPolynomial (n+2)) ∉ Submodule.span ℤ {f | ∃ ℓ ∈ OddSymmetricKernel.kernelSubring n,
      ∃ h ∈ SchubertBasis.H (n+1), ∃ k, 1 ≤ k ∧ k ≤ n + 1 ∧
        f = ℓ * «prefix» (n+1) h * generator (Fin.last (n+1)) ^ k} := by
  intro h1
  have hker : Submodule.span ℤ {f | ∃ ℓ ∈ OddSymmetricKernel.kernelSubring n,
      ∃ h ∈ SchubertBasis.H (n+1), ∃ k, 1 ≤ k ∧ k ≤ n + 1 ∧
        f = ℓ * «prefix» (n+1) h * generator (Fin.last (n+1)) ^ k} ≤
      LinearMap.ker (Finsupp.lapply 0) := by
    rw [Submodule.span_le]
    rintro _ ⟨ℓ, _, h, _, k, hk, _, rfl⟩
    exact mul_pow_last_zero _ k hk
  have := hker h1
  rw [LinearMap.mem_ker, Finsupp.lapply_apply] at this
  exact one_apply_zero _ this

/-- Moving `x_a^k` from the right to the left of a polynomial in `x_1, …, x_{a-1}`. -/
theorem prefix_mul_pow_last (N k : ℕ) (q : SkewPolynomial N) :
    ∃ q', «prefix» N q * generator (Fin.last N) ^ k = generator (Fin.last N) ^ k * «prefix» N q' := by
  induction k generalizing q with
  | zero => exact ⟨q, by simp⟩
  | succ k ih =>
    have h1 : ∀ q : SkewPolynomial N, ∃ q',
        «prefix» N q * generator (Fin.last N) = generator (Fin.last N) * «prefix» N q' := by
      intro q
      have hq : q ∈ Subring.closure (Set.range (generator : Fin N → SkewPolynomial N)) := by
        rw [closure_generators]; trivial
      induction hq using Subring.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine ⟨-generator i, ?_⟩
        rw [ElementaryBranching.prefix_generator, map_neg, ElementaryBranching.prefix_generator,
          mul_neg]
        exact OddMath.SkewPolynomial.generator_anticommute _ _ (Fin.castSucc_ne_last i)
      | one => exact ⟨1, by simp⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', hx'⟩ := hx; obtain ⟨y', hy'⟩ := hy
        exact ⟨x' + y', by rw [map_add, add_mul, hx', hy', map_add, mul_add]⟩
      | neg x _ hx =>
        obtain ⟨x', hx'⟩ := hx
        exact ⟨-x', by rw [map_neg, neg_mul, hx', map_neg, mul_neg]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨x', hx'⟩ := hx; obtain ⟨y', hy'⟩ := hy
        exact ⟨x' * y', by rw [map_mul, mul_assoc, hy', ← mul_assoc, hx', mul_assoc, map_mul]⟩
    obtain ⟨q1, hq1⟩ := h1 q
    obtain ⟨q2, hq2⟩ := ih q1
    exact ⟨q2, by rw [pow_succ', ← mul_assoc, hq1, mul_assoc, hq2, ← mul_assoc, ← pow_succ']⟩

/-- EKL (2.51) holds as stated (with `H_{a-1}` of (2.46) and `OΛ_{a-1}` the elementary-generated
subring, every rank `a = N+1`): `OPol_a = Σ_{k ≥ 0} x_a^k · OΛ_{a-1} · H_{a-1}`. -/
theorem eq_2_51 (N : ℕ) (f : SkewPolynomial (N+1)) :
    f ∈ Submodule.span ℤ {g | ∃ k : ℕ, ∃ ℓ ∈ E N, ∃ h ∈ SchubertBasis.H N,
      g = generator (Fin.last N) ^ k * «prefix» N ℓ * «prefix» N h} := by
  set S := Submodule.span ℤ {g | ∃ k : ℕ, ∃ ℓ ∈ E N, ∃ h ∈ SchubertBasis.H N,
      g = generator (Fin.last N) ^ k * «prefix» N ℓ * «prefix» N h}
  have hpre : ∀ (k : ℕ) (q : SkewPolynomial N), generator (Fin.last N) ^ k * «prefix» N q ∈ S := by
    intro k q
    obtain ⟨c, hc, _⟩ := StaircaseLeft.left_decomposition_unique N q
    rw [hc, map_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun A _ => Submodule.subset_span ⟨k, c A, (c A).property,
      StaircaseSpanning.stairMonomial A, Submodule.subset_span ⟨A, rfl⟩, ?_⟩
    rw [map_mul, mul_assoc]
  induction f using Finsupp.induction_linear with
  | zero => exact S.zero_mem
  | add f g hf hg => exact S.add_mem hf hg
  | single e c =>
    change OddMath.SkewPolynomial.monomial e c ∈ S
    rw [MonomialReversal.monomial_eq_smul_prod, List.ofFn_succ', List.prod_concat]
    have hP : (List.ofFn fun j : Fin N => generator j.castSucc ^ e j.castSucc).prod =
        «prefix» N (List.ofFn fun j : Fin N => generator j ^ e j.castSucc).prod := by
      rw [map_list_prod, List.map_ofFn]
      congr 1
      refine congrArg List.ofFn (funext fun j => ?_)
      simp [ElementaryBranching.prefix_generator]
    simp only [Function.comp_def] at hP ⊢
    rw [hP]
    obtain ⟨q', hq'⟩ := prefix_mul_pow_last N (e (Fin.last N))
      (List.ofFn fun j : Fin N => generator j ^ e j.castSucc).prod
    rw [hq']
    exact S.smul_mem c (hpre _ _)

/-- A monomial in `a = N+1` variables is `x^{A'} · x_a^{A_a}` with `x^{A'}` in the first `N`. -/
theorem monomial_split_last (N : ℕ) (e : Fin (N+1) → ℕ) (c : ℤ) :
    OddMath.SkewPolynomial.monomial e c =
      c • («prefix» N (OddMath.SkewPolynomial.monomial (fun j => e j.castSucc) 1) *
        generator (Fin.last N) ^ e (Fin.last N)) := by
  rw [MonomialReversal.monomial_eq_smul_prod, List.ofFn_succ', List.prod_concat,
    MonomialReversal.monomial_eq_prod, map_list_prod, List.map_ofFn]
  congr 2
  refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
  simp [ElementaryBranching.prefix_generator]

/-- The first equality in (2.50): `OPol_a = Σ_k x_a^k · OPol_{a-1}`. -/
theorem eq_2_50_first (N : ℕ) (f : SkewPolynomial (N+1)) :
    f ∈ Submodule.span ℤ {g | ∃ k : ℕ, ∃ q : SkewPolynomial N,
      g = generator (Fin.last N) ^ k * «prefix» N q} := by
  induction f using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | single e c =>
    change OddMath.SkewPolynomial.monomial e c ∈ _
    rw [monomial_split_last]
    obtain ⟨q', hq'⟩ := prefix_mul_pow_last N (e (Fin.last N))
      (OddMath.SkewPolynomial.monomial (fun j => e j.castSucc) 1)
    rw [hq']
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨_, q', rfl⟩)

/-- The reversed staircase `H'_N = span_ℤ{x^A : A_i ≤ i}` (zero-based), i.e. exponent of `x_i`
at most `i - 1` in the source's one-based indexing. -/
def Hrev (N : ℕ) : Submodule ℤ (SkewPolynomial N) :=
  Submodule.span ℤ {f | ∃ A : Fin N → ℕ, (∀ i, A i ≤ i.val) ∧ f = OddMath.SkewPolynomial.monomial A 1}

/-- `OPol_a = OΛ_a · H'_a`, from the (2.46) staircase decomposition and the longest element. -/
theorem reversed_left_span (n : ℕ) (f : SkewPolynomial (n+2)) :
    f ∈ Submodule.span ℤ {g | ∃ ℓ ∈ OddSymmetricKernel.kernelSubring n, ∃ A : Fin (n+2) → ℕ,
      (∀ i, A i ≤ i.val) ∧ g = ℓ * OddMath.SkewPolynomial.monomial A 1} := by
  obtain ⟨c, hc, _⟩ := StaircaseLeft.left_kernel_decomposition_unique n
    (SignedPermutation.skewAction (LongestElementary.longest (n+2)) f)
  have hf := congrArg (SignedPermutation.skewAction (LongestElementary.longest (n+2))) hc
  rw [LongestElementary.action_involutive, map_sum] at hf
  rw [hf]
  refine Submodule.sum_mem _ fun A _ => ?_
  rw [map_mul, StaircaseSpanning.stairMonomial, MonomialReversal.action_monomial, mul_smul_comm]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, LongestElementary.action_mem_kernel n _
    (c A).property, _, fun i => ?_, rfl⟩)
  have h := A.property ((LongestElementary.longest (n+2)).symm i)
  simp only [LongestElementary.longest, Equiv.coe_fn_symm_mk, Fin.val_rev] at h ⊢
  omega

/-- EKL (2.49) with the reversed staircase `H'_{a-1}` in place of `H_{a-1}` and the sum from `k = 0`,
every rank `a = n+2`: `OPol_a = Σ_{k=0}^{a-1} OΛ_a · H'_{a-1} · x_a^k`. -/
theorem eq_2_49_reversed (n : ℕ) (f : SkewPolynomial (n+2)) :
    f ∈ Submodule.span ℤ {g | ∃ ℓ ∈ OddSymmetricKernel.kernelSubring n, ∃ h ∈ Hrev (n+1),
      ∃ k, k ≤ n + 1 ∧ g = ℓ * «prefix» (n+1) h * generator (Fin.last (n+1)) ^ k} := by
  refine (Submodule.span_le.mpr ?_) (reversed_left_span n f)
  rintro _ ⟨ℓ, hℓ, A, hA, rfl⟩
  rw [monomial_split_last, one_smul, ← mul_assoc]
  exact Submodule.subset_span ⟨ℓ, hℓ, _, Submodule.subset_span ⟨_, fun i => hA i.castSucc, rfl⟩,
    A (Fin.last (n+1)), by have := hA (Fin.last (n+1)); simpa using this, rfl⟩

/-- The printed (2.50) (inner sum over `1 ≤ i ≤ a-2`) fails for `f = 1`, every rank `a = n+3`. -/
theorem eq_2_50_printed_fails (n : ℕ) :
    (1 : SkewPolynomial (n+3)) ∉ Submodule.span ℤ {g | ∃ k : ℕ,
      ∃ ℓ ∈ OddSymmetricKernel.kernelSubring n, ∃ h ∈ SchubertBasis.H (n+1), ∃ i, 1 ≤ i ∧
        i ≤ n + 1 ∧ g = generator (Fin.last (n+2)) ^ k *
          «prefix» (n+2) (ℓ * «prefix» (n+1) h * generator (Fin.last (n+1)) ^ i)} := by
  intro h1
  have hker : Submodule.span ℤ {g | ∃ k : ℕ,
      ∃ ℓ ∈ OddSymmetricKernel.kernelSubring n, ∃ h ∈ SchubertBasis.H (n+1), ∃ i, 1 ≤ i ∧
        i ≤ n + 1 ∧ g = generator (Fin.last (n+2)) ^ k *
          «prefix» (n+2) (ℓ * «prefix» (n+1) h * generator (Fin.last (n+1)) ^ i)} ≤
      LinearMap.ker (Finsupp.lapply 0) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, ℓ, _, h, _, i, hi, _, rfl⟩
    rw [map_mul, map_pow, ElementaryBranching.prefix_generator, ← mul_assoc]
    exact mul_pow_generator_zero _ _ i hi
  have := hker h1
  rw [LinearMap.mem_ker, Finsupp.lapply_apply] at this
  exact one_apply_zero _ this

/-- EKL (2.50) with `H'_{a-2}` in place of `H_{a-2}` and the inner sum from `i = 0`, `a = n+3`:
`OPol_a = Σ_{k,i} x_a^k · OΛ_{a-1} · H'_{a-2} · x_{a-1}^i`, `0 ≤ i ≤ a-2`. -/
theorem eq_2_50_reversed (n : ℕ) (f : SkewPolynomial (n+3)) :
    f ∈ Submodule.span ℤ {g | ∃ k : ℕ, ∃ ℓ ∈ OddSymmetricKernel.kernelSubring n,
      ∃ h ∈ Hrev (n+1), ∃ i, i ≤ n + 1 ∧ g = generator (Fin.last (n+2)) ^ k *
        «prefix» (n+2) (ℓ * «prefix» (n+1) h * generator (Fin.last (n+1)) ^ i)} := by
  set T := Submodule.span ℤ {g | ∃ k : ℕ, ∃ ℓ ∈ OddSymmetricKernel.kernelSubring n,
      ∃ h ∈ Hrev (n+1), ∃ i, i ≤ n + 1 ∧ g = generator (Fin.last (n+2)) ^ k *
        «prefix» (n+2) (ℓ * «prefix» (n+1) h * generator (Fin.last (n+1)) ^ i)}
  refine (Submodule.span_le.mpr ?_) (eq_2_50_first (n+2) f)
  rintro _ ⟨k, q, rfl⟩
  let L : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+3) :=
    (LinearMap.mulLeft ℤ (generator (Fin.last (n+2)) ^ k)).comp
      («prefix» (n+2)).toIntAlgHom.toLinearMap
  have key : q ∈ T.comap L := by
    refine (Submodule.span_le.mpr ?_) (eq_2_49_reversed n q)
    rintro _ ⟨ℓ, hℓ, h, hh, i, hi, rfl⟩
    exact Submodule.subset_span ⟨k, ℓ, hℓ, h, hh, i, hi, rfl⟩
  exact key

/-! ### (2.49) with the staircase (2.46), summed from `k = 0` -/

section Staircase
open StaircaseSpanning (shift stairMonomial StairIndex)
open SignedPermutation (skewAction)
open LongestElementary (longest)

theorem longest_mem_E (N : ℕ) (f : SkewPolynomial N) (hf : f ∈ E N) :
    skewAction (longest N) f ∈ E N := by
  induction hf using Subring.closure_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    rw [LongestElementary.action_elementary]
    exact (E N).zsmul_mem (Subring.subset_closure ⟨k, rfl⟩) _
  | zero => simpa using (E N).zero_mem
  | one => simpa using (E N).one_mem
  | add f g _ _ hf hg => simpa only [map_add] using (E N).add_mem hf hg
  | neg f _ hf => simpa only [map_neg] using (E N).neg_mem hf
  | mul f g _ _ hf hg => simpa only [map_mul] using (E N).mul_mem hf hg

/-- Right `OΛ_N`-span by the reversed staircase monomials. -/
theorem rev_right_span (N : ℕ) (p : SkewPolynomial N) :
    p ∈ Submodule.span ℤ {g | ∃ A : Fin N → ℕ, (∀ i, A i ≤ i.val) ∧ ∃ c ∈ E N,
      g = OddMath.SkewPolynomial.monomial A 1 * c} := by
  obtain ⟨c, hc⟩ := StaircaseSpanning.right_span N (skewAction (longest N) p)
  have hp := congrArg (skewAction (longest N)) hc
  rw [LongestElementary.action_involutive, map_sum] at hp
  rw [hp]
  refine Submodule.sum_mem _ fun A _ => ?_
  rw [map_mul, stairMonomial, MonomialReversal.action_monomial, smul_mul_assoc]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun i => ?_, _,
    longest_mem_E N _ (c A).property, rfl⟩)
  have h := A.property ((longest N).symm i)
  simp only [longest, Equiv.coe_fn_symm_mk, Fin.val_rev] at h ⊢
  omega

/-- First-variable elimination with an arbitrary right-spanning family `B` of `OPol_N`:
`OPol_{N+1} = Σ_{b ∈ B, j ≤ N} shift(b) · x_0^j · OΛ_{N+1}`. -/
theorem first_span_general (N : ℕ) (B : Set (SkewPolynomial N))
    (hB : ∀ p : SkewPolynomial N, p ∈ Submodule.span ℤ {g | ∃ b ∈ B, ∃ c ∈ E N, g = b * c})
    (f : SkewPolynomial (N+1)) :
    f ∈ Submodule.span ℤ {g | ∃ b ∈ B, ∃ j, j ≤ N ∧ ∃ c ∈ E (N+1),
      g = shift N b * StaircaseSpanning.X N ^ j * c} := by
  set T := Submodule.span ℤ {g | ∃ b ∈ B, ∃ j, j ≤ N ∧ ∃ c ∈ E (N+1),
      g = shift N b * StaircaseSpanning.X N ^ j * c}
  have hprod : ∀ (k : ℕ) (p : SkewPolynomial N), shift N p * StaircaseSpanning.X N ^ k ∈ T := by
    intro k p
    let L : SkewPolynomial N →ₗ[ℤ] SkewPolynomial (N+1) :=
      (LinearMap.mulRight ℤ (StaircaseSpanning.X N ^ k)).comp (shift N).toIntAlgHom.toLinearMap
    have key : p ∈ T.comap L := by
      refine (Submodule.span_le.mpr ?_) (hB p)
      rintro _ ⟨b, hb, c, hc, rfl⟩
      change shift N (b * c) * StaircaseSpanning.X N ^ k ∈ T
      obtain ⟨d, hd⟩ := StaircaseSpanning.shift_E_left_mem N ⟨c, hc⟩
        (StaircaseSpanning.firstSpan_power N k)
      rw [map_mul, mul_assoc]
      change shift N c * StaircaseSpanning.X N ^ k = _ at hd
      rw [hd, Finset.mul_sum]
      refine Submodule.sum_mem _ fun j _ => Submodule.subset_span
        ⟨b, hb, j.val, by have := j.isLt; omega, d j, (d j).property, by rw [mul_assoc]⟩
    exact key
  induction f using Finsupp.induction_linear with
  | zero => exact T.zero_mem
  | add f g hf hg => exact T.add_mem hf hg
  | single a c =>
    let b : Fin N → ℕ := fun i => a i.succ
    let sg : ℤ := OddMath.skewSign (VariableEmbedding.expEmbed (Fin.succOrderEmb N) b)
      (a 0 • OddMath.SkewPolynomial.expSingle (0 : Fin (N+1)))
    have hs : sg * sg = 1 := ElementaryGeneration.skewSign_square _ _
    have he : Fin.cons (a 0) b = a := by
      funext i
      cases i using Fin.cases <;> rfl
    have h := hprod (a 0) (OddMath.SkewPolynomial.monomial b 1)
    rw [StaircaseSpanning.shift_monomial_mul_power, he] at h
    change sg • OddMath.SkewPolynomial.monomial a 1 ∈ T at h
    have hh := T.smul_mem (c * sg) h
    have heq : (c * sg) • sg • OddMath.SkewPolynomial.monomial a 1 =
        OddMath.SkewPolynomial.monomial a c := by
      rw [smul_smul, mul_assoc, hs, mul_one]
      simp [OddMath.SkewPolynomial.monomial, Finsupp.smul_single]
    rw [heq] at hh
    exact hh

theorem longest_shift_monomial (N : ℕ) (B : Fin N → ℕ) :
    ∃ sg : ℤ, skewAction (longest (N+1)) (shift N (OddMath.SkewPolynomial.monomial B 1)) =
      sg • «prefix» N (OddMath.SkewPolynomial.monomial (fun i => B i.rev) 1) := by
  have hs : shift N (OddMath.SkewPolynomial.monomial B 1) =
      OddMath.SkewPolynomial.monomial (VariableEmbedding.expEmbed (Fin.succOrderEmb N) B) 1 :=
    VariableEmbedding.embed_monomial _ _ _
  rw [hs, MonomialReversal.action_monomial]
  suffices hm : OddMath.SkewPolynomial.monomial
      (fun t => VariableEmbedding.expEmbed (Fin.succOrderEmb N) B ((longest (N+1)).symm t)) 1 =
      «prefix» N (OddMath.SkewPolynomial.monomial (fun i => B i.rev) 1) by
    rw [hm]; exact ⟨_, rfl⟩
  rw [monomial_split_last, one_smul]
  have h0 : VariableEmbedding.expEmbed (Fin.succOrderEmb N) B ((longest (N+1)).symm
      (Fin.last N)) = 0 := by
    apply VariableEmbedding.expEmbed_not_mem_range
    rintro ⟨i, hi⟩
    simp only [longest, Equiv.coe_fn_symm_mk, Fin.rev_last] at hi
    exact Fin.succ_ne_zero i hi
  rw [h0, pow_zero, mul_one]
  congr 2
  funext i
  simp only [longest, Equiv.coe_fn_symm_mk, Fin.rev_castSucc]
  exact VariableEmbedding.expEmbed_apply (Fin.succOrderEmb N) B i.rev

/-- Right form of (2.49) with the staircase (2.46):
`OPol_{N+1} = Σ_{A, j ≤ N} x^A · x_{N+1}^j · OΛ_{N+1}`, `x^A ∈ H_N`. -/
theorem eq_2_49_right (N : ℕ) (f : SkewPolynomial (N+1)) :
    f ∈ Submodule.span ℤ {g | ∃ A : StairIndex N, ∃ j, j ≤ N ∧ ∃ c ∈ E (N+1),
      g = «prefix» N (stairMonomial A) * generator (Fin.last N) ^ j * c} := by
  set T := Submodule.span ℤ {g | ∃ A : StairIndex N, ∃ j, j ≤ N ∧ ∃ c ∈ E (N+1),
      g = «prefix» N (stairMonomial A) * generator (Fin.last N) ^ j * c}
  have hw := first_span_general N
    {g | ∃ A : Fin N → ℕ, (∀ i, A i ≤ i.val) ∧ g = OddMath.SkewPolynomial.monomial A 1}
    (fun p => by
      refine (Submodule.span_mono ?_) (rev_right_span N p)
      rintro _ ⟨A, hA, c, hc, rfl⟩
      exact ⟨_, ⟨A, hA, rfl⟩, c, hc, rfl⟩)
    (skewAction (longest (N+1)) f)
  let W : SkewPolynomial (N+1) →ₗ[ℤ] SkewPolynomial (N+1) :=
    (skewAction (longest (N+1))).toRingHom.toIntAlgHom.toLinearMap
  have key : skewAction (longest (N+1)) f ∈ T.comap W := by
    refine (Submodule.span_le.mpr ?_) hw
    rintro _ ⟨_, ⟨B, hB, rfl⟩, j, hj, c, hc, rfl⟩
    change skewAction (longest (N+1)) (shift N (OddMath.SkewPolynomial.monomial B 1) *
      StaircaseSpanning.X N ^ j * c) ∈ T
    obtain ⟨sg, hsg⟩ := longest_shift_monomial N B
    rw [map_mul, map_mul, map_pow, hsg, StaircaseSpanning.X, SignedPermutation.action_generator]
    simp only [longest, Equiv.coe_fn_mk, Fin.rev_zero, smul_pow, smul_mul_assoc, mul_smul_comm]
    let A : StairIndex N := ⟨fun i => B i.rev, fun i => by
      have := hB i.rev; simp only [Fin.val_rev] at this; show B i.rev ≤ N - 1 - i.val; omega⟩
    refine T.smul_mem _ (T.smul_mem _ (Submodule.subset_span ⟨A, j, hj, _,
      longest_mem_E (N+1) c hc, ?_⟩))
    rfl
  have := key
  rw [Submodule.mem_comap] at this
  change skewAction (longest (N+1)) (skewAction (longest (N+1)) f) ∈ T at this
  rwa [LongestElementary.action_involutive] at this

/-- EKL (2.49) with the staircase `H_{a-1}` of (2.46) and the sum from `k = 0`, every rank
`a = N+1`: `OPol_a = Σ_{k=0}^{a-1} OΛ_a · H_{a-1} · x_a^k` (`OΛ_a` the elementary-generated
subring, which is the joint kernel for `a ≥ 2`). -/
theorem eq_2_49_sum_from_zero (N : ℕ) (f : SkewPolynomial (N+1)) :
    f ∈ Submodule.span ℤ {g | ∃ ℓ ∈ E (N+1), ∃ h ∈ SchubertBasis.H N, ∃ k, k ≤ N ∧
      g = ℓ * «prefix» N h * generator (Fin.last N) ^ k} := by
  set T := Submodule.span ℤ {g | ∃ ℓ ∈ E (N+1), ∃ h ∈ SchubertBasis.H N, ∃ k, k ≤ N ∧
      g = ℓ * «prefix» N h * generator (Fin.last N) ^ k}
  have key : StaircaseLeft.reverse (N+1) f ∈ T.comap (StaircaseLeft.reverse (N+1)) := by
    refine (Submodule.span_le.mpr ?_) (eq_2_49_right N (StaircaseLeft.reverse (N+1) f))
    rintro _ ⟨A, j, hj, c, hc, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    let e : Fin (N+1) → ℕ := Fin.lastCases j (fun i => A.val i)
    have hsplit : «prefix» N (stairMonomial A) * generator (Fin.last N) ^ j =
        OddMath.SkewPolynomial.monomial e 1 := by
      rw [monomial_split_last, one_smul]
      simp only [e, Fin.lastCases_castSucc, Fin.lastCases_last]
      rfl
    rw [StaircaseLeft.reverse_mul, hsplit, StaircaseLeft.reverse_monomial, one_mul,
      PbwL4.monomial_smul, mul_smul_comm, ← hsplit, ← mul_assoc]
    exact T.smul_mem _ (Submodule.subset_span ⟨_, StaircaseLeft.reverse_mem_E c hc, _,
      Submodule.subset_span ⟨A, rfl⟩, j, hj, rfl⟩)
  rw [Submodule.mem_comap, StaircaseLeft.reverse_involutive] at key
  exact key

/-- EKL (2.50) with the inner sum from `i = 0` (staircase (2.46)), every rank `a = N+2`:
`OPol_a = Σ_{k, i ≤ a-2} x_a^k · OΛ_{a-1} · H_{a-2} · x_{a-1}^i`. -/
theorem eq_2_50_sum_from_zero (N : ℕ) (f : SkewPolynomial (N+2)) :
    f ∈ Submodule.span ℤ {g | ∃ k : ℕ, ∃ ℓ ∈ E (N+1), ∃ h ∈ SchubertBasis.H N, ∃ i, i ≤ N ∧
      g = generator (Fin.last (N+1)) ^ k *
        «prefix» (N+1) (ℓ * «prefix» N h * generator (Fin.last N) ^ i)} := by
  set T := Submodule.span ℤ {g | ∃ k : ℕ, ∃ ℓ ∈ E (N+1), ∃ h ∈ SchubertBasis.H N, ∃ i, i ≤ N ∧
      g = generator (Fin.last (N+1)) ^ k *
        «prefix» (N+1) (ℓ * «prefix» N h * generator (Fin.last N) ^ i)}
  refine (Submodule.span_le.mpr ?_) (eq_2_50_first (N+1) f)
  rintro _ ⟨k, q, rfl⟩
  let L : SkewPolynomial (N+1) →ₗ[ℤ] SkewPolynomial (N+2) :=
    (LinearMap.mulLeft ℤ (generator (Fin.last (N+1)) ^ k)).comp
      («prefix» (N+1)).toIntAlgHom.toLinearMap
  have key : q ∈ T.comap L := by
    refine (Submodule.span_le.mpr ?_) (eq_2_49_sum_from_zero N q)
    rintro _ ⟨ℓ, hℓ, h, hh, i, hi, rfl⟩
    exact Submodule.subset_span ⟨k, ℓ, hℓ, h, hh, i, hi, rfl⟩
  exact key

end Staircase

/-! ### (2.53) for `OPol_a` over `OΛ_a` -/

section EndRank
open NilHeckeGradedEnd NilHeckeEndomorphism NilCoxeterWords

/-- Degree-`e` piece of `OΛ_a` into the literal degree piece `(OΛ_a)_{e/2}`. -/
def kernelPieceToDegree (n : ℕ) (e : ℤ) :
    kernelPiece n e →ₗ[ℤ] ElementaryBasis.degreePiece n (e.toNat / 2) where
  toFun k := ⟨((k : K n) : SkewPolynomial (n+2)), (k : K n).property, fun a ha => by
    by_contra hne
    have h := k.property a (fun he => ha (by
      simp only [pdegree] at he; simp only [ElementaryBasis.weight]; omega))
    exact hne h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernelPieceToDegree_injective (n : ℕ) (e : ℤ) :
    Function.Injective (kernelPieceToDegree n e) := fun x y h => by
  apply Subtype.ext; apply Subtype.ext
  exact congrArg (fun z : ElementaryBasis.degreePiece n (e.toNat / 2) =>
    (z : SkewPolynomial (n+2))) h

local instance (n d : ℕ) : Module.Finite ℤ (ElementaryBasis.degreePiece n d) :=
  Module.Finite.of_basis (ElementaryBasis.gradedBasis n d)

local instance (n : ℕ) (e : ℤ) : Module.Finite ℤ (kernelPiece n e) :=
  Module.Finite.of_injective _ (kernelPieceToDegree_injective n e)

local instance (n : ℕ) (e : ℤ) : Module.Free ℤ (kernelPiece n e) := by
  haveI : NoZeroSMulDivisors ℤ (kernelPiece n e) :=
    Function.Injective.noZeroSMulDivisors _ (kernelPieceToDegree_injective n e) (map_zero _)
      (fun c x => map_zsmul _ c x)
  exact Module.free_of_finite_type_torsion_free'

/-- Homogeneous right `OΛ_a`-linear endomorphisms of `OPol_a` of degree `d`. -/
def endPiece (n : ℕ) (d : ℤ) : Submodule ℤ (rightKernelEnd n) where
  carrier := {T | endDegree d T}
  zero_mem' := fun e f _ => by
    change (0 : SkewPolynomial (n+2)) ∈ _
    exact Submodule.zero_mem _
  add_mem' := fun {T U} hT hU e f hf => by
    change T.val f + U.val f ∈ _
    exact Submodule.add_mem _ (hT e f hf) (hU e f hf)
  smul_mem' := fun z T hT e f hf => by
    change z • T.val f ∈ _
    exact Submodule.smul_mem _ z (hT e f hf)

/-- Degree-`d` matrices: entry `(i,j)` of degree `d + 2ℓ(j) - 2ℓ(i)`. -/
def matPiece (n : ℕ) (d : ℤ) : Submodule ℤ (Matrix (Perm n) (Perm n) (K n)) where
  carrier := {M | matrixDegree d M}
  zero_mem' := fun _ _ => (kernelPiece n _).zero_mem
  add_mem' := fun hM hN i j => (kernelPiece n _).add_mem (hM i j) (hN i j)
  smul_mem' := fun z _ hM i j => (kernelPiece n _).smul_mem z (hM i j)

def endMatEquiv (n : ℕ) (d : ℤ) : endPiece n d ≃ₗ[ℤ] matPiece n d :=
  LinearEquiv.ofSubmodules (matrixEquiv n).toAddEquiv.toIntLinearEquiv _ _ (by
    ext M
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact (matrixEquiv_degree_iff n T d).mp hT
    · intro hM
      refine ⟨(matrixEquiv n).symm M, (matrixEquiv_degree_iff n _ d).mpr ?_, ?_⟩
      · change matrixDegree d (matrixEquiv n ((matrixEquiv n).symm M))
        rw [RingEquiv.apply_symm_apply]; exact hM
      · change matrixEquiv n ((matrixEquiv n).symm M) = M
        rw [RingEquiv.apply_symm_apply])

def matPiEquiv (n : ℕ) (d : ℤ) :
    matPiece n d ≃ₗ[ℤ] ((ij : Perm n × Perm n) →
      kernelPiece n (d + 2 * (length ij.2 : ℤ) - 2 * (length ij.1 : ℤ))) where
  toFun M ij := ⟨M.val ij.1 ij.2, M.property ij.1 ij.2⟩
  invFun g := ⟨fun i j => (g (i, j)).val, fun i j => (g (i, j)).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- EKL (2.53) for `A = OΛ_a`, `M = OPol_a` (`a = n+2`, free with the Schubert basis of degrees
`2ℓ(w)`, so `h(q) = Σ_w q^{2ℓ(w)}`), `End` taken over right `OΛ_a`-linear maps: coefficientwise,
`rk (End^d) = Σ_{i,j ∈ S_a} rk (OΛ_a)_{d + 2ℓ(j) - 2ℓ(i)}`, the coefficient of `q^d` in
`rk_q(OΛ_a) · h(q) · h(q⁻¹)`. -/
theorem eq_2_53 (n : ℕ) (d : ℤ) :
    Module.finrank ℤ (endPiece n d) = ∑ i : Perm n, ∑ j : Perm n,
      Module.finrank ℤ (kernelPiece n (d + 2 * (length j : ℤ) - 2 * (length i : ℤ))) := by
  rw [((endMatEquiv n d).trans (matPiEquiv n d)).finrank_eq, Module.finrank_pi_fintype,
    Fintype.sum_prod_type]

end EndRank

end
end OddMath.Frontier.EKLSectionTwo
