import OddMath.Frontier.EQZabHat
import OddMath.Frontier.ThickDecomposition
import OddMath.Frontier.OnhReflection

/-!
# Reversal of products and odd Schur polynomials

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2 (the bases (4.21) of `OΛ̃_a ⊠ OΛ̃_b`); EKL arXiv:1111.1320v1 §2.2 and §3.3 (the
anti-automorphism `ψ` of `ONH`).

`rev` is the anti-automorphism of `OPol_N` fixing every `x_j` (it reverses the order of every
product). On the odd nilHecke ring, the corresponding anti-automorphism is EKL's `ψ`
(`NilHeckeRightBasis.reverseLinear`), which fixes dots and crossings; `reverse_polyElem` shows
`ψ(f) = rev(f)` on the dot subring.

* `rev_elementaryPoly`: `rev(ε_k) = ±ε_k`, so `rev` preserves `OΛ̃_N` (`rev_mem_kernel`);
* `D_rev` (all polynomials `g`, rank `N = n+2`):
  `∂_{w₀}(rev g) = (-1)^{binom(N,4)} w₀(rev(∂_{w₀} g))` (EKL's signed `w₀`), obtained by applying
  `ψ` to `∂_{w₀} g ∂_{w₀} = ∂_{w₀}(g) ∂_{w₀}`, with `ψ(∂_{w₀}) = (-1)^{binom(N,4)} ∂_{w₀}`;
* `rev_twisted` (every rank): `rev(s̃_λ) = ± s̃̂_λ`: reversing products exchanges the twisted odd
  Schur polynomials and the hat ones of Lemma 4.5, up to sign.
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open scoped BigOperators

noncomputable section

local instance (priority := high) zabRevNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabRevNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ## Signs -/

/-- `ε = ±1`. -/
def IsSign (ε : ℤ) : Prop := ε = 1 ∨ ε = -1

theorem IsSign.one : IsSign 1 := Or.inl rfl

theorem IsSign.neg_one : IsSign (-1) := Or.inr rfl

theorem IsSign.mul {ε η : ℤ} (h : IsSign ε) (h' : IsSign η) : IsSign (ε * η) := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> simp [IsSign]

theorem IsSign.pow (k : ℕ) : IsSign ((-1 : ℤ) ^ k) := by
  rcases neg_one_pow_eq_or ℤ k with h | h <;> simp [IsSign, h]

theorem IsSign.mul_self {ε : ℤ} (h : IsSign ε) : ε * ε = 1 := by
  rcases h with rfl | rfl <;> norm_num

section Generic

variable {R : Type*} [Ring R]

/-- Moving `a` across a list of elements each of which commutes with `a` up to a sign. -/
theorem mul_prod_signed (a : R) :
    ∀ L : List R, (∀ v ∈ L, ∃ ε, IsSign ε ∧ a * v = ε • (v * a)) →
      ∃ ε, IsSign ε ∧ a * L.prod = ε • (L.prod * a)
  | [], _ => ⟨1, IsSign.one, by simp⟩
  | b :: L, h => by
    obtain ⟨ε, hε, hab⟩ := h b (List.mem_cons_self)
    obtain ⟨η, hη, hL⟩ := mul_prod_signed a L (fun v hv => h v (List.mem_cons_of_mem _ hv))
    refine ⟨ε * η, hε.mul hη, ?_⟩
    rw [List.prod_cons, ← mul_assoc, hab, smul_mul_assoc, mul_assoc, hL, mul_smul_comm, smul_smul,
      ← mul_assoc]

/-- Reversing a product of pairwise sign-commuting elements changes it by a sign. -/
theorem reverse_prod_signed :
    ∀ L : List R, L.Pairwise (fun u v => ∃ ε, IsSign ε ∧ u * v = ε • (v * u)) →
      ∃ ε, IsSign ε ∧ L.reverse.prod = ε • L.prod
  | [], _ => ⟨1, IsSign.one, by simp⟩
  | a :: L, h => by
    rw [List.pairwise_cons] at h
    obtain ⟨ε, hε, hL⟩ := reverse_prod_signed L h.2
    obtain ⟨η, hη, ha⟩ := mul_prod_signed a L h.1
    refine ⟨ε * η, hε.mul hη, ?_⟩
    rw [List.reverse_cons, List.prod_append, List.prod_singleton, hL, List.prod_cons, ha,
      smul_mul_assoc, smul_smul]
    rw [mul_assoc, hη.mul_self, mul_one]

end Generic

/-! ## The reversal anti-automorphism of `OPol` -/

variable {N : ℕ}

/-- `rev : OPol_N → OPol_Nᵐᵒᵖ`, `x_j ↦ x_j`. -/
def revHom (N : ℕ) : SkewPolynomial N →+* (SkewPolynomial N)ᵐᵒᵖ :=
  skewLift (fun j => MulOpposite.op (generator j)) (fun i j h => by
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, ← MulOpposite.op_add, add_comm,
      generator_anticomm i j h, neg_add_cancel, MulOpposite.op_zero])

/-- The reversal of products, `rev(f g) = rev(g) rev(f)`, `rev(x_j) = x_j`. -/
def rev (f : SkewPolynomial N) : SkewPolynomial N := MulOpposite.unop (revHom N f)

@[simp] theorem rev_generator (j : Fin N) : rev (generator j) = generator j := by
  simp [rev, revHom]

theorem rev_mul (f g : SkewPolynomial N) : rev (f * g) = rev g * rev f := by
  simp [rev]

@[simp] theorem rev_one : rev (1 : SkewPolynomial N) = 1 := by simp [rev]

@[simp] theorem rev_zero : rev (0 : SkewPolynomial N) = 0 := by simp [rev]

theorem rev_add (f g : SkewPolynomial N) : rev (f + g) = rev f + rev g := by simp [rev]

theorem rev_neg (f : SkewPolynomial N) : rev (-f) = -rev f := by simp [rev]

theorem rev_sub (f g : SkewPolynomial N) : rev (f - g) = rev f - rev g := by simp [rev]

theorem rev_zsmul (c : ℤ) (f : SkewPolynomial N) : rev (c • f) = c • rev f := by
  rw [rev, map_zsmul, MulOpposite.unop_smul]
  rfl

theorem rev_sum {ι : Type*} (s : Finset ι) (f : ι → SkewPolynomial N) :
    rev (∑ i ∈ s, f i) = ∑ i ∈ s, rev (f i) := by
  simp [rev]

theorem unop_ringHom_list_prod {R S : Type*} [Ring R] [Ring S] (φ : R →+* Sᵐᵒᵖ) (L : List R) :
    MulOpposite.unop (φ L.prod) = (L.map fun x => MulOpposite.unop (φ x)).reverse.prod := by
  rw [map_list_prod, MulOpposite.unop_list_prod, List.map_map]
  rfl

theorem rev_list_prod (L : List (SkewPolynomial N)) : rev L.prod = (L.map rev).reverse.prod :=
  unop_ringHom_list_prod (revHom N) L

theorem rev_rev (f : SkewPolynomial N) : rev (rev f) = f := by
  induction f using induction_generator with
  | hgen j => simp
  | h0 => simp
  | h1 => simp
  | hadd f g hf hg => rw [rev_add, rev_add, hf, hg]
  | hneg f hf => rw [rev_neg, rev_neg, hf]
  | hmul f g hf hg => rw [rev_mul, rev_mul, hf, hg]

/-- `rev` commutes with every ring endomorphism sending each `x_j` to a multiple of a generator. -/
theorem rev_ringHom (σ : SkewPolynomial N →+* SkewPolynomial N)
    (hσ : ∀ j, rev (σ (generator j)) = σ (generator j)) (f : SkewPolynomial N) :
    rev (σ f) = σ (rev f) := by
  induction f using induction_generator with
  | hgen j => rw [hσ, rev_generator]
  | h0 => simp
  | h1 => simp
  | hadd f g hf hg => rw [map_add, rev_add, rev_add, map_add, hf, hg]
  | hneg f hf => rw [map_neg, rev_neg, rev_neg, map_neg, hf]
  | hmul f g hf hg => rw [map_mul, rev_mul, rev_mul, map_mul, hf, hg]

theorem rev_longestPerm (f : SkewPolynomial N) : rev (longestPerm N f) = longestPerm N (rev f) :=
  rev_ringHom _ (fun j => by simp) f

theorem rev_theta (f : SkewPolynomial N) : rev (theta N f) = theta N (rev f) :=
  rev_ringHom _ (fun j => by rw [theta_generator, rev_zsmul, rev_generator]) f

theorem rev_skewAction (f : SkewPolynomial N) :
    rev (SignedPermutation.skewAction (LongestElementary.longest N) f) =
      SignedPermutation.skewAction (LongestElementary.longest N) (rev f) :=
  rev_ringHom (SignedPermutation.skewAction (LongestElementary.longest N)).toRingHom
    (fun j => by
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        SignedPermutation.action_generator]
      rw [rev_zsmul, rev_generator]) f

/-- `rev(x^a) = ± x^a`. -/
theorem rev_monomial (a : Fin N → ℕ) :
    ∃ ε, IsSign ε ∧ rev (monomial a 1) = ε • monomial a 1 := by
  rw [MonomialReversal.monomial_eq_prod, rev_list_prod]
  have hmap : (List.ofFn fun i => generator i ^ a i).map rev =
      List.ofFn fun i => (generator i ^ a i : SkewPolynomial N) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply]
    induction a i with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, rev_mul, ih, rev_generator]
      exact (pow_mul_comm' _ _).symm
  rw [hmap]
  apply reverse_prod_signed
  rw [List.pairwise_ofFn]
  intro i j hij
  exact ⟨(-1 : ℤ) ^ (a i * a j), IsSign.pow _, OnhReflection.pow_mul_pow_anti
    (EQSkewDifferential.generator_anticomm i j (Fin.ne_of_lt hij)) (a i) (a j)⟩


/-! ## `rev` on odd symmetric polynomials -/

section Generic2

variable {R : Type*} [Ring R]

theorem mul_prod_anticomm (a : R) :
    ∀ L : List R, (∀ v ∈ L, a * v = -(v * a)) → a * L.prod = (-1 : ℤ) ^ L.length • (L.prod * a)
  | [], _ => by simp
  | b :: L, h => by
    have hL := mul_prod_anticomm a L (fun v hv => h v (List.mem_cons_of_mem _ hv))
    rw [List.prod_cons, ← mul_assoc, h b List.mem_cons_self, neg_mul, mul_assoc, hL,
      mul_smul_comm, List.length_cons, pow_succ, mul_neg_one, neg_smul, ← mul_assoc]

/-- Reversing a product of pairwise anticommuting elements: `(-1)^{binom(k,2)}`. -/
theorem reverse_prod_anticomm :
    ∀ L : List R, L.Pairwise (fun u v => u * v = -(v * u)) →
      L.reverse.prod = (-1 : ℤ) ^ L.length.choose 2 • L.prod
  | [], _ => by simp
  | a :: L, h => by
    rw [List.pairwise_cons] at h
    rw [List.reverse_cons, List.prod_append, List.prod_singleton, reverse_prod_anticomm L h.2,
      List.prod_cons, mul_prod_anticomm a L h.1, smul_mul_assoc, smul_smul, ← pow_add,
      List.length_cons, choose_two_succ]
    congr 1
    rw [add_assoc, pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

end Generic2

theorem rev_elementaryPoly (k : ℕ) :
    rev (FiniteCompleteElementary.elementaryPoly N k) =
      (-1 : ℤ) ^ k.choose 2 • FiniteCompleteElementary.elementaryPoly N k := by
  classical
  unfold FiniteCompleteElementary.elementaryPoly
  rw [rev_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  split_ifs with hf
  · rw [rev_list_prod]
    have hm : (List.ofFn fun i => PlacticEvaluation.tildeGenerator (f i)).map rev =
        List.ofFn fun i => PlacticEvaluation.tildeGenerator (f i) := by
      rw [List.map_ofFn]
      congr 1
      funext i
      simp only [Function.comp_apply, PlacticEvaluation.tildeGenerator, rev_zsmul, rev_generator]
    rw [hm, reverse_prod_anticomm, List.length_ofFn]
    rw [List.pairwise_ofFn]
    intro i j hij
    have hne : f i ≠ f j := (hf hij).ne
    simp only [PlacticEvaluation.tildeGenerator, smul_mul_assoc, mul_smul_comm, smul_smul,
      generator_anticomm _ _ hne, smul_neg, mul_comm ((-1 : ℤ) ^ (f i).val)]
  · simp

/-- `rev` preserves the odd symmetric polynomials `OΛ̃_{n+2}` (EKL's common kernel). -/
theorem rev_mem_kernel {n : ℕ} {f : SkewPolynomial (n+2)}
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    rev f ∈ OddSymmetricKernel.kernelSubring n := by
  rw [← StaircaseIndependence.E_eq_kernel] at hf ⊢
  induction hf using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [rev_elementaryPoly]
    exact Subring.zsmul_mem _ (Subring.subset_closure (Set.mem_range_self k)) _
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [rev_add]; exact add_mem hx hy
  | neg x _ hx => rw [rev_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [rev_mul]; exact mul_mem hy hx

/-! ## `ψ` on the dot subring and the reversal of `∂_{w₀}` -/

open NilHeckeAction OnhPolynomial NilHeckeRightBasis in
/-- EKL's anti-automorphism `ψ` restricts to `rev` on the dot subring. -/
theorem reverse_polyElem {n : ℕ} (f : SkewPolynomial (n+2)) :
    reverseLinear n (polyElem n f) = polyElem n (rev f) := by
  induction f using induction_generator with
  | hgen j => rw [rev_generator, polyElem_generator, reverse_dot]
  | h0 => simp
  | h1 => simp
  | hadd f g hf hg => rw [map_add, map_add, hf, hg, rev_add, map_add]
  | hneg f hg => rw [map_neg, map_neg, hg, rev_neg, map_neg]
  | hmul f g hf hg => rw [map_mul, reverse_mul, hf, hg, rev_mul, map_mul]

theorem skewAction_longest_small {N : ℕ} (hN : N ≤ 1) (f : SkewPolynomial N) :
    SignedPermutation.skewAction (LongestElementary.longest N) f = f := by
  have h : LongestElementary.longest N = 1 := by
    rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl <;> exact Subsingleton.elim _ _
  rw [h, SignedPermutation.action_one]

open NilHeckeAction OnhPolynomial NilHeckeRightBasis ZeroHecke in
/-- `∂_{w₀}(rev g) = (-1)^{binom(N,4)} w₀(rev(∂_{w₀} g))` (EKL's signed action of `w₀`), for every
polynomial `g`: apply `ψ` to `∂_{w₀} g ∂_{w₀} = ∂_{w₀}(g) ∂_{w₀}`. -/
theorem D_rev (g : SkewPolynomial N) :
    LongestDivided.D N (rev g) = (-1 : ℤ) ^ N.choose 4 •
      SignedPermutation.skewAction (LongestElementary.longest N) (rev (LongestDivided.D N g)) := by
  rcases N with _ | _ | n
  · rw [skewAction_longest_small (by omega)]
    simp [LongestDivided.D, Nat.choose_eq_zero_of_lt]
  · rw [skewAction_longest_small (by omega)]
    simp [LongestDivided.D, Nat.choose_eq_zero_of_lt]
  · set s : ℤ := (-1 : ℤ) ^ (n+2).choose 4
    have hs : s * s = 1 := (IsSign.pow _).mul_self
    have hD : reverseLinear n (DElem n) = s • DElem n := OnhReflection.reverse_DElem n
    have h1 := congrArg (reverseLinear n) (DElem_poly_DElem g)
    rw [reverse_mul, reverse_mul, reverse_mul, hD, reverse_polyElem, reverse_polyElem] at h1
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hs, one_smul] at h1
    rw [← mul_assoc, DElem_poly_DElem,
      DElem_poly_kernel _ (rev_mem_kernel (LongestKernel.D_mem_kernel n g))] at h1
    have h2 := congrArg (fun u => action n u (LongestDivided.staircase (n+2))) h1
    simp only [map_mul, map_zsmul, LinearMap.smul_apply, Module.End.mul_apply, action_polyElem,
      action_DElem, LongestDivided.D_staircase, mul_one] at h2
    have hc : ((-1 : ℤ) ^ (n+2).choose 3) * (-1) ^ (n+2).choose 3 = 1 := (IsSign.pow _).mul_self
    have h3 := congrArg (fun x => ((-1 : ℤ) ^ (n+2).choose 3) • x) h2
    simp only [smul_smul, hc, one_smul] at h3
    rw [h3, mul_left_comm, hc, mul_one]

/-- `rev(s̃_λ) = ± s̃̂_λ` in every rank: reversing products turns twisted odd Schur polynomials
into the hat ones. -/
theorem rev_twisted (l : Fin N → ℕ) :
    ∃ ε, IsSign ε ∧ rev (twisted N l) = ε • twistedHat N l := by
  set m := monomial l 1 * LongestDivided.staircase N with hm
  have hmono : ∃ ε, IsSign ε ∧ rev m = ε • m := by
    obtain ⟨ε, hε, he⟩ := rev_monomial (N := N) (l + delta N)
    refine ⟨ε, hε, ?_⟩
    rw [hm, staircase_eq_monomial, OddSchurPieri.mono_mul, rev_zsmul, he, smul_comm]
  obtain ⟨ε, hε, hrm⟩ := hmono
  -- `rev(∂ m) = s ε w₀^{EKL}(∂ m)`
  have hDm := D_rev (N := N) m
  rw [hrm, map_zsmul] at hDm
  have hrev : rev (LongestDivided.D N m) = ((-1 : ℤ) ^ N.choose 4 * ε) •
      SignedPermutation.skewAction (LongestElementary.longest N) (LongestDivided.D N m) := by
    have := congrArg (fun x => ((-1 : ℤ) ^ N.choose 4) •
      SignedPermutation.skewAction (LongestElementary.longest N) x) hDm
    simp only [map_zsmul, LongestElementary.action_involutive, smul_smul,
      (IsSign.pow (N.choose 4)).mul_self, one_smul] at this
    exact this.symm
  have hpar := parityInv_D_of l m (parityInv_mul_staircase l)
  rw [skewAction_longest _ _ hpar] at hrev
  have htw : rev (twisted N l) = ((-1 : ℤ) ^ (N.choose 3 + N.choose 2 * ∑ j, l j) *
      ((-1 : ℤ) ^ N.choose 4 * ε * (-1) ^ (N.choose 2 * ∑ j, l j))) • LongestDivided.D N m := by
    rw [twisted, rev_zsmul, rev_longestPerm, hrev, map_zsmul, map_zsmul, longestPerm_longestPerm,
      smul_smul, smul_smul, mul_assoc]
  have hsgn : IsSign (hatCorr N l * (-1) ^ pairSum l) := by
    unfold hatCorr; exact (IsSign.pow _).mul (IsSign.pow _)
  have hD : LongestDivided.D N m = (hatCorr N l * (-1) ^ pairSum l) • twistedHat N l := by
    rw [twistedHat_eq_D, smul_smul, hsgn.mul_self, one_smul]
  rw [htw, hD, smul_smul]
  exact ⟨_, ((IsSign.pow _).mul (((IsSign.pow _).mul hε).mul (IsSign.pow _))).mul hsgn, rfl⟩

end

end OddMath.Frontier.EQZab
