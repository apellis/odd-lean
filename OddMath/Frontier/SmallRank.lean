import OddMath.Frontier.NilHeckeSmallRank
import OddMath.Frontier.ElementaryGeneration
import OddMath.Frontier.OddSymmetrizer
import OddMath.Frontier.Cyclotomic
import OddMath.Frontier.NilHeckeBasis

/-!
# Ranks `0` and `1`: the polynomial side

EKL arXiv:1111.1320v1, §2.1–§2.3. Most results of the library are stated for rank `a = n+2 ≥ 2`
(`OPol_{n+2} = SkewPolynomial (n+2)`, `OΛ_{n+2} = OddSymmetricKernel.kernelSubring n`,
`ONH_{n+2} = NilHeckeAction.Presented n`). The paper states them for every `a ≥ 0`, with
`OPol_0 = OΛ_0 = ONH_0 = ℤ` and `OPol_1 = OΛ_1 = ONH_1 = ℤ[x]` (there are no divided
differences, so the joint kernel (2.12) is everything). This file supplies those objects and the
corresponding statements for every rank, reducing to the rank `≥ 2` theorems.

* `ONH a`: `ONH_0 = ℤ`, `ONH_1 = OPol_1`, `ONH_{n+2} = Presented n`; `OLam N`: `⊤` for `N ≤ 1`
  and `kernelSubring n` for `N = n+2`.
* `zeroEquiv : OPol_0 ≃+* ℤ` and `rankOneEquiv : OPol_1 ≃+* ℤ[X]` (so `OPol_1` is commutative
  and a domain).
* Prop 2.2 for every `N` (`OLam_eq_elementaryClosure`); Prop 2.13 for `N ≤ 1`
  (`kernel_decomposition_small`, `right_kernel_decomposition_small`); (2.64) for every `N`
  (`D_left_kernel_all`); Cor 2.22 for every `N` (`Sym`, `Sym_mem`, `Sym_eq_self`,
  `Sym_idempotent`, `Sym_left_kernel`); Def 2.24 for every `N` (`schurAll`) and the Pieri rules
  (2.71)–(2.74) for `N ≤ 1` (`schurAll_mul_small`); Prop 2.15 for `N ≤ 1` (`center_OLam_small`,
  `center_OLam_one`; the paper states it for `a ≥ 2`); Prop 2.11 (faithfulness of `ONH_a` on
  `OPol_a`) for every `a` (`act_injective`).

Statements that involve a divided difference `∂_i` or a crossing (Prop 2.1, (2.4), (2.6), (2.11),
Lemmas 2.18–2.21, (2.59)–(2.63)) are vacuous for `a ≤ 1`: there is no index `i`. Lemma 2.10,
Cor 2.23 and Props 4.6–4.7 are already stated for every `N` (`LongestDivided.D 0 = D 1 = id`).
-/

namespace OddMath.Frontier.SmallRank
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open scoped BigOperators

noncomputable section

/-! ## The objects -/

/-- `ONH_a` for every `a ≥ 0`: `ONH_0 = ℤ`, `ONH_1 = OPol_1`, `ONH_{n+2} = Presented n`
(EKL §2.2; for `a ≤ 1` there are no crossings). -/
def ONH : ℕ → Type
  | 0 => ℤ
  | 1 => SkewPolynomial 1
  | n+2 => NilHeckeAction.Presented n

instance ONH.ring : ∀ a, Ring (ONH a)
  | 0 => inferInstanceAs (Ring ℤ)
  | 1 => inferInstanceAs (Ring (SkewPolynomial 1))
  | n+2 => inferInstanceAs (Ring (NilHeckeAction.Presented n))

/-- `OΛ_N ⊂ OPol_N`, EKL (2.12): the joint kernel of the `∂_i`, which is all of `OPol_N` for
`N ≤ 1`. -/
def OLam : (N : ℕ) → Subring (SkewPolynomial N)
  | 0 => ⊤
  | 1 => ⊤
  | n+2 => OddSymmetricKernel.kernelSubring n

theorem OLam_small {N : ℕ} (hN : N ≤ 1) : OLam N = ⊤ := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl <;> rfl

theorem OLam_add_two (n : ℕ) : OLam (n+2) = OddSymmetricKernel.kernelSubring n := rfl

/-! ## `OPol_0 = ℤ` -/

theorem exp_zero_eq (a : Fin 0 → ℕ) : a = 0 := funext fun i => i.elim0

/-- `OPol_0 ≅ ℤ`, by the constant coefficient. -/
def zeroEquiv : SkewPolynomial 0 ≃+* ℤ :=
  RingEquiv.ofBijective (Cyclotomic.constTerm 0)
    ⟨fun f g h => Finsupp.ext fun a => by rw [exp_zero_eq a]; exact h,
     fun z => ⟨(z : SkewPolynomial 0), by simp⟩⟩

@[simp] theorem zeroEquiv_apply (f : SkewPolynomial 0) : zeroEquiv f = f 0 := rfl

theorem eq_intCast_zero (f : SkewPolynomial 0) : f = ((f 0 : ℤ) : SkewPolynomial 0) := by
  apply zeroEquiv.injective
  rw [map_intCast]
  rfl

/-! ## `OPol_1 = ℤ[x]` -/

theorem skewSign_one (a b : Fin 1 → ℕ) : OddMath.skewSign a b = 1 := by
  simp [OddMath.skewSign, OddMath.crossingCount]

/-- The exponent of a rank-one monomial. -/
def expEquiv : (Fin 1 → ℕ) ≃ ℕ := Equiv.funUnique (Fin 1) ℕ

/-- The additive identification `OPol_1 ≃ ℤ[X]`, `x^k ↦ X^k`. -/
def rankOneAdd : SkewPolynomial 1 ≃+ Polynomial ℤ :=
  (Finsupp.domCongr expEquiv).trans (Polynomial.toFinsuppIso ℤ).symm.toAddEquiv

theorem rankOneAdd_monomial (a : Fin 1 → ℕ) (c : ℤ) :
    rankOneAdd (monomial a c) = Polynomial.monomial (a 0) c := by
  simp only [rankOneAdd, monomial, AddEquiv.trans_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single]
  exact Polynomial.ofFinsupp_single (a 0) c

theorem rankOneAdd_mul (f g : SkewPolynomial 1) :
    rankOneAdd (f * g) = rankOneAdd f * rankOneAdd g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
  | single a r =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
    | single b s =>
      change rankOneAdd (monomial a r * monomial b s) =
        rankOneAdd (monomial a r) * rankOneAdd (monomial b s)
      rw [MonomialReversal.monomial_mul_monomial, skewSign_one, mul_one, rankOneAdd_monomial,
        rankOneAdd_monomial, rankOneAdd_monomial, Polynomial.monomial_mul_monomial]
      rfl

/-- `OPol_1 ≅ ℤ[X]` as rings, `x ↦ X`. -/
def rankOneEquiv : SkewPolynomial 1 ≃+* Polynomial ℤ :=
  { rankOneAdd with map_mul' := rankOneAdd_mul }

@[simp] theorem rankOneEquiv_monomial (a : Fin 1 → ℕ) (c : ℤ) :
    rankOneEquiv (monomial a c) = Polynomial.monomial (a 0) c :=
  rankOneAdd_monomial a c

@[simp] theorem rankOneEquiv_generator : rankOneEquiv (generator 0) = Polynomial.X := by
  rw [generator, rankOneEquiv_monomial]
  simp [OddMath.SkewPolynomial.expSingle, Polynomial.X]

/-- `OPol_1` is commutative. -/
theorem rankOne_mul_comm (f g : SkewPolynomial 1) : f * g = g * f :=
  rankOneEquiv.injective (by rw [map_mul, map_mul, mul_comm])

/-- `OPol_N` is commutative for `N ≤ 1`. -/
theorem small_mul_comm {N : ℕ} (hN : N ≤ 1) (f g : SkewPolynomial N) : f * g = g * f := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
  · exact zeroEquiv.injective (by rw [map_mul, map_mul, mul_comm])
  · exact rankOne_mul_comm f g

/-- `OPol_1` has no zero divisors. -/
theorem rankOne_eq_zero_or_eq_zero {f g : SkewPolynomial 1} (h : f * g = 0) : f = 0 ∨ g = 0 := by
  have h' : rankOneEquiv f * rankOneEquiv g = 0 := by rw [← map_mul, h, map_zero]
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact Or.inl (rankOneEquiv.map_eq_zero_iff.mp h0)
  · exact Or.inr (rankOneEquiv.map_eq_zero_iff.mp h0)

/-- Every element of `OPol_1` lies in the subring generated by `x`. -/
theorem mem_closure_generator (f : SkewPolynomial 1) :
    f ∈ Subring.closure {generator (0 : Fin 1)} := by
  let S := (Subring.closure {generator (0 : Fin 1)}).comap rankOneEquiv.symm.toRingHom
  have hX : Polynomial.X ∈ S := by
    rw [Subring.mem_comap]
    show rankOneEquiv.symm Polynomial.X ∈ Subring.closure {generator (0 : Fin 1)}
    rw [← rankOneEquiv_generator, RingEquiv.symm_apply_apply]
    exact Subring.subset_closure rfl
  have hall : ∀ p : Polynomial ℤ, p ∈ S := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact S.add_mem hp hq
    | monomial k c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, eq_intCast]
      exact S.mul_mem (intCast_mem S c) (S.pow_mem hX k)
  have := Subring.mem_comap.mp (hall (rankOneEquiv f))
  simpa using this

/-! ## `h_m` in ranks `0` and `1` -/

/-- In no variables, `h_m = 0` for `m > 0`. -/
theorem completePoly_zero_succ (m : ℕ) : FiniteCompleteElementary.completePoly 0 (m+1) = 0 := by
  rw [FiniteCompleteElementary.completePoly_eq_weakSum,
    FiniteCompleteElementary.FiniteWords.weakSum_empty]

/-- In one variable, `h_m = x^m`. -/
theorem completePoly_one (m : ℕ) :
    FiniteCompleteElementary.completePoly 1 m = generator 0 ^ m := by
  induction m with
  | zero => rw [FiniteCompleteElementary.completePoly_zero, pow_zero]
  | succ m ih =>
    rw [FiniteCompleteElementary.completePoly_eq_weakSum,
      FiniteCompleteElementary.FiniteWords.weakSum_succ,
      FiniteCompleteElementary.FiniteWords.weakSum_empty, add_zero,
      ← FiniteCompleteElementary.completePoly_eq_weakSum, ih, pow_succ',
      PlacticEvaluation.tildeGenerator]
    simp

/-! ## Prop 2.2 in every rank -/

theorem elementaryPoly_one_one : FiniteCompleteElementary.elementaryPoly 1 1 = generator 0 := by
  rw [FiniteCompleteElementary.elementaryPoly_eq_strictSum]
  simp [FiniteCompleteElementary.FiniteWords.strictSum_succ, PlacticEvaluation.tildeGenerator]

/-- **EKL Prop 2.2** (proof, p. 8), every rank `N`: `OΛ_N` is generated by `ε_1, …, ε_N`.
For `N = n+2` this is `ElementaryGeneration.kernel_eq_elementaryClosure`. -/
theorem OLam_eq_elementaryClosure (N : ℕ) :
    OLam N = Subring.closure
      {f | ∃ k, 1 ≤ k ∧ k ≤ N ∧ f = FiniteCompleteElementary.elementaryPoly N k} := by
  match N with
  | 0 =>
    refine (eq_top_iff.mpr fun f _ => ?_).symm
    rw [eq_intCast_zero f]
    exact intCast_mem _ _
  | 1 =>
    refine (eq_top_iff.mpr fun f _ => ?_).symm
    refine Subring.closure_mono ?_ (mem_closure_generator f)
    rintro _ rfl
    exact ⟨1, le_rfl, le_rfl, elementaryPoly_one_one.symm⟩
  | n+2 => exact ElementaryGeneration.kernel_eq_elementaryClosure n

/-! ## Staircase, longest element and `D_N` in ranks `0, 1` -/

theorem staircase_small {N : ℕ} (hN : N ≤ 1) : LongestDivided.staircase N = 1 := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
  · rw [LongestDivided.staircase, exp_zero_eq (fun i => _)]
    rfl
  · have h : (fun i : Fin 1 => 1 - 1 - i.val) = 0 := funext fun i => by simp
    rw [LongestDivided.staircase, h]
    rfl

theorem longest_small {N : ℕ} (hN : N ≤ 1) : LongestElementary.longest N = 1 := by
  ext i
  have : ∀ j k : Fin N, j = k := fun j k => Fin.ext (by have := j.isLt; have := k.isLt; omega)
  exact congrArg Fin.val (this _ _)

theorem skewAction_longest_small {N : ℕ} (hN : N ≤ 1) (f : SkewPolynomial N) :
    SignedPermutation.skewAction (LongestElementary.longest N) f = f := by
  rw [longest_small hN, SignedPermutation.action_one]

theorem D_small {N : ℕ} (hN : N ≤ 1) (f : SkewPolynomial N) : LongestDivided.D N f = f := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl <;> rfl

theorem mem_OLam_small {N : ℕ} (hN : N ≤ 1) (f : SkewPolynomial N) : f ∈ OLam N := by
  rw [OLam_small hN]
  trivial

/-! ## Prop 2.13, (2.64) and Cor 2.22 in every rank -/

/-- **EKL Prop 2.13**, `N ≤ 1`: `OPol_N` is free over `OΛ_N` on the single Schubert polynomial
`s_e = x^δ = 1`. For `N = n+2` see `SchubertBasis.left_kernel_decomposition_unique`. -/
theorem kernel_decomposition_small {N : ℕ} (hN : N ≤ 1) (f : SkewPolynomial N) :
    ∃! c : OLam N, f = (c : SkewPolynomial N) * LongestDivided.staircase N := by
  refine ⟨⟨f, mem_OLam_small hN f⟩, by show f = f * _; rw [staircase_small hN, mul_one],
    fun c hc => ?_⟩
  rw [staircase_small hN, mul_one] at hc
  exact Subtype.ext hc.symm

/-- **EKL (2.64)** in every rank: `D_N(f g) = f^{w_0} D_N(g)` for `f ∈ OΛ_N`. For `N = n+2` this
is `OddSymmetrizer.D_left_kernel`. -/
theorem D_left_kernel_all (N : ℕ) (f g : SkewPolynomial N) (hf : f ∈ OLam N) :
    LongestDivided.D N (f * g) =
      SignedPermutation.skewAction (LongestElementary.longest N) f * LongestDivided.D N g := by
  match N, f, g, hf with
  | 0, f, g, _ => rw [D_small (by omega), D_small (by omega), skewAction_longest_small (by omega)]
  | 1, f, g, _ => rw [D_small le_rfl, D_small le_rfl, skewAction_longest_small le_rfl]
  | n+2, f, g, hf => exact OddSymmetrizer.D_left_kernel n f g hf

/-- The odd symmetrizer `S` of EKL (2.57) in every rank:
`S(f) = (-1)^{C(N,3)} (D_N(f x^δ))^{w_0}`. For `N = n+2` it is `OddSymmetrizer.S n`
(`Sym_add_two`); for `N ≤ 1` it is the identity. -/
def Sym (N : ℕ) : SkewPolynomial N →ₗ[ℤ] SkewPolynomial N where
  toFun f := (-1 : ℤ)^(N.choose 3) • SignedPermutation.skewAction (LongestElementary.longest N)
    (LongestDivided.D N (f * LongestDivided.staircase N))
  map_add' f g := by simp only [add_mul, map_add, smul_add]
  map_smul' z f := by
    simp only [smul_mul_assoc, map_smul, map_zsmul, RingHom.id_apply]
    exact smul_comm _ _ _

theorem Sym_add_two (n : ℕ) : Sym (n+2) = OddSymmetrizer.S n := rfl

theorem Sym_small {N : ℕ} (hN : N ≤ 1) (f : SkewPolynomial N) : Sym N f = f := by
  change (-1 : ℤ)^(N.choose 3) • _ = f
  rw [staircase_small hN, mul_one, D_small hN, skewAction_longest_small hN,
    Nat.choose_eq_zero_of_lt (by omega), pow_zero, one_smul]

/-- **EKL Cor 2.22**, every rank: `S` lands in `OΛ_N`. -/
theorem Sym_mem (N : ℕ) (f : SkewPolynomial N) : Sym N f ∈ OLam N := by
  match N, f with
  | 0, f => exact mem_OLam_small (by omega) _
  | 1, f => exact mem_OLam_small le_rfl _
  | n+2, f => exact OddSymmetrizer.S_mem_kernel n f

/-- **EKL Cor 2.22** and (2.65), every rank: `S(f) = f` for `f ∈ OΛ_N`. -/
theorem Sym_eq_self (N : ℕ) (f : SkewPolynomial N) (hf : f ∈ OLam N) : Sym N f = f := by
  match N, f, hf with
  | 0, f, _ => exact Sym_small (by omega) f
  | 1, f, _ => exact Sym_small le_rfl f
  | n+2, f, hf => exact OddSymmetrizer.S_eq_self n f hf

/-- **EKL Cor 2.22**, every rank: `S` is idempotent. -/
theorem Sym_idempotent (N : ℕ) (f : SkewPolynomial N) : Sym N (Sym N f) = Sym N f :=
  Sym_eq_self N _ (Sym_mem N f)

/-- **EKL Cor 2.22**, every rank: `S(f g) = f S(g)` for `f ∈ OΛ_N`. -/
theorem Sym_left_kernel (N : ℕ) (f g : SkewPolynomial N) (hf : f ∈ OLam N) :
    Sym N (f * g) = f * Sym N g := by
  match N, f, g, hf with
  | 0, f, g, _ => rw [Sym_small (by omega), Sym_small (by omega)]
  | 1, f, g, _ => rw [Sym_small le_rfl, Sym_small le_rfl]
  | n+2, f, g, hf => exact OddSymmetrizer.S_left_kernel n f g hf

/-- The odd Schur polynomial of EKL Def 2.24 (2.69) in every rank, `s_α = S(x^α)`. For
`N = n+2` it is `OddSymmetrizer.schur n α`. -/
def schurAll (N : ℕ) (α : Fin N → ℕ) : SkewPolynomial N := Sym N (monomial α 1)

theorem schurAll_add_two (n : ℕ) (α : OddSymmetrizer.PartitionExponent n) :
    schurAll (n+2) α.val = OddSymmetrizer.schur n α := rfl

/-- In ranks `0` and `1`, `s_α = x^α`. -/
theorem schurAll_small {N : ℕ} (hN : N ≤ 1) (α : Fin N → ℕ) : schurAll N α = monomial α 1 :=
  Sym_small hN _

theorem skewSign_small {N : ℕ} (hN : N ≤ 1) (a b : Fin N → ℕ) : OddMath.skewSign a b = 1 := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
  · simp [OddMath.skewSign, OddMath.crossingCount]
  · exact skewSign_one a b

/-- **EKL Prop 2.26** (2.71) and Remark 2.27 (2.72)–(2.74) in ranks `a ≤ 1`: a product of odd Schur
polynomials is the single Schur polynomial `s_α s_β = s_{α+β}` (one strip, sign `+1`). For
`a ≥ 2` see `OddSchurPieri.right_pieri` and `EKLSectionTwo.horizontal_pieri`. -/
theorem schurAll_mul_small {N : ℕ} (hN : N ≤ 1) (α β : Fin N → ℕ) :
    schurAll N α * schurAll N β = schurAll N (α + β) := by
  rw [schurAll_small hN, schurAll_small hN, schurAll_small hN,
    MonomialReversal.monomial_mul_monomial, skewSign_small hN, mul_one, mul_one]

/-- **EKL Prop 2.13** (right form), `N ≤ 1`: `OPol_N = s_e OΛ_N` with `s_e = x^δ = 1`. For
`N = n+2` see `SchubertBasis.right_kernel_decomposition_unique`. -/
theorem right_kernel_decomposition_small {N : ℕ} (hN : N ≤ 1) (f : SkewPolynomial N) :
    ∃! c : OLam N, f = LongestDivided.staircase N * (c : SkewPolynomial N) := by
  refine ⟨⟨f, mem_OLam_small hN f⟩, by show f = _ * f; rw [staircase_small hN, one_mul],
    fun c hc => ?_⟩
  rw [staircase_small hN, one_mul] at hc
  exact Subtype.ext hc.symm

/-! ## Prop 2.15 for `N ≤ 1` -/

/-- **EKL Prop 2.15** (as corrected, `CenterCorrected.center_oddSymmetric`), `N ≤ 1`: `OΛ_N` is
commutative, so its centre is everything. -/
theorem center_OLam_small {N : ℕ} (hN : N ≤ 1) : Subring.center (OLam N) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => Subring.mem_center_iff.mpr fun w => Subtype.ext ?_
  exact small_mul_comm hN _ _

/-- The corrected description of the centre at `N = 1` (odd rank): every element of `OΛ_1 = ℤ[x]`
is `a + x b` with `a, b` symmetric polynomials in `x²`, i.e. in `ℤ[x²]`. -/
theorem center_OLam_one (f : SkewPolynomial 1) :
    ∃ a ∈ Subring.closure {generator (0 : Fin 1) ^ 2},
      ∃ b ∈ Subring.closure {generator (0 : Fin 1) ^ 2}, f = a + generator 0 * b := by
  set C := Subring.closure {generator (0 : Fin 1) ^ 2}
  have hx2 : generator (0 : Fin 1) ^ 2 ∈ C := Subring.subset_closure rfl
  induction mem_closure_generator f using Subring.closure_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨0, C.zero_mem, 1, C.one_mem, by rw [zero_add, mul_one]⟩
  | zero => exact ⟨0, C.zero_mem, 0, C.zero_mem, by rw [mul_zero, add_zero]⟩
  | one => exact ⟨1, C.one_mem, 0, C.zero_mem, by rw [mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    exact ⟨a + a', C.add_mem ha ha', b + b', C.add_mem hb hb', by rw [mul_add]; abel⟩
  | neg x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨-a, C.neg_mem ha, -b, C.neg_mem hb, by rw [mul_neg, neg_add]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a' + generator 0 ^ 2 * (b * b'), C.add_mem (C.mul_mem ha ha')
      (C.mul_mem hx2 (C.mul_mem hb hb')), a * b' + b * a',
      C.add_mem (C.mul_mem ha hb') (C.mul_mem hb ha'), ?_⟩
    apply rankOneEquiv.injective
    simp only [map_add, map_mul, map_pow]
    ring

/-! ## Prop 2.11: `ONH_a` acts faithfully on `OPol_a`, every rank -/

/-- Left multiplication `OPol_1 → End(OPol_1)`. -/
def lmulOne : SkewPolynomial 1 →+* Module.End ℤ (SkewPolynomial 1) where
  toFun g := LinearMap.mulLeft ℤ g
  map_one' := LinearMap.ext fun f => one_mul f
  map_mul' g h := LinearMap.ext fun f => mul_assoc g h f
  map_zero' := LinearMap.ext fun f => zero_mul f
  map_add' g h := LinearMap.ext fun f => add_mul g h f

/-- The action of `ONH_a` on `OPol_a` (EKL §2.2): scalars for `a = 0`, left multiplication for
`a = 1`, `NilHeckeAction.action` for `a ≥ 2`. -/
def act : (a : ℕ) → ONH a →+* Module.End ℤ (SkewPolynomial a)
  | 0 => Int.castRingHom (Module.End ℤ (SkewPolynomial 0))
  | 1 => lmulOne
  | n+2 => NilHeckeAction.action n

/-- **EKL Prop 2.11** (faithfulness), every rank. For `a = n+2` this is
`NilHeckeBasis.action_injective`. -/
theorem act_injective : ∀ a, Function.Injective (act a)
  | 0 => fun (z w : ℤ) h => by
    have h1 := congrArg (fun T : Module.End ℤ (SkewPolynomial 0) => zeroEquiv (T 1)) h
    change zeroEquiv (z • (1 : SkewPolynomial 0)) = zeroEquiv (w • 1) at h1
    simpa only [map_zsmul, map_one, smul_eq_mul, mul_one] using h1
  | 1 => fun f g h => by
    have := LinearMap.congr_fun h 1
    simpa [act, lmulOne] using this
  | n+2 => NilHeckeBasis.action_injective n

end

end OddMath.Frontier.SmallRank
