import OddMath.Frontier.EQLimaPoly
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Ellis–Qi, Proposition A.3: `H(OΛ)` is a polynomial algebra

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Proposition A.3: the cohomology ring `H(OΛ)` is a polynomial algebra on either of the sets
`{s_{(2,…,2)}}` (`2k` twos) and `{s_{(2k,2k)}}`.

Here `H(OΛ) = HQ` is the cohomology ring of the dg algebra `OΛ` (`EQLimaLimit`), which is
commutative (`HQ.instCommRing`). We prove, for `k ≥ 1`:

* `prop_A_3_columns`: `ℤ[X_0, X_1, …] → H(OΛ)`, `X_a ↦ [s_{(2^{2(a+1)})}]`, is an isomorphism;
* `prop_A_3_rows`: `ℤ[X_0, X_1, …] → H(OΛ)`, `X_a ↦ [s_{(2(a+1), 2(a+1))}]`, is an isomorphism.

The proof is the paper's leading-term argument, in cohomology: `tri_monomial` shows that a
monomial in the generators is `±[s_λ]` plus classes `[s_μ]` with `μ` dominated by `λ`
(respectively with `μᵀ` dominated by `λᵀ`), where `λ` runs bijectively over the Lima partitions
(`colEquiv`). This is the corrected form of (A.1): the leading coefficient is proved to be `±1`
(not `1`), and the other coefficients need not be non-negative; the dominance bounds come from
the Littlewood–Richardson rule (`EQLimaLR`), not from an equality of odd and even
Littlewood–Richardson coefficients.

Deviation from the printed statement: the printed index sets include `k = 0`, whose generator
`s_∅ = 1` cannot be a polynomial generator; the generators here are indexed by `k ≥ 1`.
-/

namespace OddMath.Frontier.EQLima

open Finset
open OddLRTableau (oddLR)
open OddLREKIdentification (sK)

noncomputable section

/-- Lima partitions. -/
abbrev Lima : Type := {μ : YoungDiagram // IsLima μ}

/-- Coordinates of a cohomology class in the basis of Lima classes. -/
def coord (x : HQ) : Lima →₀ ℤ := HQ_basis.repr x

theorem coord_limaClass_mul (μ β lam : Lima) :
    coord (limaClass μ * limaClass β) lam = oddLR lam.1 μ.1 β.1 := by
  rw [limaClass_mul, coord]
  have : (limaCoords (sK μ.1 * sK β.1)).sum (fun lam a => a • limaClass lam) =
      Finsupp.linearCombination ℤ HQ_basis (limaCoords (sK μ.1 * sK β.1)) := by
    rw [Finsupp.linearCombination_apply]
    simp only [HQ_basis_apply]
  rw [this, Module.Basis.repr_linearCombination]
  rfl

theorem coord_mul (μ : Lima) (x : HQ) (lam : Lima) :
    coord (limaClass μ * x) lam = (coord x).sum (fun β c => c * oddLR lam.1 μ.1 β.1) := by
  conv_lhs => rw [← HQ_basis.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.mul_sum, coord, map_finsuppSum,
    Finsupp.sum_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [mul_smul_comm, map_zsmul, Finsupp.smul_apply, smul_eq_mul, HQ_basis_apply]
  rw [show HQ_basis.repr (limaClass μ * limaClass β) lam = oddLR lam.1 μ.1 β.1 from
    coord_limaClass_mul μ β lam]
  rfl

theorem card_of_oddLR_ne_zero {lam μ β : YoungDiagram} (h : oddLR lam μ β ≠ 0) :
    lam.card = μ.card + β.card := by
  by_contra hc
  exact h (by rw [OddLRRule.thm_4_8, OddLRRule.lrSignedCount_eq_zero hc])

/-! ### Twists: dominance and transposed dominance -/

/-- The data for one of the two leading-term arguments: `τ = id` (column generators, dominance)
or `τ = transpose` (row generators, dominance of transposes). -/
structure Twist where
  /-- the twist -/
  τ : YoungDiagram → YoungDiagram
  invol : ∀ μ, τ (τ μ) = μ
  card : ∀ μ, (τ μ).card = μ.card
  lima : ∀ μ, IsLima μ → IsLima (τ μ)
  bot : τ ⊥ = ⊥
  dom : ∀ lam μ β, oddLR lam μ β ≠ 0 → Dom (τ lam) (addRows (τ μ) (τ β))
  lead : ∀ μ β, oddLR (τ (addRows (τ μ) (τ β))) μ β = 1 ∨
    oddLR (τ (addRows (τ μ) (τ β))) μ β = -1

/-- `τ = id`. -/
def idTwist : Twist where
  τ := id
  invol _ := rfl
  card _ := rfl
  lima _ h := h
  bot := rfl
  dom _ _ _ h := dom_of_oddLR_ne_zero h
  lead μ β := oddLR_addRows μ β

/-- `τ = transpose`. -/
def trTwist : Twist where
  τ := YoungDiagram.transpose
  invol := YoungDiagram.transpose_transpose
  card := YoungDiagram.card_transpose
  lima _ h := isLima_transpose h
  bot := bot_transpose
  dom _ _ _ h := dom_of_oddLR_ne_zero (oddLR_transpose_ne_zero h)
  lead μ β := by
    have := oddLR_transpose_unit (oddLR_addRows μ.transpose β.transpose)
    rwa [YoungDiagram.transpose_transpose, YoungDiagram.transpose_transpose] at this

namespace Twist

variable (T : Twist)

/-- The leading shape of a product `[s_μ][s_β]`. -/
def leadShape (μ β : Lima) : Lima :=
  ⟨T.τ (addRows (T.τ μ.1) (T.τ β.1)),
    T.lima _ (isLima_addRows (T.lima _ μ.2) (T.lima _ β.2))⟩

theorem τ_injective : Function.Injective T.τ := fun a b h => by
  rw [← T.invol a, h, T.invol]

/-- `x` is `±[s_{λ₀}]` plus classes `[s_λ]` with `τλ ⊴ τλ₀` and `|λ| = |λ₀|`. -/
def Tri (x : HQ) (l0 : Lima) : Prop :=
  (coord x l0 = 1 ∨ coord x l0 = -1) ∧
    ∀ lam, coord x lam ≠ 0 → Dom (T.τ lam.1) (T.τ l0.1) ∧ lam.1.card = l0.1.card

theorem tri_mul (μ : Lima) {x : HQ} {l0 : Lima} (h : T.Tri x l0) :
    T.Tri (limaClass μ * x) (T.leadShape μ l0) := by
  obtain ⟨hl, hlow⟩ := h
  have hτ : T.τ (T.leadShape μ l0).1 = addRows (T.τ μ.1) (T.τ l0.1) := T.invol _
  constructor
  · rw [coord_mul, Finsupp.sum, Finset.sum_eq_single l0]
    · rcases hl with h | h <;> rcases T.lead μ.1 l0.1 with h' | h' <;>
        simp only [leadShape, h, h', one_mul, neg_mul, neg_neg, true_or, or_true]
    · intro β hβ hne
      by_contra hc
      have hc' : oddLR (T.leadShape μ l0).1 μ.1 β.1 ≠ 0 := fun h0 => hc (by rw [h0, mul_zero])
      have h1 := T.dom _ _ _ hc'
      rw [hτ] at h1
      have h2 := (hlow β (Finsupp.mem_support_iff.mp hβ)).1
      have h3 := h2.addRows_left (T.τ μ.1)
      have h4 := addRows_left_cancel (Dom.antisymm h3 h1)
      exact hne (Subtype.ext (T.τ_injective h4))
    · intro h
      rcases hl with h' | h' <;> rw [Finsupp.notMem_support_iff.mp h] at h' <;> simp at h'
  · intro lam hlam
    rw [coord_mul] at hlam
    obtain ⟨β, hβ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hlam
    simp only at hne
    have hc : coord x β ≠ 0 := Finsupp.mem_support_iff.mp hβ
    have ho : oddLR lam.1 μ.1 β.1 ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    obtain ⟨h2, hcard⟩ := hlow β hc
    refine ⟨?_, ?_⟩
    · rw [hτ]
      exact (T.dom _ _ _ ho).trans (h2.addRows_left _)
    · rw [card_of_oddLR_ne_zero ho, hcard]
      simp only [leadShape, T.card, card_addRows]

theorem sK_bot : sK ⊥ = 1 := by
  have e : TableauExtremal.rowShape 0 = ⊥ := by
    apply YoungDiagram.ext
    simp [TableauExtremal.rowShape]
  rw [← e, OddLRMisc.sK_row, OddLRMisc.hq_zero]

/-- The empty partition, as a Lima partition. -/
def limaBot : Lima := ⟨⊥, isLima_bot⟩

theorem limaClass_bot : limaClass limaBot = 1 := by
  rw [limaClass, ← map_one dataQ.cls]
  congr 1
  exact Subtype.ext sK_bot

theorem tri_one : T.Tri 1 limaBot := by
  classical
  have hc : coord 1 = Finsupp.single limaBot 1 := by
    rw [coord, ← limaClass_bot, ← HQ_basis_apply, Module.Basis.repr_self]
  refine ⟨by rw [hc, Finsupp.single_eq_same]; exact Or.inl rfl, fun lam hlam => ?_⟩
  rw [hc, Finsupp.single_apply] at hlam
  split_ifs at hlam with h
  · subst h; exact ⟨Dom.refl _, rfl⟩
  · exact absurd rfl hlam

/-! ### Generators and monomials -/

/-- The generator `(2^{2(a+1)})` (for `τ = id`) or `(2(a+1), 2(a+1))` (for `τ = transpose`). -/
def gen (a : ℕ) : Lima :=
  ⟨T.τ (colPart (Finsupp.single a 1)), T.lima _ (isLima_colPart _)⟩

/-- The class of the generator. -/
def genClass (a : ℕ) : HQ := limaClass (T.gen a)

/-- The monomial `∏ genClass(a)^{m_a}`. -/
def mono (m : ℕ →₀ ℕ) : HQ := m.prod (fun a n => T.genClass a ^ n)

/-- The leading shape of a monomial: `τ(Σ m_a (2^{2(a+1)}))`. -/
def leadOf (m : ℕ →₀ ℕ) : Lima := ⟨T.τ (colPart m), T.lima _ (isLima_colPart _)⟩

theorem mono_single_add (a : ℕ) (m : ℕ →₀ ℕ) :
    T.mono (Finsupp.single a 1 + m) = T.genClass a * T.mono m := by
  rw [mono, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun a n => T.genClass a ^ n) (pow_zero _), pow_one]
  rfl

theorem leadOf_single_add (a : ℕ) (m : ℕ →₀ ℕ) :
    T.leadOf (Finsupp.single a 1 + m) = T.leadShape (T.gen a) (T.leadOf m) := by
  apply Subtype.ext
  simp only [leadOf, leadShape, gen, T.invol, colPart_add]

theorem tri_mono (m : ℕ →₀ ℕ) : T.Tri (T.mono m) (T.leadOf m) := by
  induction m using Finsupp.induction with
  | zero =>
    have h1 : T.mono 0 = 1 := Finsupp.prod_zero_index
    have h2 : T.leadOf 0 = limaBot := Subtype.ext (by simp [leadOf, colPart_zero, T.bot, limaBot])
    rw [h1, h2]
    exact T.tri_one
  | single_add a b f _ hb ih =>
    clear hb
    induction b with
    | zero => simpa using ih
    | succ b ihb =>
      have e : Finsupp.single a (b + 1) + f = Finsupp.single a 1 + (Finsupp.single a b + f) := by
        rw [← add_assoc, ← Finsupp.single_add, add_comm 1 b]
      rw [e, T.mono_single_add, T.leadOf_single_add]
      exact T.tri_mul _ ihb

/-- The leading shapes of monomials run bijectively over the Lima partitions. -/
def leadEquiv : (ℕ →₀ ℕ) ≃ Lima :=
  colEquiv.trans
    { toFun := fun μ => ⟨T.τ μ.1, T.lima _ μ.2⟩
      invFun := fun μ => ⟨T.τ μ.1, T.lima _ μ.2⟩
      left_inv := fun _ => Subtype.ext (T.invol _)
      right_inv := fun _ => Subtype.ext (T.invol _) }

theorem leadEquiv_apply (m : ℕ →₀ ℕ) : T.leadEquiv m = T.leadOf m := rfl

theorem mono_basis :
    LinearIndependent ℤ T.mono ∧ ⊤ ≤ Submodule.span ℤ (Set.range T.mono) := by
  refine unitriangular HQ_basis T.mono T.leadEquiv (fun lam => domRank (T.τ lam.1))
    (fun m => ?_) (fun m lam hlam hne => ?_)
  · rw [leadEquiv_apply]; exact (T.tri_mono m).1
  · rw [leadEquiv_apply] at hne ⊢
    obtain ⟨hd, hc⟩ := (T.tri_mono m).2 lam hlam
    refine domRank_lt hd (by rw [T.card, T.card, hc]) (fun h => hne (Subtype.ext ?_))
    exact T.τ_injective h

/-- The monomials in the generators form a `ℤ`-basis of `H(OΛ)`. -/
def monoBasis : Module.Basis (ℕ →₀ ℕ) ℤ HQ := Module.Basis.mk T.mono_basis.1 T.mono_basis.2

/-- The evaluation `ℤ[X_0, X_1, …] → H(OΛ)`, `X_a ↦ genClass a`, is bijective. -/
theorem aeval_bijective :
    Function.Bijective (MvPolynomial.aeval T.genClass : MvPolynomial ℕ ℤ →ₐ[ℤ] HQ) := by
  have key : (MvPolynomial.aeval T.genClass : MvPolynomial ℕ ℤ →ₐ[ℤ] HQ).toLinearMap =
      ((MvPolynomial.basisMonomials ℕ ℤ).equiv T.monoBasis (Equiv.refl _)).toLinearMap := by
    refine (MvPolynomial.basisMonomials ℕ ℤ).ext fun m => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, monoBasis,
      Module.Basis.mk_apply, MvPolynomial.coe_basisMonomials]
    simp only [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, map_one, one_mul]
    rfl
  have : ⇑(MvPolynomial.aeval T.genClass : MvPolynomial ℕ ℤ →ₐ[ℤ] HQ) =
      ⇑((MvPolynomial.basisMonomials ℕ ℤ).equiv T.monoBasis (Equiv.refl _)) :=
    congrArg DFunLike.coe key
  rw [this]
  exact LinearEquiv.bijective _

end Twist

/-! ### Proposition A.3 -/

theorem mem_gen_id (a : ℕ) (c : ℕ × ℕ) :
    c ∈ (idTwist.gen a).1 ↔ c.1 < 2 * (a + 1) ∧ c.2 < 2 := by
  change c ∈ colPart (Finsupp.single a 1) ↔ _
  rw [YoungDiagram.mem_iff_lt_rowLen, rowLen_colPart_single]
  split_ifs <;> omega

theorem mem_gen_tr (a : ℕ) (c : ℕ × ℕ) :
    c ∈ (trTwist.gen a).1 ↔ c.1 < 2 ∧ c.2 < 2 * (a + 1) := by
  change c ∈ (colPart (Finsupp.single a 1)).transpose ↔ _
  rw [YoungDiagram.mem_transpose, YoungDiagram.mem_iff_lt_rowLen, rowLen_colPart_single]
  simp only [Prod.fst_swap, Prod.snd_swap]
  split_ifs <;> omega

/-- **Proposition A.3** (Ellis–Qi), generators `s_{(2,…,2)}` (`2k` twos, `k ≥ 1`): `H(OΛ)` is
the polynomial algebra `ℤ[X_0, X_1, …]` with `X_a ↦ [s_{(2^{2(a+1)})}]`. -/
theorem prop_A_3_columns :
    Function.Bijective (MvPolynomial.aeval idTwist.genClass : MvPolynomial ℕ ℤ →ₐ[ℤ] HQ) :=
  idTwist.aeval_bijective

/-- **Proposition A.3** (Ellis–Qi), generators `s_{(2k,2k)}` (`k ≥ 1`): `H(OΛ)` is the polynomial
algebra `ℤ[X_0, X_1, …]` with `X_a ↦ [s_{(2(a+1), 2(a+1))}]`. -/
theorem prop_A_3_rows :
    Function.Bijective (MvPolynomial.aeval trTwist.genClass : MvPolynomial ℕ ℤ →ₐ[ℤ] HQ) :=
  trTwist.aeval_bijective

/-- The algebra isomorphism `ℤ[X_0, X_1, …] ≅ H(OΛ)`, `X_a ↦ [s_{(2^{2(a+1)})}]`. -/
def propA3ColumnsEquiv : MvPolynomial ℕ ℤ ≃ₐ[ℤ] HQ :=
  AlgEquiv.ofBijective _ prop_A_3_columns

/-- The algebra isomorphism `ℤ[X_0, X_1, …] ≅ H(OΛ)`, `X_a ↦ [s_{(2(a+1), 2(a+1))}]`. -/
def propA3RowsEquiv : MvPolynomial ℕ ℤ ≃ₐ[ℤ] HQ :=
  AlgEquiv.ofBijective _ prop_A_3_rows

end

end OddMath.Frontier.EQLima
