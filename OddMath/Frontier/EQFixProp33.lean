import OddMath.Frontier.EQZnAction

/-!
# Proposition 3.3: local differentials on `ONH_n` induced from `OPol_n(α)`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.2, (3.6)–(3.11) and Proposition 3.3.

Rank `N = n + 2`, strands numbered from `0`, integer coefficients. `OPol_N(α)` is the rank-one
free left module with `d_α(f 1_α) = (d f + ι(f) Σ_i α_i x_i) 1_α` (`EQSkewDifferential.dAlpha`);
it is a dg module iff `α ∈ {0,1}^N` (Proposition 3.1, `EQSkewDifferential.prop_3_1_left`).
`ONH_N` acts faithfully on `OPol_N` (`x_j` by left multiplication, `∂_i` by EKL's odd divided
differences `AllRankDivided.divided i`; `NilHeckeEndomorphism.actionEquiv`), and the dg module
structure induces the differential (2.7) on `END(OPol_N(α))`: for the odd operator `∂_i`,
`d(∂_i) = d_α ∘ ∂_i + ∂_i ∘ d_α`. For the even generators `d(x_j) = x_j²` holds for every `α`
(`EQZn.dAlpha_generator_anticomm`).

*Diagrammatic locality* of the induced differential means that `d(∂_i)` is given by one local
rule in the window of strands `i, i+1`,
`d(∂_i) = a + b x_i ∂_i + c x_{i+1} ∂_i` with constants `a, b, c ∈ ℤ` (the ansatz before (3.6)).
Here the constants are even allowed to depend on `i` (`IsLocalAt`), which is weaker than the
paper's hypothesis.

* `local_constants`: if `d(∂_i) = a + b x_i ∂_i + c x_{i+1} ∂_i` as operators on `OPol_N(α)`, then
  `a = 1`, `b = c = 0` and `α_i + α_{i+1} = 1` (the computation (3.8)–(3.11) on `1`, `x_i`,
  `x_{i+1}`; the general formula is `EQZn.dAlpha_divided_general`,
  `d(∂_i) = id + (α_i + α_{i+1} - 1) s_i ι`).
* **Proposition 3.3** (`prop_3_3`): if `OPol_N(α)` is a dg module and the induced differential on
  `ONH_N` is diagrammatically local, then `d(∂_i) = 1` for all `i` and
  `α = (0,1,0,1,…)` or `α = (1,0,1,0,…)` (0-indexed: `α = zAlpha N` or `α = 1 - zAlpha N`).
* `prop_3_3_converse`: for both alternating `α`, `OPol_N(α)` is a dg module and `d(∂_i) = 1`
  (so the induced differential is local, with `a = 1`, `b = c = 0`); `prop_3_3_iff` combines both.
-/

namespace OddMath.Frontier.EQFix

open OddMath.SkewPolynomial (SkewPolynomial generator expSingle)
open EQSkewDifferential (dAlpha parityInv parityInv_generator zAlpha prop_3_1_left)
open AllRankDivided (divided s)
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) eqFixP33NUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqFixP33NUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-- The coefficient of `x_k` in `x_j`. -/
theorem generator_apply_expSingle {N : ℕ} (j k : Fin N) :
    (generator j : SkewPolynomial N) (expSingle k) = if j = k then 1 else 0 := by
  have hinj : expSingle j = expSingle k ↔ j = k := by
    constructor
    · intro h
      have := congrFun h j
      by_contra hne
      simp [expSingle, Ne.symm hne] at this
    · rintro rfl; rfl
  simp only [OddMath.SkewPolynomial.generator, OddMath.SkewPolynomial.monomial,
    Finsupp.single_apply, hinj]

/-- The coefficient of `x_k` in `1`. -/
theorem one_apply_expSingle {N : ℕ} (k : Fin N) : (1 : SkewPolynomial N) (expSingle k) = 0 := by
  change (Finsupp.single (0 : Fin N → ℕ) (1 : ℤ)) (expSingle k) = 0
  rw [Finsupp.single_apply, ite_eq_right]
  intro h
  have := congrFun h k
  simp [expSingle] at this

/-- The constant term of `1`. -/
theorem one_apply_zero' {N : ℕ} : (1 : SkewPolynomial N) 0 = 1 := by
  change (Finsupp.single (0 : Fin N → ℕ) (1 : ℤ)) 0 = 1
  rw [Finsupp.single_eq_same]

/-- The induced differential of `∂_i` on `END(OPol_N(α))`, (2.7): since `∂_i` is odd,
`d(∂_i) = d_α ∘ ∂_i + ∂_i ∘ d_α`. -/
def dDivided (α : Fin (n+2) → ℤ) (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    SkewPolynomial (n+2) :=
  dAlpha α (divided i f) + divided i (dAlpha α f)

/-- The local ansatz `a + b x_i ∂_i + c x_{i+1} ∂_i` in the window of strands `i, i+1`, as an
operator on `OPol_N`. -/
def ansatz (i : Fin (n+1)) (a b c : ℤ) (f : SkewPolynomial (n+2)) : SkewPolynomial (n+2) :=
  a • f + b • (generator i.castSucc * divided i f) + c • (generator i.succ * divided i f)

/-- The induced differential of `∂_i` is given by the local ansatz with constants `a, b, c`. -/
def IsLocalAt (α : Fin (n+2) → ℤ) (i : Fin (n+1)) (a b c : ℤ) : Prop :=
  ∀ f, dDivided α i f = ansatz i a b c f

/-- **Ellis–Qi (3.8)–(3.11)**: if `d(∂_i) = a + b x_i ∂_i + c x_{i+1} ∂_i` on `OPol_N(α)`, then
`a = 1`, `b = c = 0` and `α_i + α_{i+1} = 1`. -/
theorem local_constants (α : Fin (n+2) → ℤ) (i : Fin (n+1)) (a b c : ℤ)
    (h : IsLocalAt α i a b c) :
    a = 1 ∧ b = 0 ∧ c = 0 ∧ α i.castSucc + α i.succ = 1 := by
  set γ := α i.castSucc + α i.succ - 1 with hγ
  have H : ∀ f, f + γ • s i (parityInv (n+2) f) = ansatz i a b c f := fun f => by
    rw [← h f, dDivided, EQZn.dAlpha_divided_general]
  have hne := AllRankDivided.adjacent_ne i
  have hne' := hne.symm
  have hl : divided i (generator i.castSucc) = 1 := by
    rw [AllRankDivided.divided_generator, ite_eq_left (Or.inl rfl)]
  have hr : divided i (generator i.succ) = 1 := by
    rw [AllRankDivided.divided_generator, ite_eq_left (Or.inr rfl)]
  -- evaluate at `1`
  have h1 := congrArg (fun p : SkewPolynomial (n+2) => p 0) (H 1)
  simp only [ansatz, map_one, AllRankDivided.divided_one, mul_zero, smul_zero, add_zero,
    Finsupp.add_apply, Finsupp.smul_apply, one_apply_zero', smul_eq_mul, mul_one] at h1
  -- evaluate at `x_i`
  have hxl := H (generator i.castSucc)
  rw [parityInv_generator, map_neg, AllRankDivided.s_generator, Equiv.swap_apply_left, neg_neg,
    ansatz, hl, mul_one, mul_one] at hxl
  have hxl1 := congrArg (fun p : SkewPolynomial (n+2) => p (expSingle i.castSucc)) hxl
  have hxl2 := congrArg (fun p : SkewPolynomial (n+2) => p (expSingle i.succ)) hxl
  simp only [Finsupp.add_apply, Finsupp.smul_apply, generator_apply_expSingle, ite_true,
    ite_eq_right hne, ite_eq_right hne', smul_eq_mul, mul_one, mul_zero, add_zero,
    zero_add] at hxl1 hxl2
  -- evaluate at `x_{i+1}`
  have hxr := H (generator i.succ)
  rw [parityInv_generator, map_neg, AllRankDivided.s_generator, Equiv.swap_apply_right, neg_neg,
    ansatz, hr, mul_one, mul_one] at hxr
  have hxr1 := congrArg (fun p : SkewPolynomial (n+2) => p (expSingle i.castSucc)) hxr
  simp only [Finsupp.add_apply, Finsupp.smul_apply, generator_apply_expSingle, ite_true,
    ite_eq_right hne', smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at hxr1
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- A sequence with `α_{m+1} = 1 - α_m` alternates: `α_m = α_0` for `m` even and `1 - α_0` for
`m` odd. -/
theorem alternating_of_adjacent (α : Fin (n+2) → ℤ)
    (hα : ∀ i : Fin (n+1), α i.castSucc + α i.succ = 1) :
    ∀ m (hm : m < n + 2), α ⟨m, hm⟩ = if m % 2 = 0 then α 0 else 1 - α 0 := by
  intro m
  induction m with
  | zero => intro hm; rfl
  | succ m ih =>
    intro hm
    have h := hα ⟨m, by omega⟩
    have e1 : (⟨m, by omega⟩ : Fin (n+1)).castSucc = ⟨m, by omega⟩ := rfl
    have e2 : (⟨m, by omega⟩ : Fin (n+1)).succ = ⟨m + 1, hm⟩ := rfl
    rw [e1, e2, ih (by omega)] at h
    rcases Nat.mod_two_eq_zero_or_one m with hm2 | hm2
    · rw [ite_eq_left hm2] at h
      rw [ite_eq_right (by omega)]; omega
    · rw [ite_eq_right (by omega)] at h
      rw [ite_eq_left (by omega)]; omega

/-- **Ellis–Qi, Proposition 3.3**: suppose `OPol_N(α)` is a left dg module over `OPol_N`
(`d_α² = 0`, i.e. `α ∈ {0,1}^N` by Proposition 3.1) and the differential it induces on
`ONH_N ⊆ END(OPol_N(α))` is diagrammatically local:
`d(∂_i) = a_i + b_i x_i ∂_i + c_i x_{i+1} ∂_i` for all `i`. Then `d(∂_i) = 1` for all `i`
(with `a_i = 1`, `b_i = c_i = 0`), and `α = (0,1,0,1,…)` or `α = (1,0,1,0,…)`
(`α = zAlpha N` or `α = 1 - zAlpha N`, strands numbered from `0`). -/
theorem prop_3_3 (α : Fin (n+2) → ℤ) (hdg : ∀ f, dAlpha α (dAlpha α f) = 0)
    (a b c : Fin (n+1) → ℤ) (hloc : ∀ i, IsLocalAt α i (a i) (b i) (c i)) :
    (∀ i f, dDivided α i f = f) ∧ (∀ i, a i = 1 ∧ b i = 0 ∧ c i = 0) ∧
      (α = zAlpha (n+2) ∨ α = fun j => 1 - zAlpha (n+2) j) := by
  have hc := fun i => local_constants α i (a i) (b i) (c i) (hloc i)
  have hadj : ∀ i : Fin (n+1), α i.castSucc + α i.succ = 1 := fun i => (hc i).2.2.2
  refine ⟨fun i f => ?_, fun i => ⟨(hc i).1, (hc i).2.1, (hc i).2.2.1⟩, ?_⟩
  · rw [hloc i f, ansatz, (hc i).1, (hc i).2.1, (hc i).2.2.1]
    simp
  · have halt := alternating_of_adjacent α hadj
    rcases (prop_3_1_left α).mp hdg 0 with h0 | h0
    · left
      funext j
      rw [show j = ⟨j.val, j.isLt⟩ from rfl, halt, h0, zAlpha]
      rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp [h]
    · right
      funext j
      rw [show j = ⟨j.val, j.isLt⟩ from rfl, halt, h0, zAlpha]
      rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp [h]

/-- Converse of **Ellis–Qi, Proposition 3.3**: for `α = (0,1,0,1,…)` and `α = (1,0,1,0,…)`,
`OPol_N(α)` is a dg module and the induced differential satisfies `d(∂_i) = 1` for all `i`; in
particular it is diagrammatically local (`a = 1`, `b = c = 0`). -/
theorem prop_3_3_converse (α : Fin (n+2) → ℤ)
    (hα : α = zAlpha (n+2) ∨ α = fun j => 1 - zAlpha (n+2) j) :
    (∀ f, dAlpha α (dAlpha α f) = 0) ∧ (∀ i f, dDivided α i f = f) ∧ ∀ i, IsLocalAt α i 1 0 0 := by
  have hadj : ∀ i : Fin (n+1), α i.castSucc + α i.succ = 1 := by
    intro i
    rcases hα with rfl | rfl
    · exact EQZn.zAlpha_adjacent i
    · have := EQZn.zAlpha_adjacent (n := n) i
      simp only
      omega
  have hdd : ∀ i f, dDivided α i f = f := fun i f => by
    rw [dDivided, EQZn.dAlpha_divided_general, hadj, sub_self, zero_smul, add_zero]
  refine ⟨(prop_3_1_left α).mpr fun j => ?_, hdd, fun i f => by rw [hdd, ansatz]; simp⟩
  rcases hα with rfl | rfl <;> simp only [zAlpha] <;>
    rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp [h]

/-- **Ellis–Qi, Proposition 3.3** and its converse: for `α` with `OPol_N(α)` a dg module, the
induced differential on `ONH_N` is diagrammatically local iff `α` is `(0,1,0,1,…)` or
`(1,0,1,0,…)`; in that case `d(∂_i) = 1`. -/
theorem prop_3_3_iff (α : Fin (n+2) → ℤ) (hdg : ∀ f, dAlpha α (dAlpha α f) = 0) :
    (∃ a b c : Fin (n+1) → ℤ, ∀ i, IsLocalAt α i (a i) (b i) (c i)) ↔
      (α = zAlpha (n+2) ∨ α = fun j => 1 - zAlpha (n+2) j) :=
  ⟨fun ⟨a, b, c, h⟩ => (prop_3_3 α hdg a b c h).2.2,
    fun hα => ⟨fun _ => 1, fun _ => 0, fun _ => 0, (prop_3_3_converse α hα).2.2⟩⟩

end

end OddMath.Frontier.EQFix
