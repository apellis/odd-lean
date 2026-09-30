import OddMath.Frontier.EQAppHypercube
import OddMath.Frontier.EQLimaCohomology
import OddMath.Frontier.EQZnFiniteCell

/-!
# Ellis–Qi, Appendix A.2: the filtration on `Z_n`

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.2 (printed numbering).  By (3.38) (`EQZn.eq_3_38`), `Z_n ≅ U_n ⊗ OΛ_n` as right dg
`OΛ_n`-modules, where `U_n` has the `ℤ`-basis `B'_n = {x^a 1_z : 0 ≤ a_i ≤ i - 1}` (one-based;
this is the corrected range, `EQZn.RevStair`, see `EQZn.staircase_span_stable_iff`) and
`d(x^a 1_z) = Σ_i {a_i + i - 1} x_i x^a 1_z` (`EQZn.dAlpha_zAlpha_monomial`).  So the finite-cell
filtration of `Z_n` is governed by the complex `U_n`, which this file analyses.

Indices are `0`-based here: the exponent `A_i` of `x_i` satisfies `A_i ≤ i`, and the coefficient
of `x_i x^A` in `d(x^A)` is `{A_i + i}` (`= 1` if `A_i + i` is odd, `0` otherwise), times the sign
`ε(i, A) = ±1` of `x_i x^A = ε x^{A + e_i}`.

* **Urns and balls** (`uSystem`).  The factor `x_i^{A_i}` of `x^A` is an *empty urn* if `A_i + i`
  is odd (one-based: `i ≡ a_i` mod 2), and an *urn with a ball* if `A_i + i` is even and
  `A_i ≥ 1`; adding the ball raises `A_i` by one.  This is a `BoxSystem` on the reversed staircase,
  with the box `(i, A_i)` for the ball of urn `i`.  **Correction to the printed description:** a
  factor with `A_i = 0` and `i` even (one-based `a_i = 0`, `i` odd), e.g. `x_1^0`, `x_3^0`, is not an
  urn, although the printed rule ("full iff `i ≡ a_i + 1`") would call it full: it has no ball to
  remove (`notMem_uRemovable_of_zero`).
* `actsByBoxes_dU`: the differential of `U_n` adds balls, with coefficients `ε(i, A) = ±1`.
* **Hypercube decomposition** (`uDecompEquiv`, `uDecompEquiv_dU`): `U_n` is isomorphic, as a
  complex, to the direct sum over the initial vectors `q` of the hypercube complexes `Y_{A q}`, whose
  urns are the empty urns of `q` (`EQApp.decompEquiv_delta`).
* **Initial vectors** (`init_iff`): `x^q 1_z` is an initial vector (no balls) iff for every `i`,
  `q_i ∈ initExps i = {0} ∪ {a ≤ i : a + i odd}`; one-based, `a_i ∈ {0} ∪ {a ≤ i - 1 : a ≡ i mod 2}`.
  So the initial vectors of `U_{n+1}` are the products of those of `U_n` with `x_{n+1}^c`,
  `c ∈ initExps n` (`init_succ_iff`); for `n = 5, 6` this is the printed description
  (`initExps_small`: `{x_3^a x_4^b x_5^c : a ∈ {0,1}, b ∈ {0,2}, c ∈ {0,1,3}}`, then
  `{x_6^0, x_6^2, x_6^4}`).  The hypercube of `q` has dimension
  `#{i : q_i + i odd} = #{i odd (0-based)} + #{i even : q_i ≠ 0}` (`card_uAddable_init`), which is
  `≥ 1` for `n ≥ 2` (`uAddable_init_nonempty`: the urn `x_2` is always empty).
* **Cohomology** (`uCrit_iff`, `homology_U_subsingleton`, `homologyU_small`): the critical
  vectors are the `x^A` with `A_i = 0` and `i` even for all `i`, so `H(U_n) = 0` for `n ≥ 2` (every
  hypercube has an urn; compare `EQZn.U_acyclic`), and `H(U_n) ≅ ℤ`, spanned by `[1_z]`, for
  `n ≤ 1`.
* **The filtration of `Z_n`** (`zDecompEquiv`, `zDecompEquiv_d`): combining with (3.38),
  `Z_n ≅ (⨁_q Y_{A q}) ⊗ OΛ_n` with differential `δ ⊗ 1 + ι ⊗ d`: the finite-cell filtration of
  `Z_n` is a direct sum, over the initial vectors `q`, of hypercube complexes tensored with the
  regular dg module `OΛ_n`.
-/

namespace OddMath.Frontier.EQApp

open Finset OddMath.Frontier.EQLima OddMath.Frontier.EQZn
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open OddMath.Frontier.EQSkewDifferential

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) eqAppZnNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqAppZnNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {N : ℕ}

/-! ### Urns and balls -/

/-- The cells of `x^A`: the pairs `(i, j)` with `j < A_i`. -/
def uCells (A : RevStair N) : Finset (Fin N × ℕ) :=
  (univ ×ˢ range N).filter fun c => c.2 < A.1 c.1

/-- The empty urns of `x^A`: the boxes `(i, A_i)` with `A_i + i` odd. -/
def uAddable (A : RevStair N) : Finset (Fin N × ℕ) :=
  (univ ×ˢ range N).filter fun c => (A.1 c.1 + c.1.val) % 2 = 1 ∧ c.2 = A.1 c.1

/-- The urns of `x^A` holding a ball: the boxes `(i, A_i - 1)` with `A_i ≥ 1`, `A_i + i` even. -/
def uRemovable (A : RevStair N) : Finset (Fin N × ℕ) :=
  (univ ×ˢ range N).filter fun c => 0 < A.1 c.1 ∧ (A.1 c.1 + c.1.val) % 2 = 0 ∧ c.2 + 1 = A.1 c.1

theorem mem_uCells {A : RevStair N} {c : Fin N × ℕ} : c ∈ uCells A ↔ c.2 < A.1 c.1 := by
  simp only [uCells, mem_filter, mem_product, mem_univ, mem_range, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by have := A.2 c.1; have := c.1.2; omega, h⟩

theorem mem_uAddable {A : RevStair N} {c : Fin N × ℕ} :
    c ∈ uAddable A ↔ (A.1 c.1 + c.1.val) % 2 = 1 ∧ c.2 = A.1 c.1 := by
  simp only [uAddable, mem_filter, mem_product, mem_univ, mem_range, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by have := A.2 c.1; have := c.1.2; omega, h⟩

theorem mem_uRemovable {A : RevStair N} {c : Fin N × ℕ} :
    c ∈ uRemovable A ↔ 0 < A.1 c.1 ∧ (A.1 c.1 + c.1.val) % 2 = 0 ∧ c.2 + 1 = A.1 c.1 := by
  simp only [uRemovable, mem_filter, mem_product, mem_univ, mem_range, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by have := A.2 c.1; have := c.1.2; omega, h⟩

/-- A factor `x_i^0` with `i` even (`0`-based) is not an urn: it is neither empty nor full. -/
theorem notMem_uRemovable_of_zero {A : RevStair N} {i : Fin N} (h : A.1 i = 0) (j : ℕ) :
    (i, j) ∉ uRemovable A ∧ ((i, j) ∈ uAddable A ↔ i.val % 2 = 1 ∧ j = 0) := by
  rw [mem_uRemovable, mem_uAddable]
  simp only [h]
  omega

theorem lt_of_odd {A : RevStair N} {i : Fin N} (h : (A.1 i + i.val) % 2 = 1) : A.1 i < i.val := by
  have := A.2 i
  rcases Nat.lt_or_ge (A.1 i) i.val with h' | h'
  · exact h'
  · have : A.1 i = i.val := le_antisymm (A.2 i) h'
    omega

/-- Add the ball of urn `c.1` (if it is empty). -/
def uAdd (A : RevStair N) (c : Fin N × ℕ) : RevStair N :=
  if h : (A.1 c.1 + c.1.val) % 2 = 1 then
    ⟨Function.update A.1 c.1 (A.1 c.1 + 1), fun i => by
      rcases eq_or_ne i c.1 with hi | hi
      · subst hi; rw [Function.update_self]; have := lt_of_odd h; omega
      · rw [Function.update_of_ne hi]; exact A.2 i⟩
  else A

/-- Take the ball out of urn `c.1`. -/
def uRem (A : RevStair N) (c : Fin N × ℕ) : RevStair N :=
  ⟨Function.update A.1 c.1 (A.1 c.1 - 1), fun i => by
    rcases eq_or_ne i c.1 with hi | hi
    · subst hi; rw [Function.update_self]; have := A.2 c.1; omega
    · rw [Function.update_of_ne hi]; exact A.2 i⟩

theorem uAdd_val {A : RevStair N} {c : Fin N × ℕ} (h : (A.1 c.1 + c.1.val) % 2 = 1) :
    (uAdd A c).1 = Function.update A.1 c.1 (A.1 c.1 + 1) := by
  simp [uAdd, h]

theorem uRem_val (A : RevStair N) (c : Fin N × ℕ) :
    (uRem A c).1 = Function.update A.1 c.1 (A.1 c.1 - 1) := rfl

theorem uCells_injective : Function.Injective (uCells (N := N)) := by
  intro A A' h
  apply Subtype.ext
  funext i
  have h1 : ∀ j, j < A.1 i ↔ j < A'.1 i := fun j => by
    have := congrArg (fun s => (i, j) ∈ s) h
    simpa only [mem_uCells, eq_iff_iff] using this
  have := h1 (A.1 i)
  have := h1 (A'.1 i)
  omega

/-- The urns and balls of `U_n` as a box system (Ellis–Qi, Appendix A.2). -/
def uSystem (N : ℕ) : BoxSystem (RevStair N) (Fin N × ℕ) where
  cells := uCells
  cells_injective := uCells_injective
  A := uAddable
  R := uRemovable
  add := uAdd
  rem := uRem
  notMem_cells_of_mem_A := by
    intro A c h
    rw [mem_uAddable] at h
    rw [mem_uCells]
    omega
  cells_add := by
    intro A c h
    have h' := mem_uAddable.mp h
    ext ⟨i, j⟩
    rw [mem_uCells, uAdd_val h'.1, mem_insert, mem_uCells, Function.update_apply]
    obtain ⟨ci, cj⟩ := c
    simp only [Prod.mk.injEq] at h' ⊢
    split_ifs with hi
    · subst hi; omega
    · simp only [hi, false_and, false_or]
  mem_cells_of_mem_R := by
    intro A c h
    rw [mem_uRemovable] at h
    rw [mem_uCells]
    omega
  cells_rem := by
    intro A c h
    have h' := mem_uRemovable.mp h
    ext ⟨i, j⟩
    rw [mem_uCells, uRem_val, mem_erase, mem_uCells, Function.update_apply]
    obtain ⟨ci, cj⟩ := c
    simp only [ne_eq, Prod.mk.injEq] at h' ⊢
    split_ifs with hi
    · subst hi; omega
    · simp only [hi, false_and, not_false_eq_true, true_and]
  A_add := by
    intro A c h
    have h' := mem_uAddable.mp h
    ext ⟨i, j⟩
    rw [mem_uAddable, uAdd_val h'.1, mem_erase, mem_uAddable, Function.update_apply]
    obtain ⟨ci, cj⟩ := c
    simp only [ne_eq, Prod.mk.injEq] at h' ⊢
    split_ifs with hi
    · subst hi; omega
    · simp only [hi, false_and, not_false_eq_true, true_and]
  R_add := by
    intro A c h
    have h' := mem_uAddable.mp h
    ext ⟨i, j⟩
    rw [mem_uRemovable, uAdd_val h'.1, mem_insert, mem_uRemovable, Function.update_apply]
    obtain ⟨ci, cj⟩ := c
    simp only [Prod.mk.injEq] at h' ⊢
    split_ifs with hi
    · subst hi; omega
    · simp only [hi, false_and, false_or]
  mem_A_rem := by
    intro A c h
    have h' := mem_uRemovable.mp h
    rw [mem_uAddable, uRem_val, Function.update_self]
    omega

/-! ### The differential adds balls -/

/-- The sign `ε(i, A)` of `x_i x^A = ε x^{A + e_i}`, as a unit. -/
def uCoeff (A : RevStair N) (c : Fin N × ℕ) : ℤˣ :=
  (-1) ^ OddMath.crossingCount (expSingle c.1) A.1

theorem uCoeff_val (A : RevStair N) (c : Fin N × ℕ) :
    ((uCoeff A c : ℤˣ) : ℤ) = OddMath.skewSign (expSingle c.1) A.1 := by
  simp [uCoeff, OddMath.skewSign]

theorem expSingle_add_eq_update (i : Fin N) (A : Fin N → ℕ) :
    expSingle i + A = Function.update A i (A i + 1) := by
  funext j
  simp only [Pi.add_apply, expSingle, Function.update_apply]
  by_cases h : j = i
  · subst h; simp; omega
  · simp [h, Ne.symm h]

theorem uAddable_eq (A : RevStair N) :
    uAddable A = (univ.filter fun i : Fin N => (A.1 i + i.val) % 2 = 1).map
      ⟨fun i => (i, A.1 i), fun _ _ h => congrArg Prod.fst h⟩ := by
  ext ⟨i, j⟩
  rw [mem_uAddable, mem_map]
  simp only [mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨i, h1, rfl, rfl⟩
  · rintro ⟨i', h1, rfl, rfl⟩; exact ⟨h1, rfl⟩

/-- **The differential of `U_n` adds balls** (Ellis–Qi, Appendix A.2, from (3.37)):
`d(x^A 1_z) = Σ_{empty urns (i, A_i)} ε(i, A) x^{A + e_i} 1_z`. -/
theorem actsByBoxes_dU : ActsByBoxes (uSystem N) (uBasis N) uCoeff (dU N) := by
  intro A
  apply Subtype.ext
  change dAlpha (zAlpha N) (uBasis N A : SkewPolynomial N) = _
  rw [uBasis_apply, dAlpha_zAlpha_monomial]
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  change _ = ∑ c ∈ uAddable A, ((uCoeff A c : ℤˣ) : ℤ) • (uBasis N (uAdd A c) : SkewPolynomial N)
  rw [uAddable_eq, Finset.sum_map, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  by_cases h : (A.1 i + i.val) % 2 = 1
  · simp only [h, ↓reduceIte]
    rw [uBasis_apply, uAdd_val (c := (i, A.1 i)) h, generator_mul_monomial,
      uCoeff_val, expSingle_add_eq_update]
    simp
  · simp only [h, ↓reduceIte]
    rw [show (A.1 i + i.val) % 2 = 0 by omega]
    simp

/-- `d² = 0` on `Z_n`: `d_α² = (·) Σ (α_i - α_i²) x_i²` and `α_i ∈ {0, 1}`. -/
theorem dAlpha_zAlpha_sq (f : SkewPolynomial N) : dAlpha (zAlpha N) (dAlpha (zAlpha N) f) = 0 := by
  rw [dAlpha_dAlpha, Finset.sum_eq_zero, mul_zero]
  intro i _
  have : zAlpha N i - zAlpha N i * zAlpha N i = 0 := by
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h <;> simp [zAlpha, h]
  rw [this, zero_smul]

theorem squareCond_uCoeff : (uSystem N).SquareCond uCoeff :=
  squareCond_of_actsByBoxes actsByBoxes_dU fun x =>
    Subtype.ext (dAlpha_zAlpha_sq (x : SkewPolynomial N))

/-! ### The hypercube decomposition of `U_n` -/

/-- The isomorphism `U_n ≅ ⨁_{q initial} Y_{A q}` (as `ℤ`-modules). -/
def uDecompEquiv (N : ℕ) :
    EKLSectionTwo.Hrev N ≃ₗ[ℤ]
      Π₀ q : Init (uSystem N), (Finset (Urn (uSystem N) q) →₀ ℤ) :=
  (uBasis N).repr.trans (decompEquiv (uSystem N))

/-- **Ellis–Qi, Appendix A.2**: `U_n` is a direct sum of subcomplexes, each isomorphic to a
hypercube complex (with signs `±1`): the isomorphism `uDecompEquiv` intertwines the differential
of `U_n` with the direct sum of the hypercube differentials `hyperDelta`, one for each initial
vector `q`, whose urns are the empty urns of `q`. -/
theorem uDecompEquiv_dU (x : EKLSectionTwo.Hrev N) :
    uDecompEquiv N (dU N x) =
      DFinsupp.mapRange.linearMap (fun q => hyperDelta (uSystem N) uCoeff q) (uDecompEquiv N x) := by
  have h := actsByBoxes_intertwine actsByBoxes_dU ((uBasis N).repr x)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [uDecompEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, h,
    LinearEquiv.apply_symm_apply, decompEquiv_delta]

/-- Each summand is a hypercube complex: `d² = 0` on it. -/
theorem hyperDelta_U_sq (q : Init (uSystem N)) :
    hyperDelta (uSystem N) uCoeff q ∘ₗ hyperDelta (uSystem N) uCoeff q = 0 :=
  hyper_delta_sq _ _ squareCond_uCoeff q

/-! ### Initial vectors -/

/-- The allowed exponents of `x_i` (`0`-based) in an initial vector: `0`, or `a ≤ i` with `a + i`
odd.  One-based: `a_i ∈ {0} ∪ {a ≤ i - 1 : a ≡ i mod 2}`. -/
def initExps (i : ℕ) : Finset ℕ := (range (i + 1)).filter fun a => a = 0 ∨ (a + i) % 2 = 1

theorem mem_initExps {i a : ℕ} : a ∈ initExps i ↔ a ≤ i ∧ (a = 0 ∨ (a + i) % 2 = 1) := by
  simp only [initExps, mem_filter, mem_range]
  omega

/-- The exponent sets for `n ≤ 6` (one-based `x_1, …, x_6`): `{0}`, `{0}`, `{0,1}`, `{0,2}`,
`{0,1,3}`, `{0,2,4}`, as printed in Ellis–Qi, Appendix A.2, for `n = 5` and `n = 6`. -/
theorem initExps_small :
    initExps 0 = {0} ∧ initExps 1 = {0} ∧ initExps 2 = {0, 1} ∧ initExps 3 = {0, 2} ∧
      initExps 4 = {0, 1, 3} ∧ initExps 5 = {0, 2, 4} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Initial vectors of `U_n`** (Ellis–Qi, Appendix A.2): `x^q 1_z` has no balls iff
`q_i ∈ initExps i` for every `i`. -/
theorem init_iff (q : RevStair N) : uRemovable q = ∅ ↔ ∀ i, q.1 i ∈ initExps i.val := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h i
    rw [mem_initExps]
    refine ⟨q.2 i, ?_⟩
    by_contra hc
    exact h (i, q.1 i - 1) (mem_uRemovable.mpr (by simp only; omega))
  · rintro h ⟨i, j⟩ hc
    have := mem_initExps.mp (h i)
    rw [mem_uRemovable] at hc
    simp only at hc
    omega

/-- The recursive description (Ellis–Qi, Appendix A.2: "for `n = 6`, take all products consisting of
one element from the previous and one element from `{x_6^0, x_6^2, x_6^4}`; and so forth"): an
exponent vector of rank `n + 1` is initial iff its first `n` exponents form an initial vector of
rank `n` and the last exponent lies in `initExps n`. -/
theorem init_succ_iff (q : Fin (N + 1) → ℕ) :
    (∀ i : Fin (N + 1), q i ∈ initExps i.val) ↔
      (∀ i : Fin N, q i.castSucc ∈ initExps i.val) ∧ q (Fin.last N) ∈ initExps N := by
  rw [Fin.forall_fin_succ']
  rfl

/-- The initial vectors of `U_5` are `{x_3^a x_4^b x_5^c : a ∈ {0,1}, b ∈ {0,2}, c ∈ {0,1,3}}`
(Ellis–Qi, Appendix A.2, one-based variables). -/
theorem init_five (q : RevStair 5) :
    uRemovable q = ∅ ↔ q.1 0 = 0 ∧ q.1 1 = 0 ∧ q.1 2 ∈ ({0, 1} : Finset ℕ) ∧
      q.1 3 ∈ ({0, 2} : Finset ℕ) ∧ q.1 4 ∈ ({0, 1, 3} : Finset ℕ) := by
  rw [init_iff]
  simp only [mem_insert, mem_singleton]
  constructor
  · intro h
    have h0 : q.1 0 ∈ initExps 0 := h 0
    have h1 : q.1 1 ∈ initExps 1 := h 1
    have h2 : q.1 2 ∈ initExps 2 := h 2
    have h3 : q.1 3 ∈ initExps 3 := h 3
    have h4 : q.1 4 ∈ initExps 4 := h 4
    rw [mem_initExps] at h0 h1 h2 h3 h4
    omega
  · rintro ⟨h0, h1, h2, h3, h4⟩ ⟨i, hi⟩
    rw [mem_initExps]
    refine ⟨q.2 _, ?_⟩
    rcases i with _ | _ | _ | _ | _ | i
    · exact Or.inl h0
    · exact Or.inl h1
    · have h' : q.1 ⟨2, hi⟩ = 0 ∨ q.1 ⟨2, hi⟩ = 1 := h2
      show q.1 ⟨2, hi⟩ = 0 ∨ (q.1 ⟨2, hi⟩ + 2) % 2 = 1
      omega
    · have h' : q.1 ⟨3, hi⟩ = 0 ∨ q.1 ⟨3, hi⟩ = 2 := h3
      show q.1 ⟨3, hi⟩ = 0 ∨ (q.1 ⟨3, hi⟩ + 3) % 2 = 1
      omega
    · have h' : q.1 ⟨4, hi⟩ = 0 ∨ q.1 ⟨4, hi⟩ = 1 ∨ q.1 ⟨4, hi⟩ = 3 := h4
      show q.1 ⟨4, hi⟩ = 0 ∨ (q.1 ⟨4, hi⟩ + 4) % 2 = 1
      omega
    · omega


/-- The dimension of the hypercube of an initial vector `q`: its empty urns are the `x_i` with
`i` odd (`0`-based; one-based even) and the `x_i` with `q_i ≠ 0`. -/
theorem card_uAddable_init {q : RevStair N} (hq : uRemovable q = ∅) :
    (uAddable q).card = (univ.filter fun i : Fin N => i.val % 2 = 1 ∨ q.1 i ≠ 0).card := by
  rw [uAddable_eq, Finset.card_map]
  congr 1
  ext i
  have := mem_initExps.mp ((init_iff q).mp hq i)
  simp only [mem_filter, mem_univ, true_and]
  omega

/-- For `n ≥ 2` every hypercube summand of `U_n` has at least one urn: `x_2` (one-based) is an
empty urn of every initial vector. -/
theorem uAddable_init_nonempty (hN : 2 ≤ N) {q : RevStair N} (hq : uRemovable q = ∅) :
    (uAddable q).Nonempty := by
  have h1 := mem_initExps.mp ((init_iff q).mp hq ⟨1, hN⟩)
  refine ⟨(⟨1, hN⟩, q.1 ⟨1, hN⟩), mem_uAddable.mpr ⟨?_, rfl⟩⟩
  simp only at h1 ⊢
  omega

/-! ### The cohomology of `U_n` -/

/-- The critical vectors of `U_n` (no urns at all): `A_i = 0` and `i` even (`0`-based) for all
`i`. -/
theorem uCrit_iff (A : RevStair N) :
    (uSystem N).Crit A ↔ ∀ i, A.1 i = 0 ∧ i.val % 2 = 0 := by
  rw [BoxSystem.crit_iff]
  change uAddable A = ∅ ∧ uRemovable A = ∅ ↔ _
  simp only [Finset.eq_empty_iff_forall_notMem]
  constructor
  · rintro ⟨hA, hR⟩ i
    have h1 : ¬((A.1 i + i.val) % 2 = 1 ∧ A.1 i = A.1 i) := fun h => hA (i, A.1 i)
      (mem_uAddable.mpr h)
    have h2 : ¬(0 < A.1 i ∧ (A.1 i + i.val) % 2 = 0 ∧ A.1 i - 1 + 1 = A.1 i) := fun h =>
      hR (i, A.1 i - 1) (mem_uRemovable.mpr h)
    omega
  · intro h
    refine ⟨fun ⟨i, j⟩ hc => ?_, fun ⟨i, j⟩ hc => ?_⟩
    · rw [mem_uAddable] at hc; have := h i; simp only at hc; omega
    · rw [mem_uRemovable] at hc; have := h i; simp only at hc; omega

/-- For `n ≥ 2`, `U_n` has no critical vectors. -/
theorem uCritSet_eq_empty (hN : 2 ≤ N) : (uSystem N).critSet = ∅ :=
  critSet_eq_empty _ fun _ hq => uAddable_init_nonempty hN hq

/-- **Cohomology of `U_n`** (Ellis–Qi, Appendix A.2): `H(U_n)` is free with basis the classes of
the critical vectors. -/
def homologyBasisU (N : ℕ) : Module.Basis (uSystem N).critSet ℤ (Homology (dU N)) :=
  schurHomologyBasis actsByBoxes_dU squareCond_uCoeff

theorem homologyBasisU_apply (p : (uSystem N).critSet) :
    homologyBasisU N p = Submodule.Quotient.mk ⟨uBasis N p.1, LinearMap.mem_ker.mpr
      (schur_crit_cocycle actsByBoxes_dU p.2)⟩ :=
  schurHomologyBasis_apply actsByBoxes_dU squareCond_uCoeff p

/-- **`H(U_n) = 0` for `n ≥ 2`** (Ellis–Qi, Appendix A.2: each hypercube summand has at least one
urn, so is contractible). -/
theorem homology_U_subsingleton (hN : 2 ≤ N) : Subsingleton (Homology (dU N)) := by
  have : IsEmpty (uSystem N).critSet := by
    rw [uCritSet_eq_empty hN]; exact Set.isEmpty_coe_sort.mpr rfl
  exact (homologyBasisU N).repr.toEquiv.subsingleton

/-- The unique critical vector `1_z` of `U_n` for `n ≤ 1`. -/
def zeroCrit (hN : N ≤ 1) : (uSystem N).critSet :=
  ⟨⟨0, fun _ => Nat.zero_le _⟩, (uCrit_iff _).mpr fun i => ⟨rfl, by have := i.2; omega⟩⟩

theorem critSet_subsingleton : Subsingleton (uSystem N).critSet :=
  ⟨fun p p' => Subtype.ext (Subtype.ext (funext fun i =>
    ((uCrit_iff p.1).mp p.2 i).1.trans ((uCrit_iff p'.1).mp p'.2 i).1.symm))⟩

/-- For `n ≤ 1`, `H(U_n) ≅ ℤ`, spanned by the class of `1_z` (`homologyU_small_symm_one`). -/
def homologyU_small (hN : N ≤ 1) : Homology (dU N) ≃ₗ[ℤ] ℤ :=
  letI := critSet_subsingleton (N := N)
  (homologyBasisU N).repr.trans (Finsupp.uniqueLinearEquiv ℤ ℤ (zeroCrit hN))

theorem homologyU_small_symm_one (hN : N ≤ 1) :
    (homologyU_small hN).symm 1 = homologyBasisU N (zeroCrit hN) := by
  have := critSet_subsingleton (N := N)
  rw [homologyU_small, LinearEquiv.symm_trans_apply]
  rw [show (Finsupp.uniqueLinearEquiv ℤ ℤ (zeroCrit hN)).symm 1 = Finsupp.single (zeroCrit hN) 1
    from rfl]
  exact (homologyBasisU N).repr_symm_single_one _


/-! ### The finite-cell filtration of `Z_n` -/

open scoped TensorProduct

/-- `Z_n ≅ (⨁_q Y_{A q}) ⊗ OΛ_n`: the composite of (3.38) (`EQZn.eq_3_38`) and the hypercube
decomposition of `U_n`. -/
def zDecompEquiv (N : ℕ) :
    (Π₀ q : Init (uSystem N), (Finset (Urn (uSystem N) q) →₀ ℤ)) ⊗[ℤ] osym N ≃ₗ[ℤ]
      SkewPolynomial N :=
  (TensorProduct.congr (uDecompEquiv N).symm (LinearEquiv.refl ℤ _)).trans
    (LinearEquiv.ofBijective (tensorMap N) eq_3_38.1)

/-- The parity involution of `U_n`, transported to the direct sum of hypercubes. -/
def iotaDecomp (N : ℕ) :
    (Π₀ q : Init (uSystem N), (Finset (Urn (uSystem N) q) →₀ ℤ)) →ₗ[ℤ]
      (Π₀ q : Init (uSystem N), (Finset (Urn (uSystem N) q) →₀ ℤ)) :=
  (uDecompEquiv N).toLinearMap ∘ₗ iotaU N ∘ₗ (uDecompEquiv N).symm.toLinearMap

/-- **The finite-cell filtration of `Z_n`** (Ellis–Qi, Appendix A.2): under
`Z_n ≅ (⨁_q Y_{A q}) ⊗ OΛ_n`, the differential of `Z_n` is
`d(y ⊗ c) = (⊕_q δ_q)(y) ⊗ c + ι(y) ⊗ d(c)`, a direct sum over the initial vectors `q` of hypercube
complexes tensored with the regular dg module `OΛ_n`. -/
theorem zDecompEquiv_d (t : (Π₀ q : Init (uSystem N), (Finset (Urn (uSystem N) q) →₀ ℤ)) ⊗[ℤ]
    osym N) :
    zDecompEquiv N (TensorProduct.map (DFinsupp.mapRange.linearMap
        (fun q => hyperDelta (uSystem N) uCoeff q)) LinearMap.id t +
      TensorProduct.map (iotaDecomp N) (dO N) t) = dAlpha (zAlpha N) (zDecompEquiv N t) := by
  induction t with
  | add x y hx hy =>
    simp only [map_add] at hx hy ⊢
    rw [← hx, ← hy]
    abel
  | tmul u c =>
    have hu : (uDecompEquiv N).symm (DFinsupp.mapRange.linearMap
        (fun q => hyperDelta (uSystem N) uCoeff q) u) = dU N ((uDecompEquiv N).symm u) := by
      rw [LinearEquiv.symm_apply_eq, uDecompEquiv_dU, LinearEquiv.apply_symm_apply]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, zDecompEquiv, LinearEquiv.trans_apply,
      map_add, TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.ofBijective_apply,
      iotaDecomp, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, hu]
    rw [← (eq_3_38 (N := N)).2.1]
    simp only [dTensor, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply, map_add]

end

end OddMath.Frontier.EQApp
