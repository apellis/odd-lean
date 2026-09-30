import OddMath.Frontier.EQZabModule

/-!
# The differential of `Z_{a,b}` on the Schur basis (Ellis–Qi, Lemma 4.7, Corollary 4.8)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, (4.23), Lemma 4.7, Corollary 4.8 and the discussion after Proposition 4.12 (printed
numbering).

Conventions as in `EQZabModule`: strands and rows numbered from `0`, `y = (x_a, …, x_{a+b-1})`,
`s_λ = untwisted b λ`, `s̃_λ = twisted b λ` (Ellis–Qi (3.24), (3.25)), `{m} = m mod 2`. For an
exponent vector `λ : Fin b → ℕ`, `|λ/i| = Σ_{j<i} λ_j` (`rowsAbove`), `|i/λ| = Σ_{j>i} λ_j`
(`rowsBelow`) and `ct(□_i) = λ_i - i` (`content`). `Par(b,a)` (partitions with at most `b` rows
and at most `a` columns) is `ParBox b a`.

* `pieri_untwisted` (the odd Pieri rule (4.23), transported by `θ` to untwisted Schur
  polynomials): `s_λ e_1 = Σ_i (-1)^{|i/λ|} s_{λ + ε_i}`, for every exponent vector `λ` and every
  rank (from EKL Proposition 2.26, `OddSchurPieri`); `pieri_twisted` is (4.23) itself,
  `s̃_λ ẽ_1 = Σ_i (-1)^{|i/λ|} s̃_{λ+ε_i}`.
* `dZ_schur` : `d(s_λ(y) z) = Σ_i (-1)^{|λ/i| + i} {a + ct(□_i)} s_{λ+ε_i}(y) z` for every
  exponent vector.
* **Lemma 4.7** (`lemma_4_7`, `lemma_4_7_box`): for a partition `λ`, the sum runs over the
  partitions `μ = λ + □_i` (0-indexed rows, so the printed sign `(-1)^{|λ/i| + i - 1}` reads
  `(-1)^{|λ/i| + i}`); for `λ ∈ Par(b,a)` it runs over `μ ∈ Par(b,a)`, because the only box that
  leaves the `b × a` box is in row `0` and has coefficient `{2a} = 0`. `lemma_4_7_twisted` and
  `lemma_4_7_box_twisted` are the same statements for Ellis–Qi's literal `s̃_λ(y) z` in the
  twisted model (`dT`).
* **Corollary 4.8**, first part (`cor_4_8_stable`, `cor_4_8_stable_twisted`): the `ℤ`-span
  `V_{a,b}` of `{s̃_μ(y) z : μ ∈ Par(b,a)}` is `d`-stable; `dZ_rectangle`: `d(s̃_{(a^b)}(y) z) = 0`.
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open FiniteCompleteElementary
open scoped BigOperators

noncomputable section

local instance (priority := high) zabSchurNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabSchurNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ## The Pieri rule -/

/-- `|i/λ| = Σ_{j>i} λ_j`: the boxes in the rows below row `i`. -/
def rowsBelow {N : ℕ} (l : Fin N → ℕ) (i : Fin N) : ℕ := ∑ j, if i < j then l j else 0

theorem theta_elementary (N k : ℕ) : theta N (elementary N k) = elementaryPoly N k := by
  rw [elementaryPoly_eq_strictSum, elementary, ringHom_strictSum]
  congr 1
  funext j
  rw [theta_generator]
  rfl

open OddSchurPieri OddSymmetrizer in
/-- EKL's right Pieri computation (Proposition 2.26) for an arbitrary exponent vector. -/
theorem pieri_general (n k : ℕ) (a : Fin (n+2) → ℕ) :
    S n (monomial a 1) * ((-1 : ℤ)^k.choose 2 • elementaryPoly (n+2) k) =
      ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin (n+2)) => I.card = k),
        (-1 : ℤ)^lowerRows a I • S n (monomial (increment a I) 1) := by
  classical
  rw [right_elementary_transport, elementary_subsets, Finset.mul_sum, map_sum,
    map_sum, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hc := (Finset.mem_filter.mp hI).2
  rw [pieri_normal_order (by omega)]
  simp only [map_zsmul]
  rw [hc]
  simp only [S_apply, smul_smul, show n+2-1 = n+1 by omega]
  have hs : (-1 : ℤ)^(k*(n+1).choose 2) * (-1 : ℤ)^(k*(n+1).choose 2) = 1 := by
    rw [← mul_pow]; norm_num
  congr 1
  calc
    _ = ((-1 : ℤ)^(k*(n+1).choose 2) * (-1 : ℤ)^(k*(n+1).choose 2)) *
        ((-1 : ℤ)^lowerRows a I * (-1 : ℤ)^((n+2).choose 3)) := by ring
    _ = _ := by rw [hs, one_mul]

theorem twisted_eq_S (n : ℕ) (a : Fin (n+2) → ℕ) : twisted (n+2) a = OddSymmetrizer.S n (monomial a 1) := by
  rw [twisted_eq_ekl]
  rfl

/-- **Ellis–Qi (4.23)** (the odd Pieri rule of [EOddLR, Proposition 3.6], i.e. EKL
Proposition 2.26 for `k = 1`), for every exponent vector `λ` and every rank:
`s̃_λ ẽ_1 = Σ_i (-1)^{|i/λ|} s̃_{λ + ε_i}`, `ẽ_1 = θ(e_1)`. Terms with `λ + ε_i` not a partition
vanish when `λ` is a partition. -/
theorem pieri_twisted {N : ℕ} (l : Fin N → ℕ) :
    twisted N l * elementaryPoly N 1 =
      ∑ i, (-1 : ℤ) ^ rowsBelow l i • twisted N (l + expSingle i) := by
  classical
  rcases N with _ | _ | n
  · simp [elementaryPoly_eq_strictSum]
  · have h1 : ∀ m : Fin (0+1) → ℕ, twisted (0+1) m = monomial m 1 := fun m => by
      rw [twisted_eq_schurAll, SmallRank.schurAll_small (by norm_num)]
    have hrb : rowsBelow l 0 = 0 := by simp [rowsBelow]
    have he : elementaryPoly (0+1) 1 = monomial (expSingle 0) 1 := by
      rw [elementaryPoly_eq_strictSum, strictSum_one, Fin.sum_univ_one,
        PlacticEvaluation.tildeGenerator, Fin.val_zero, pow_zero, one_smul]
      rfl
    rw [Fin.sum_univ_one, h1, h1, he, hrb, pow_zero, one_smul, OddSchurPieri.mono_mul,
      SmallRank.skewSign_small (by norm_num), one_smul]
  · have h := pieri_general n 1 l
    rw [show (1 : ℕ).choose 2 = 0 from rfl, pow_zero, one_smul] at h
    rw [twisted_eq_S, h]
    have hset : Finset.univ.filter (fun I : Finset (Fin (n+2)) => I.card = 1) =
        Finset.univ.map ⟨fun i => {i}, Finset.singleton_injective⟩ := by
      ext I
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk, Finset.card_eq_one]
      exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩
    rw [hset, Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.Embedding.coeFn_mk]
    have hinc : OddSchurPieri.increment l {i} = l + expSingle i := by
      funext j
      simp [OddSchurPieri.increment, expSingle, eq_comm]
    have hlow : OddSchurPieri.lowerRows l {i} = rowsBelow l i := by
      simp [OddSchurPieri.lowerRows, rowsBelow, Finset.sum_filter]
    rw [hinc, hlow, twisted_eq_S]

/-- The Pieri rule for untwisted odd Schur polynomials:
`s_λ e_1 = Σ_i (-1)^{|i/λ|} s_{λ + ε_i}`, for every exponent vector `λ` and every rank. -/
theorem pieri_untwisted {N : ℕ} (l : Fin N → ℕ) :
    untwisted N l * elementary N 1 =
      ∑ i, (-1 : ℤ) ^ rowsBelow l i • untwisted N (l + expSingle i) := by
  have he : elementary N 1 = theta N (elementaryPoly N 1) := by
    rw [← theta_elementary, theta_theta]
  rw [untwisted_eq_theta_twisted, he, ← map_mul, pieri_twisted, map_sum]
  simp only [map_zsmul, ← untwisted_eq_theta_twisted]

/-! ## Lemma 4.7 -/

theorem neg_one_pow_cases (x : ℕ) :
    ((-1 : ℤ) ^ x = 1 ∧ x % 2 = 0) ∨ ((-1 : ℤ) ^ x = -1 ∧ x % 2 = 1) := by
  rcases Nat.even_or_odd x with h | h
  · exact Or.inl ⟨h.neg_one_pow, Nat.even_iff.mp h⟩
  · exact Or.inr ⟨h.neg_one_pow, Nat.odd_iff.mp h⟩

/-- The sign bookkeeping of the proof of Lemma 4.7:
`(-1)^{|λ/i|+i} {ct} + {a} (-1)^{|λ|} (-1)^{|i/λ|} = (-1)^{|λ/i|+i} {a + ct}`, with
`|λ| = |λ/i| + λ_i + |i/λ|` and `ct = λ_i - i`. -/
theorem coeff_identity (rA rB li i a : ℕ) :
    (-1 : ℤ) ^ (rA + i) * (((li : ℤ) - i) % 2) +
        ((a % 2 : ℕ) : ℤ) * (-1 : ℤ) ^ (rA + li + rB) * (-1 : ℤ) ^ rB =
      (-1 : ℤ) ^ (rA + i) * (((a : ℤ) + ((li : ℤ) - i)) % 2) := by
  simp only [pow_add]
  rcases neg_one_pow_cases rA with ⟨e1, p1⟩ | ⟨e1, p1⟩ <;>
  rcases neg_one_pow_cases rB with ⟨e2, p2⟩ | ⟨e2, p2⟩ <;>
  rcases neg_one_pow_cases li with ⟨e3, p3⟩ | ⟨e3, p3⟩ <;>
  rcases neg_one_pow_cases i with ⟨e4, p4⟩ | ⟨e4, p4⟩ <;>
  simp only [e1, e2, e3, e4] <;> omega

theorem sum_eq_rowsAbove_add (l : Fin b → ℕ) (i : Fin b) :
    ∑ j, l j = rowsAbove l i + l i + rowsBelow l i := by
  rw [sum_split l i, rowsAbove_eq, rowsBelow]

variable {a b : ℕ}

/-- The differential of `Z_{a,b}` on `s_λ(y) z` for every exponent vector `λ`:
`d(s_λ(y) z) = Σ_i (-1)^{|λ/i| + i} {a + ct(□_i)} s_{λ+ε_i}(y) z`. -/
theorem dZ_schur (l : Fin b → ℕ) :
    dZ a b (inclY a b (untwisted b l)) =
      ∑ i, ((-1 : ℤ) ^ (rowsAbove l i + i.val) * (((a : ℤ) + content l i) % 2)) •
        inclY a b (untwisted b (l + expSingle i)) := by
  rw [dZ_apply, d_inclY, parityInv_inclY, mul_smul_comm, ← map_mul, ← map_zsmul, ← map_add,
    d_untwisted, parityInv_untwisted, smul_mul_assoc, pieri_untwisted, Finset.smul_sum,
    Finset.smul_sum, ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, smul_smul, ← add_smul, map_zsmul]
  congr 1
  rw [sum_eq_rowsAbove_add l i, content]
  exact coeff_identity _ _ _ _ _

/-- A partition plus a box in a row where it is not a partition gives `s = 0`. -/
theorem untwisted_add_expSingle_eq_zero {N : ℕ} {l : Fin N → ℕ} (hl : Antitone l) {i : Fin N}
    (h : ¬Antitone (l + expSingle i)) : untwisted N (l + expSingle i) = 0 := by
  rcases N with _ | _ | n
  · exact i.elim0
  · exact absurd (fun p q _ => le_of_eq (congrArg _
      (Fin.ext (by have := p.isLt; have := q.isLt; omega)))) h
  · obtain ⟨j, rfl, hjl⟩ := exists_step_of_not_antitone hl h
    rw [untwisted_eq_zero_of_step _ j]
    simp [expSingle, hjl, (Fin.castSucc_lt_succ (i := j)).ne']

open Classical in
/-- **Ellis–Qi, Lemma 4.7** (sum over all partitions `μ = λ + □_i`): for a partition `λ` with at
most `b` rows, `d(s̃_λ(y) z) = Σ_{μ = λ + □_i} (-1)^{|λ/i| + i - 1} {a + ct(□_i)} s̃_μ(y) z`,
here in the untwisted model (`s̃_λ(y) z` is represented by `s_λ(y)`) with rows numbered from
`0`, so that the sign reads `(-1)^{|λ/i| + i}`. -/
theorem lemma_4_7 (l : Fin b → ℕ) (hl : Antitone l) :
    dZ a b (inclY a b (untwisted b l)) =
      ∑ i, if Antitone (l + expSingle i) then
        ((-1 : ℤ) ^ (rowsAbove l i + i.val) * (((a : ℤ) + content l i) % 2)) •
          inclY a b (untwisted b (l + expSingle i))
      else 0 := by
  rw [dZ_schur]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rw [untwisted_add_expSingle_eq_zero hl h, map_zero, smul_zero]

/-- `Par(b,a)`: partitions with at most `b` rows and at most `a` columns. -/
def ParBox (b a : ℕ) := {l : Fin b → ℕ // Antitone l ∧ ∀ j, l j ≤ a}

/-- Adding a box to a partition in `Par(b,a)` in a row already of length `a` is only possible in
row `0`, where the coefficient `{a + ct} = {2a}` vanishes. -/
theorem coeff_out_of_box {l : Fin b → ℕ} (hla : ∀ j, l j ≤ a) {i : Fin b}
    (hi : Antitone (l + expSingle i)) (hia : ¬ l i < a) :
    ((a : ℤ) + content l i) % 2 = 0 := by
  have hli : l i = a := le_antisymm (hla i) (not_lt.mp hia)
  have hi0 : i.val = 0 := by
    by_contra hne
    let j : Fin b := ⟨i.val - 1, by omega⟩
    have hji : j ≤ i := Fin.mk_le_mk.mpr (by omega)
    have h1 := hi hji
    have hjne : i ≠ j := fun e => hne (by have := congrArg Fin.val e; simp [j] at this; omega)
    simp [expSingle, hjne] at h1
    have := hla j
    omega
  rw [content, hli, hi0]
  omega

open Classical in
/-- **Ellis–Qi, Lemma 4.7** as printed: for `λ ∈ Par(b,a)`, the sum runs over the partitions
`μ = λ + □_i ∈ Par(b,a)`. -/
theorem lemma_4_7_box (l : Fin b → ℕ) (hl : Antitone l) (hla : ∀ j, l j ≤ a) :
    dZ a b (inclY a b (untwisted b l)) =
      ∑ i, if Antitone (l + expSingle i) ∧ l i < a then
        ((-1 : ℤ) ^ (rowsAbove l i + i.val) * (((a : ℤ) + content l i) % 2)) •
          inclY a b (untwisted b (l + expSingle i))
      else 0 := by
  rw [lemma_4_7 l hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : Antitone (l + expSingle i)
  · by_cases h2 : l i < a
    · simp [h1, h2]
    · rw [coeff_out_of_box hla h1 h2]
      simp [h1, h2]
  · simp [h1]

/-! ## The twisted form -/

theorem tauAB_inclY_untwisted (l : Fin b → ℕ) :
    tauAB a b (inclY a b (untwisted b l)) = inclY a b (twisted b l) := by
  rw [tauAB_inclY, twisted_eq_theta_untwisted]

theorem tauAB_inclY_twisted (l : Fin b → ℕ) :
    tauAB a b (inclY a b (twisted b l)) = inclY a b (untwisted b l) := by
  rw [← tauAB_inclY_untwisted, tauAB_tauAB]

open Classical in
/-- **Ellis–Qi, Lemma 4.7**, literally: in `Z_{a,b} = OΛ̃_a ⊠ OΛ̃_b · z` with the differential of
Definition 4.6 (`dT`), `d(s̃_λ(y) z) = Σ_{μ = λ + □_i} (-1)^{|λ/i| + i - 1} {a + ct(□_i)} s̃_μ(y) z`
(rows numbered from `0`). -/
theorem lemma_4_7_twisted (l : Fin b → ℕ) (hl : Antitone l) :
    dT a b (inclY a b (twisted b l)) =
      ∑ i, if Antitone (l + expSingle i) then
        ((-1 : ℤ) ^ (rowsAbove l i + i.val) * (((a : ℤ) + content l i) % 2)) •
          inclY a b (twisted b (l + expSingle i))
      else 0 := by
  rw [dT_apply, tauAB_inclY_twisted, lemma_4_7 l hl, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [map_zsmul, tauAB_inclY_untwisted]
  · rw [map_zero]

open Classical in
/-- **Ellis–Qi, Lemma 4.7**, literally and with the sum over `μ ∈ Par(b,a)`. -/
theorem lemma_4_7_box_twisted (l : Fin b → ℕ) (hl : Antitone l) (hla : ∀ j, l j ≤ a) :
    dT a b (inclY a b (twisted b l)) =
      ∑ i, if Antitone (l + expSingle i) ∧ l i < a then
        ((-1 : ℤ) ^ (rowsAbove l i + i.val) * (((a : ℤ) + content l i) % 2)) •
          inclY a b (twisted b (l + expSingle i))
      else 0 := by
  rw [dT_apply, tauAB_inclY_twisted, lemma_4_7_box l hl hla, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [map_zsmul, tauAB_inclY_untwisted]
  · rw [map_zero]

/-! ## Corollary 4.8: the `d`-stable span -/

/-- `V_{a,b}` in the untwisted model: the `ℤ`-span of the `s_μ(y)`, `μ ∈ Par(b,a)`. -/
def schurSpan (a b : ℕ) : Submodule ℤ (SkewPolynomial (a+b)) :=
  Submodule.span ℤ (Set.range fun μ : ParBox b a => inclY a b (untwisted b μ.val))

/-- `V_{a,b} = ⊕_{μ ∈ Par(b,a)} ℤ s̃_μ(y) z` (Ellis–Qi, after Proposition 4.12). -/
def schurSpanT (a b : ℕ) : Submodule ℤ (SkewPolynomial (a+b)) :=
  Submodule.span ℤ (Set.range fun μ : ParBox b a => inclY a b (twisted b μ.val))

theorem add_box_mem {l : Fin b → ℕ} (hla : ∀ j, l j ≤ a) {i : Fin b}
    (h : Antitone (l + expSingle i) ∧ l i < a) : ∀ j, (l + expSingle i) j ≤ a := by
  intro j
  simp only [Pi.add_apply, expSingle]
  split_ifs with hij
  · subst hij; have := h.2; omega
  · simpa using hla j

open Classical in
theorem dZ_schur_mem (μ : ParBox b a) : dZ a b (inclY a b (untwisted b μ.val)) ∈ schurSpan a b := by
  rw [lemma_4_7_box μ.val μ.property.1 μ.property.2]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨μ.val + expSingle i, h.1, add_box_mem μ.property.2 h⟩, rfl⟩)
  · exact Submodule.zero_mem _

/-- **Ellis–Qi, Corollary 4.8** (first part), untwisted model: the `ℤ`-span of the basis
`{s̃_μ(y) z : μ ∈ Par(b,a)}` is `d`-stable. -/
theorem cor_4_8_stable {F : SkewPolynomial (a+b)} (hF : F ∈ schurSpan a b) :
    dZ a b F ∈ schurSpan a b := by
  induction hF using Submodule.span_induction with
  | mem x hx => obtain ⟨μ, rfl⟩ := hx; exact dZ_schur_mem μ
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ c hx

theorem schurSpanT_eq_map : schurSpanT a b = (schurSpan a b).map (tauAB a b).toAddMonoidHom.toIntLinearMap := by
  rw [schurSpan, schurSpanT, Submodule.map_span, ← Set.range_comp]
  refine congrArg _ (congrArg Set.range (funext fun μ => ?_))
  exact (tauAB_inclY_untwisted μ.val).symm

/-- **Ellis–Qi, Corollary 4.8** (first part), literally: `V_{a,b} = span_ℤ{s̃_μ(y) z : μ ∈ Par(b,a)}`
is stable under the differential of Definition 4.6. -/
theorem cor_4_8_stable_twisted {G : SkewPolynomial (a+b)} (hG : G ∈ schurSpanT a b) :
    dT a b G ∈ schurSpanT a b := by
  rw [schurSpanT_eq_map] at hG ⊢
  obtain ⟨F, hF, rfl⟩ := hG
  refine ⟨dZ a b F, cor_4_8_stable hF, ?_⟩
  simp [dT_apply, tauAB_tauAB]

/-- The full rectangle `(a^b)` (`b` rows of length `a`) is a cycle: `d(s̃_{(a^b)}(y) z) = 0`
(Ellis–Qi, after Proposition 4.12): the only box that can be added to a partition with at most `b`
rows lies in row `0`, with coefficient `{a + a} = 0`. -/
theorem dZ_rectangle : dZ a b (inclY a b (untwisted b (fun _ => a))) = 0 := by
  rw [lemma_4_7_box _ (fun _ _ _ => le_rfl) (fun _ => le_rfl)]
  exact Finset.sum_eq_zero fun i _ => by simp

end

end OddMath.Frontier.EQZab
