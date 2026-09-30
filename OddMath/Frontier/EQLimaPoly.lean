import OddMath.Frontier.EQLimaLR
import OddMath.Frontier.EQLimaCounting
import OddMath.Frontier.OddLRRuleLemma47

/-!
# Ellis–Qi, Proposition A.3, part 1: combinatorial preliminaries

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Proposition A.3. This file provides:

* `unitriangular`: a family which is unitriangular (leading coefficients `±1`) with respect to a
  basis, relative to a rank function, is again a basis;
* `domRank`: a rank function strictly increasing along the strict dominance order on partitions
  of a fixed size;
* `colPart m`: for `m : ℕ →₀ ℕ`, the Lima partition `Σ_k m_k (2^{2(k+1)})` (columns of height
  `2(k+1)` and width `2`, `m_k` of each); `colEquiv : (ℕ →₀ ℕ) ≃ {λ // IsLima λ}`;
* `isLima_transpose`: the transpose of a Lima partition is Lima.
-/

namespace OddMath.Frontier.EQLima

open Finset

/-! ### Unitriangular families -/

section Unitriangular

variable {M ι κ : Type*} [AddCommGroup M]

theorem repr_sum_smul (b : Module.Basis ι ℤ M) (l : κ →₀ ℤ) (v : κ → M) (i : ι) :
    b.repr (l.sum (fun j a => a • v j)) i = l.sum (fun j a => a * b.repr (v j) i) := by
  rw [map_finsuppSum, Finsupp.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_zsmul, Finsupp.smul_apply, smul_eq_mul]

/-- A family `v` which is unitriangular with respect to a basis `b` (leading coefficients `±1`
at `e j`, all other coefficients at indices of smaller rank) is a basis. -/
theorem unitriangular (b : Module.Basis ι ℤ M) (v : κ → M) (e : κ ≃ ι) (rank : ι → ℕ)
    (hlead : ∀ j, b.repr (v j) (e j) = 1 ∨ b.repr (v j) (e j) = -1)
    (hlow : ∀ j i, b.repr (v j) i ≠ 0 → i ≠ e j → rank i < rank (e j)) :
    LinearIndependent ℤ v ∧ ⊤ ≤ Submodule.span ℤ (Set.range v) := by
  classical
  constructor
  · rw [linearIndependent_iff]
    intro l hl
    by_contra hne
    obtain ⟨j0, hj0, hmax⟩ := l.support.exists_max_image (fun j => rank (e j))
      (Finsupp.support_nonempty_iff.mpr hne)
    have h0 := congrArg (fun x => b.repr x (e j0)) hl
    simp only [Finsupp.linearCombination_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h0
    rw [repr_sum_smul, Finsupp.sum, Finset.sum_eq_single j0] at h0
    · rcases hlead j0 with h | h <;> rw [h] at h0 <;> simp at h0 <;>
        exact Finsupp.mem_support_iff.mp hj0 h0
    · intro j hj hjne
      by_contra hc
      have hc' : b.repr (v j) (e j0) ≠ 0 := fun h => hc (by rw [h, mul_zero])
      have := hlow j (e j0) hc' (fun h => hjne (e.injective h).symm)
      have := hmax j hj
      omega
    · intro h; exact absurd hj0 h
  · have key : ∀ n, ∀ i, rank i = n → b i ∈ Submodule.span ℤ (Set.range v) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro i hi
      set j := e.symm i
      have hj : e j = i := e.apply_symm_apply i
      set c := b.repr (v j) with hc
      have hv : v j = c.sum (fun i' a => a • b i') := by
        conv_lhs => rw [← b.linearCombination_repr (v j)]
        rw [Finsupp.linearCombination_apply]
      have hmem : i ∈ c.support := by
        rw [Finsupp.mem_support_iff, ← hj]
        rcases hlead j with h | h <;> rw [h] <;> decide
      rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hmem] at hv
      have hrest : ∑ x ∈ c.support.erase i, c x • b x ∈ Submodule.span ℤ (Set.range v) := by
        refine Submodule.sum_mem _ fun i' hi' => Submodule.smul_of_tower_mem _ _ ?_
        obtain ⟨hne, hsupp⟩ := Finset.mem_erase.mp hi'
        refine ih (rank i') ?_ i' rfl
        rw [← hi, ← hj]
        exact hlow j i' (Finsupp.mem_support_iff.mp hsupp) (by rw [hj]; exact hne)
      have hvj : v j ∈ Submodule.span ℤ (Set.range v) := Submodule.subset_span ⟨j, rfl⟩
      have hci : c i • b i ∈ Submodule.span ℤ (Set.range v) := by
        have := Submodule.sub_mem _ hvj hrest
        rwa [hv, add_sub_cancel_right] at this
      rcases hlead j with h | h
      · rw [hj, ← hc] at h; rwa [h, one_smul] at hci
      · rw [hj, ← hc] at h
        have := Submodule.neg_mem _ hci
        simpa [h] using this
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact key _ i rfl)

end Unitriangular

/-! ### A rank function for dominance -/

theorem pre_eq_card {μ : YoungDiagram} {k : ℕ} (hk : μ.card ≤ k) : pre μ k = μ.card := by
  rw [← card_filter_row_lt, Finset.filter_true_of_mem]
  intro p hp
  have h1 : (p.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) hp
  rw [YoungDiagram.mem_iff_lt_colLen] at h1
  have := OddLRRule.colLen_le_card μ
  omega

theorem card_addRows (μ ν : YoungDiagram) : (addRows μ ν).card = μ.card + ν.card := by
  have h := pre_addRows μ ν ((addRows μ ν).card + μ.card + ν.card)
  rw [pre_eq_card (by omega), pre_eq_card (by omega), pre_eq_card (by omega)] at h
  exact h

/-- Sum of the prefix sums up to the size. -/
def domRank (μ : YoungDiagram) : ℕ := ∑ k ∈ range (μ.card + 1), pre μ k

theorem domRank_lt {μ ν : YoungDiagram} (h : Dom μ ν) (hc : μ.card = ν.card) (hne : μ ≠ ν) :
    domRank μ < domRank ν := by
  unfold domRank
  rw [hc]
  apply Finset.sum_lt_sum (fun k _ => h k)
  by_contra hall
  push Not at hall
  apply hne
  apply eq_of_pre
  intro k
  rcases Nat.lt_or_ge k (ν.card + 1) with hk | hk
  · exact le_antisymm (h k) (hall k (Finset.mem_range.mpr hk))
  · rw [pre_eq_card (by omega), pre_eq_card (by omega), hc]

/-! ### Transposes of Lima partitions -/

theorem double_transpose (ν : YoungDiagram) : (double ν).transpose = double ν.transpose := by
  apply YoungDiagram.ext
  ext c
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_transpose, mem_double,
    mem_double, YoungDiagram.mem_transpose]
  rfl

theorem isLima_transpose {μ : YoungDiagram} (h : IsLima μ) : IsLima μ.transpose := by
  obtain ⟨ν, rfl⟩ := (isLima_iff_exists_double μ).mp h
  rw [double_transpose]
  exact isLima_double _

theorem bot_transpose : (⊥ : YoungDiagram).transpose = ⊥ := by
  apply YoungDiagram.ext
  ext c
  simp [YoungDiagram.mem_transpose]

theorem isLima_bot : IsLima ⊥ := by
  intro k
  have : ∀ i, (⊥ : YoungDiagram).rowLen i = 0 := fun i => by
    by_contra h
    exact YoungDiagram.notMem_bot _ (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))
  rw [this, this]
  exact ⟨⟨0, rfl⟩, rfl⟩

theorem isLima_addRows {μ ν : YoungDiagram} (hμ : IsLima μ) (hν : IsLima ν) :
    IsLima (addRows μ ν) := by
  intro k
  rw [rowLen_addRows, rowLen_addRows, (hμ k).2, (hν k).2]
  exact ⟨(hμ k).1.add (hν k).1, rfl⟩

/-! ### Column multiplicities -/

/-- `S(m, r) = Σ_{j ≥ r} m_j`. -/
def tailSum (m : ℕ →₀ ℕ) (r : ℕ) : ℕ := m.sum (fun j n => if r ≤ j then n else 0)

theorem tailSum_add (m m' : ℕ →₀ ℕ) (r : ℕ) :
    tailSum (m + m') r = tailSum m r + tailSum m' r := by
  unfold tailSum
  rw [Finsupp.sum_add_index']
  · intro j; simp
  · intro j a b; split_ifs <;> simp

theorem tailSum_succ (m : ℕ →₀ ℕ) (r : ℕ) : tailSum m r = m r + tailSum m (r + 1) := by
  unfold tailSum
  have e : (fun j n => if r ≤ j then n else 0) =
      fun (j : ℕ) (n : ℕ) => (if r = j then n else 0) + (if r + 1 ≤ j then n else 0) := by
    funext j n
    split_ifs <;> omega
  rw [e, Finsupp.sum_add, Finsupp.sum_ite_self_eq]

theorem tailSum_anti (m : ℕ →₀ ℕ) {r s : ℕ} (h : r ≤ s) : tailSum m s ≤ tailSum m r := by
  unfold tailSum Finsupp.sum
  refine Finset.sum_le_sum fun j _ => ?_
  dsimp only
  split_ifs <;> omega

theorem tailSum_single (a r : ℕ) : tailSum (Finsupp.single a 1) r = if r ≤ a then 1 else 0 := by
  unfold tailSum
  rw [Finsupp.sum_single_index (by simp)]

theorem tailSum_eq_zero {m : ℕ →₀ ℕ} {r : ℕ} (h : ∀ j ∈ m.support, j < r) : tailSum m r = 0 := by
  unfold tailSum Finsupp.sum
  refine Finset.sum_eq_zero fun j hj => ?_
  have := h j hj
  dsimp only
  simp only [show ¬ r ≤ j by omega, ↓reduceIte]

/-- The partition with rows `S(m, r)`, i.e. with `m_k` columns of height `k + 1`. -/
def colMultPart (m : ℕ →₀ ℕ) : YoungDiagram where
  cells := ((range (m.support.sup id + 1)) ×ˢ (range (tailSum m 0))).filter
    (fun c => c.2 < tailSum m c.1)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨⟨h1, -⟩, h3⟩ := ha
    have h4 := tailSum_anti m hba.1
    have h5 := tailSum_anti m (Nat.zero_le b.1)
    have hb : b.2 < tailSum m b.1 := by have := hba.2; omega
    exact ⟨⟨by have := hba.1; omega, by omega⟩, hb⟩

theorem mem_colMultPart (m : ℕ →₀ ℕ) (c : ℕ × ℕ) : c ∈ colMultPart m ↔ c.2 < tailSum m c.1 := by
  change c ∈ (colMultPart m).cells ↔ _
  simp only [colMultPart, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, by have := tailSum_anti m (Nat.zero_le c.1); omega⟩, h⟩
    by_contra hc
    rw [tailSum_eq_zero (fun j hj => by
      have := Finset.le_sup (f := id) hj; simp only [id] at this; omega)] at h
    omega

theorem rowLen_colMultPart (m : ℕ →₀ ℕ) (r : ℕ) : (colMultPart m).rowLen r = tailSum m r :=
  rowLen_eq_of fun j => by rw [mem_colMultPart]

/-- `Σ_k m_k (2^{2(k+1)})`: the Lima partition with `m_k` blocks of two columns of height
`2(k+1)`. -/
def colPart (m : ℕ →₀ ℕ) : YoungDiagram := double (colMultPart m)

theorem rowLen_colPart (m : ℕ →₀ ℕ) (r : ℕ) : (colPart m).rowLen r = 2 * tailSum m (r / 2) := by
  rw [colPart, rowLen_double, rowLen_colMultPart]

theorem isLima_colPart (m : ℕ →₀ ℕ) : IsLima (colPart m) := isLima_double _

theorem colPart_add (m m' : ℕ →₀ ℕ) : colPart (m + m') = addRows (colPart m) (colPart m') := by
  apply eq_of_pre
  intro k
  rw [pre_addRows]
  simp only [pre, rowLen_colPart, tailSum_add, ← Finset.sum_add_distrib, mul_add]

theorem colPart_zero : colPart 0 = ⊥ := by
  apply YoungDiagram.ext
  ext c
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, rowLen_colPart]
  simp [tailSum]

/-- The generator shape `(2^{2(a+1)})`: two columns of height `2(a+1)`. -/
theorem rowLen_colPart_single (a r : ℕ) :
    (colPart (Finsupp.single a 1)).rowLen r = if r < 2 * (a + 1) then 2 else 0 := by
  rw [rowLen_colPart, tailSum_single]
  split_ifs <;> omega

/-- The column multiplicities of a Lima partition. -/
noncomputable def colMult (μ : YoungDiagram) : ℕ →₀ ℕ :=
  Finsupp.onFinset (range (μ.colLen 0)) (fun k => (μ.rowLen (2 * k) - μ.rowLen (2 * k + 2)) / 2)
    (by
      intro k hk
      rw [Finset.mem_range]
      by_contra hc
      have : μ.rowLen (2 * k) = 0 := by
        by_contra h0
        have := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h0)
        rw [YoungDiagram.mem_iff_lt_colLen] at this
        omega
      apply hk
      rw [this]
      simp)

theorem colMult_apply (μ : YoungDiagram) (k : ℕ) :
    colMult μ k = (μ.rowLen (2 * k) - μ.rowLen (2 * k + 2)) / 2 := rfl

theorem colMult_colPart (m : ℕ →₀ ℕ) : colMult (colPart m) = m := by
  ext k
  rw [colMult_apply, rowLen_colPart, rowLen_colPart, show 2 * k / 2 = k by omega,
    show (2 * k + 2) / 2 = k + 1 by omega, tailSum_succ m k]
  omega

theorem tailSum_colMult {μ : YoungDiagram} (h : IsLima μ) (r : ℕ) :
    2 * tailSum (colMult μ) r = μ.rowLen (2 * r) := by
  -- downward induction from a row beyond the diagram
  have hbound : ∀ r, μ.colLen 0 ≤ 2 * r → 2 * tailSum (colMult μ) r = μ.rowLen (2 * r) := by
    intro r hr
    have h0 : μ.rowLen (2 * r) = 0 := by
      by_contra h0
      have := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h0)
      rw [YoungDiagram.mem_iff_lt_colLen] at this
      omega
    rw [h0, tailSum_eq_zero]
    intro j hj
    have := (Finsupp.mem_support_iff.mp hj)
    rw [colMult_apply] at this
    by_contra hc
    have hle := μ.rowLen_anti (2 * r) (2 * j) (by omega)
    rw [h0] at hle
    have : μ.rowLen (2 * j) = 0 := by omega
    simp_all
  have key : ∀ n r, μ.colLen 0 ≤ 2 * (r + n) → 2 * tailSum (colMult μ) r = μ.rowLen (2 * r) := by
    intro n
    induction n with
    | zero => intro r hr; exact hbound r (by simpa using hr)
    | succ n ih =>
      intro r hr
      have := ih (r + 1) (by omega)
      rw [tailSum_succ, colMult_apply, mul_add, this]
      have hle := μ.rowLen_anti (2 * r) (2 * (r + 1)) (by omega)
      have he1 := (even_iff_mod _).mp (h r).1
      have he2 := (even_iff_mod _).mp (h (r + 1)).1
      rw [show 2 * (r + 1) = 2 * r + 2 by ring] at *
      omega
  exact key (μ.colLen 0) r (by omega)

theorem colPart_colMult {μ : YoungDiagram} (h : IsLima μ) : colPart (colMult μ) = μ := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, rowLen_colPart, tailSum_colMult h]
  have : μ.rowLen i = μ.rowLen (2 * (i / 2)) := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
    · subst hk; rw [show 2 * k / 2 = k by omega]
    · subst hk; rw [show (2 * k + 1) / 2 = k by omega, (h k).2]
  rw [this]

/-- Lima partitions correspond to multisets of column-block heights. -/
noncomputable def colEquiv : (ℕ →₀ ℕ) ≃ {μ : YoungDiagram // IsLima μ} where
  toFun m := ⟨colPart m, isLima_colPart m⟩
  invFun μ := colMult μ.1
  left_inv m := colMult_colPart m
  right_inv μ := Subtype.ext (colPart_colMult μ.2)

end OddMath.Frontier.EQLima
