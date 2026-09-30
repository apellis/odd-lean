import OddMath.Frontier.EQLimaPartitions
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin

/-!
# Ellis–Qi, Appendix A.1: Lima partitions are doubled partitions

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.1.2: "a Lima partition is a partition whose Young diagram can be subdivided into
`2 × 2` squares of boxes".

* `double ν`: replace every box of `ν` by a `2 × 2` square; `mem_double`, `rowLen_double`,
  `card_double` (`|double ν| = 4 |ν|`).
* `isLima_iff_exists_double`: `μ` is a Lima partition iff `μ = double ν` for some `ν`.
* `limaEquiv`: Lima partitions are in bijection with all partitions, with `|μ| = 4 |ν|`.

This is the counting input of the proof of Proposition A.3: the Lima partitions of size `4m`
(the degree-`4m` part of the basis of `H(OΛ)` given by Proposition A.2) are counted by the
partitions of `m`, which is the graded rank of a polynomial algebra with one generator in each
degree `4k`, `k ≥ 1`.
-/

namespace OddMath.Frontier.EQLima

open Finset

/-- Replace every box of `ν` by a `2 × 2` square. -/
def double (ν : YoungDiagram) : YoungDiagram where
  cells := ((range (2 * ν.colLen 0)) ×ˢ (range (2 * ν.rowLen 0))).filter
    (fun c => (c.1 / 2, c.2 / 2) ∈ ν)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨-, ha⟩ := ha
    have hb : (b.1 / 2, b.2 / 2) ∈ ν :=
      ν.up_left_mem (Nat.div_le_div_right hba.1) (Nat.div_le_div_right hba.2) ha
    refine ⟨⟨?_, ?_⟩, hb⟩
    · have := ν.up_left_mem le_rfl (Nat.zero_le _) hb
      rw [YoungDiagram.mem_iff_lt_colLen] at this
      omega
    · have := ν.up_left_mem (Nat.zero_le _) le_rfl hb
      rw [YoungDiagram.mem_iff_lt_rowLen] at this
      omega

theorem mem_double (ν : YoungDiagram) (c : ℕ × ℕ) : c ∈ double ν ↔ (c.1 / 2, c.2 / 2) ∈ ν := by
  change c ∈ (double ν).cells ↔ _
  simp only [double, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · have := ν.up_left_mem le_rfl (Nat.zero_le _) h
      rw [YoungDiagram.mem_iff_lt_colLen] at this
      omega
    · have := ν.up_left_mem (Nat.zero_le _) le_rfl h
      rw [YoungDiagram.mem_iff_lt_rowLen] at this
      omega

theorem rowLen_double (ν : YoungDiagram) (r : ℕ) : (double ν).rowLen r = 2 * ν.rowLen (r / 2) := by
  apply rowLen_eq_of
  intro j
  rw [mem_double, YoungDiagram.mem_iff_lt_rowLen]
  dsimp only
  omega

theorem isLima_double (ν : YoungDiagram) : IsLima (double ν) := by
  intro k
  rw [rowLen_double, rowLen_double, show 2 * k / 2 = k by omega, show (2 * k + 1) / 2 = k by omega]
  exact ⟨even_two_mul _, rfl⟩

/-- The partition whose `2 × 2` blocks are the boxes `(2i, 2j)` of `μ`. -/
def half (μ : YoungDiagram) : YoungDiagram where
  cells := ((range (μ.colLen 0)) ×ˢ (range (μ.rowLen 0))).filter
    (fun c => (2 * c.1, 2 * c.2) ∈ μ)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨-, ha⟩ := ha
    have hb : (2 * b.1, 2 * b.2) ∈ μ :=
      μ.up_left_mem (by have := hba.1; omega) (by have := hba.2; omega) ha
    refine ⟨⟨?_, ?_⟩, hb⟩
    · have := μ.up_left_mem le_rfl (Nat.zero_le _) hb
      rw [YoungDiagram.mem_iff_lt_colLen] at this
      omega
    · have := μ.up_left_mem (Nat.zero_le _) le_rfl hb
      rw [YoungDiagram.mem_iff_lt_rowLen] at this
      omega

theorem mem_half (μ : YoungDiagram) (c : ℕ × ℕ) : c ∈ half μ ↔ (2 * c.1, 2 * c.2) ∈ μ := by
  change c ∈ (half μ).cells ↔ _
  simp only [half, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · have := μ.up_left_mem le_rfl (Nat.zero_le _) h
      rw [YoungDiagram.mem_iff_lt_colLen] at this
      omega
    · have := μ.up_left_mem (Nat.zero_le _) le_rfl h
      rw [YoungDiagram.mem_iff_lt_rowLen] at this
      omega

theorem half_double (ν : YoungDiagram) : half (double ν) = ν := by
  apply YoungDiagram.ext
  ext c
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, mem_half, mem_double]
  simp only [show ∀ m : ℕ, 2 * m / 2 = m from fun m => by omega]

theorem double_half {μ : YoungDiagram} (h : IsLima μ) : double (half μ) = μ := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, mem_double, mem_half,
    YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen]
  simp only
  have hr : μ.rowLen i = μ.rowLen (2 * (i / 2)) := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
    · subst hk; rw [show 2 * k / 2 = k by omega]
    · subst hk; rw [show (2 * k + 1) / 2 = k by omega, (h k).2]
  have he := (even_iff_mod _).mp (h (i / 2)).1
  rw [hr]
  omega

/-- A partition is a Lima partition iff its diagram is tiled by `2 × 2` squares, i.e. it is
`double ν` for some partition `ν`. -/
theorem isLima_iff_exists_double (μ : YoungDiagram) : IsLima μ ↔ ∃ ν, μ = double ν :=
  ⟨fun h => ⟨half μ, (double_half h).symm⟩, fun ⟨ν, hν⟩ => hν ▸ isLima_double ν⟩

theorem card_double (ν : YoungDiagram) : (double ν).card = 4 * ν.card := by
  have e : (double ν).cells = (ν.cells ×ˢ (univ : Finset (Fin 2 × Fin 2))).image
      (fun x => (2 * x.1.1 + x.2.1.val, 2 * x.1.2 + x.2.2.val)) := by
    ext c
    rw [YoungDiagram.mem_cells, mem_double, Finset.mem_image]
    constructor
    · intro h
      refine ⟨((c.1 / 2, c.2 / 2), (⟨c.1 % 2, Nat.mod_lt _ (by norm_num)⟩,
        ⟨c.2 % 2, Nat.mod_lt _ (by norm_num)⟩)), ?_, ?_⟩
      · simp only [Finset.mem_product, YoungDiagram.mem_cells, Finset.mem_univ, and_true]
        exact h
      · obtain ⟨c1, c2⟩ := c
        simp only [Prod.mk.injEq]
        omega
    · rintro ⟨⟨⟨a1, a2⟩, ⟨e1, e2⟩⟩, hx, rfl⟩
      simp only [Finset.mem_product, YoungDiagram.mem_cells, Finset.mem_univ, and_true] at hx
      have h1 : (2 * a1 + e1.val) / 2 = a1 := by have := e1.2; omega
      have h2 : (2 * a2 + e2.val) / 2 = a2 := by have := e2.2; omega
      simp only [h1, h2]
      exact hx
  rw [YoungDiagram.card, e, Finset.card_image_of_injective, Finset.card_product,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, YoungDiagram.card]
  · ring
  · rintro ⟨⟨a1, a2⟩, ⟨e1, e2⟩⟩ ⟨⟨b1, b2⟩, ⟨f1, f2⟩⟩ h
    simp only [Prod.mk.injEq] at h
    have := e1.2; have := e2.2; have := f1.2; have := f2.2
    have ha1 : a1 = b1 := by omega
    have ha2 : a2 = b2 := by omega
    have he1 : e1 = f1 := Fin.ext (by omega)
    have he2 : e2 = f2 := Fin.ext (by omega)
    subst ha1 ha2 he1 he2
    rfl

/-- Lima partitions are in bijection with all partitions (`μ ↦ ν` with `μ = double ν`), and
`|μ| = 4 |ν|`. -/
def limaEquiv : {μ : YoungDiagram // IsLima μ} ≃ YoungDiagram where
  toFun μ := half μ.1
  invFun ν := ⟨double ν, isLima_double ν⟩
  left_inv μ := Subtype.ext (double_half μ.2)
  right_inv ν := half_double ν

theorem card_eq_four_mul_card_limaEquiv (μ : {μ : YoungDiagram // IsLima μ}) :
    μ.1.card = 4 * (limaEquiv μ).card := by
  conv_lhs => rw [← double_half μ.2]
  exact card_double _

end OddMath.Frontier.EQLima
