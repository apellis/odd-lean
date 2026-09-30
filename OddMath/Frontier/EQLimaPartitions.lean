import OddMath.Frontier.EQLimaHypercube
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity

/-!
# Ellis–Qi, Appendix A.1.2–A.1.3: white boxes and Lima partitions

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.1.2 (Lima partitions) and A.1.3 (Lemma A.1 and the combinatorial part of the proof of
Proposition A.2).

Partitions are Mathlib's `YoungDiagram`s; a cell is `(i, j)` with `i` the row and `j` the column,
both starting at `0`.  The content of `(i, j)` is `j - i` (Subsection 3.3 of the paper uses
`1`-based rows and columns, which does not change the content).  A box is *white* if its content
is odd and *black* if its content is even.

* `Addable`, `Removable`, `addCell`, `remCell`: adding and removing boxes.
* `addable_addCell_iff`, `removable_addCell_iff` and `lemma_A_1`: Lemma A.1 — adding or removing
  a white (resp. black) box creates no new addable white (resp. black) boxes; more precisely the
  addable and removable boxes of the given colour change only at the box itself.
* `ydSystem W`: Young diagrams with the boxes of colour `W` form a `BoxSystem`; `whiteSystem`,
  `blackSystem`, and `whiteSystemLen n` (partitions of length `≤ n`, boxes in the first `n` rows).
* `IsLima`: Lima partitions (all parts even and `λ_{2k+1} = λ_{2k+2}`, i.e. every value occurs an
  even number of times; `isLima_iff_printed` proves equivalence with the printed definition).
* `whiteSystem_crit_iff`, `whiteSystemLen_crit_iff`: a partition (of length `≤ n`) has no addable
  and no removable white box (in the first `n` rows) iff it is a Lima partition.
* `schurSign`: the sign `(-1)^{|λ/i| + i - 1}` of Proposition 3.11, and
  `squareCond_schurSign`: with these signs the white-box differential squares to zero.
-/

namespace OddMath.Frontier.EQLima

open Finset

/-! ### Colours and contents -/

/-- The content `ct(□) = j - i` of the cell in row `i`, column `j`. -/
def content (c : ℕ × ℕ) : ℤ := (c.2 : ℤ) - c.1

/-- A cell is *white* if its content is odd. -/
def IsWhite (c : ℕ × ℕ) : Prop := (c.1 + c.2) % 2 = 1

/-- A cell is *black* if its content is even. -/
def IsBlack (c : ℕ × ℕ) : Prop := (c.1 + c.2) % 2 = 0

instance : DecidablePred IsWhite := fun c => inferInstanceAs (Decidable ((c.1 + c.2) % 2 = 1))
instance : DecidablePred IsBlack := fun c => inferInstanceAs (Decidable ((c.1 + c.2) % 2 = 0))

theorem isWhite_iff_odd_content (c : ℕ × ℕ) : IsWhite c ↔ Odd (content c) := by
  have e : content c = ((c.1 + c.2 : ℕ) : ℤ) - 2 * c.1 := by unfold content; push_cast; ring
  rw [e, Int.odd_sub, Int.odd_coe_nat, Nat.odd_iff, IsWhite]
  simp

theorem isBlack_iff_even_content (c : ℕ × ℕ) : IsBlack c ↔ Even (content c) := by
  have e : content c = ((c.1 + c.2 : ℕ) : ℤ) - 2 * c.1 := by unfold content; push_cast; ring
  rw [e, Int.even_sub, Int.even_coe_nat, Nat.even_iff, IsBlack]
  simp

/-- Adjacent cells never have the same colour. -/
def Checker (W : ℕ × ℕ → Prop) : Prop :=
  ∀ i j, W (i, j) → ¬ W (i + 1, j) ∧ ¬ W (i, j + 1)

theorem checker_white : Checker IsWhite := by
  intro i j h; unfold IsWhite at *; constructor <;> omega

theorem checker_black : Checker IsBlack := by
  intro i j h; unfold IsBlack at *; constructor <;> omega

theorem Checker.and {W : ℕ × ℕ → Prop} (hW : Checker W) (Q : ℕ × ℕ → Prop) :
    Checker (fun c => W c ∧ Q c) :=
  fun i j h => ⟨fun h' => (hW i j h.1).1 h'.1, fun h' => (hW i j h.1).2 h'.1⟩

/-! ### Addable and removable boxes -/

/-- The cell `c` may be added to `μ`. -/
def Addable (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∉ μ ∧ (0 < c.1 → (c.1 - 1, c.2) ∈ μ) ∧ (0 < c.2 → (c.1, c.2 - 1) ∈ μ)

/-- The cell `c` may be removed from `μ`. -/
def Removable (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∈ μ ∧ (c.1 + 1, c.2) ∉ μ ∧ (c.1, c.2 + 1) ∉ μ

instance (μ : YoungDiagram) (c : ℕ × ℕ) : Decidable (Addable μ c) := by
  unfold Addable; infer_instance

instance (μ : YoungDiagram) (c : ℕ × ℕ) : Decidable (Removable μ c) := by
  unfold Removable; infer_instance

theorem isLowerSet_insert {μ : YoungDiagram} {c : ℕ × ℕ} (h : Addable μ c) :
    IsLowerSet (↑(insert c μ.cells) : Set (ℕ × ℕ)) := by
  intro a b hba ha
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, YoungDiagram.mem_cells]
    at ha ⊢
  rcases ha with rfl | ha
  · by_cases hb : b = a
    · exact Or.inl hb
    · right
      obtain ⟨b1, b2⟩ := b
      obtain ⟨a1, a2⟩ := a
      rw [Prod.mk_le_mk] at hba
      have hne : b1 < a1 ∨ b2 < a2 := by
        by_contra hc
        exact hb (Prod.ext (by simp only; omega) (by simp only; omega))
      rcases hne with h1 | h2
      · exact μ.up_left_mem (by omega) hba.2 (h.2.1 (by simp only; omega))
      · exact μ.up_left_mem hba.1 (by omega) (h.2.2 (by simp only; omega))
  · exact Or.inr (μ.isLowerSet hba ha)

theorem isLowerSet_erase {μ : YoungDiagram} {c : ℕ × ℕ} (h : Removable μ c) :
    IsLowerSet (↑(μ.cells.erase c) : Set (ℕ × ℕ)) := by
  intro a b hba ha
  simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, YoungDiagram.mem_cells,
    Set.mem_singleton_iff] at ha ⊢
  refine ⟨μ.isLowerSet hba ha.1, ?_⟩
  rintro rfl
  obtain ⟨b1, b2⟩ := b
  obtain ⟨a1, a2⟩ := a
  rw [Prod.mk_le_mk] at hba
  have hne : b1 < a1 ∨ b2 < a2 := by
    by_contra hc
    exact ha.2 (Prod.ext (by simp only; omega) (by simp only; omega))
  rcases hne with h1 | h2
  · exact h.2.1 (μ.up_left_mem (by omega) hba.2 ha.1)
  · exact h.2.2 (μ.up_left_mem hba.1 (by omega) ha.1)

/-- Add the cell `c` to `μ` (if it is addable; otherwise `μ`). -/
def addCell (μ : YoungDiagram) (c : ℕ × ℕ) : YoungDiagram :=
  if h : Addable μ c then ⟨insert c μ.cells, isLowerSet_insert h⟩ else μ

/-- Remove the cell `c` from `μ` (if it is removable; otherwise `μ`). -/
def remCell (μ : YoungDiagram) (c : ℕ × ℕ) : YoungDiagram :=
  if h : Removable μ c then ⟨μ.cells.erase c, isLowerSet_erase h⟩ else μ

theorem cells_addCell {μ : YoungDiagram} {c : ℕ × ℕ} (h : Addable μ c) :
    (addCell μ c).cells = insert c μ.cells := by
  simp [addCell, h]

theorem cells_remCell {μ : YoungDiagram} {c : ℕ × ℕ} (h : Removable μ c) :
    (remCell μ c).cells = μ.cells.erase c := by
  simp [remCell, h]

theorem mem_addCell {μ : YoungDiagram} {c : ℕ × ℕ} (h : Addable μ c) (x : ℕ × ℕ) :
    x ∈ addCell μ c ↔ x = c ∨ x ∈ μ := by
  rw [← YoungDiagram.mem_cells, cells_addCell h, Finset.mem_insert, YoungDiagram.mem_cells]

theorem mem_remCell {μ : YoungDiagram} {c : ℕ × ℕ} (h : Removable μ c) (x : ℕ × ℕ) :
    x ∈ remCell μ c ↔ x ≠ c ∧ x ∈ μ := by
  rw [← YoungDiagram.mem_cells, cells_remCell h, Finset.mem_erase, YoungDiagram.mem_cells]

theorem addable_bound {μ : YoungDiagram} {c : ℕ × ℕ} (h : Addable μ c) :
    c.1 < μ.colLen 0 + 1 ∧ c.2 < μ.rowLen 0 + 1 := by
  obtain ⟨c1, c2⟩ := c
  constructor
  · rcases Nat.eq_zero_or_pos c1 with h0 | h0
    · simp only at h0 ⊢; omega
    · have h1 := h.2.1 h0
      have h2 : (c1 - 1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) h1
      rw [YoungDiagram.mem_iff_lt_colLen] at h2
      simp only; omega
  · rcases Nat.eq_zero_or_pos c2 with h0 | h0
    · simp only at h0 ⊢; omega
    · have h1 := h.2.2 h0
      have h2 : (0, c2 - 1) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl h1
      rw [YoungDiagram.mem_iff_lt_rowLen] at h2
      simp only; omega

/-! ### Lemma A.1 -/

section LemmaA1

variable {W : ℕ × ℕ → Prop} (hW : Checker W) {μ : YoungDiagram} {b : ℕ × ℕ}
include hW

/-- Lemma A.1 (adding): if `b` is an addable box of colour `W`, the addable boxes of colour `W`
of `μ + b` are exactly those of `μ` other than `b`. -/
theorem addable_addCell_iff (hb : W b) (hab : Addable μ b) {c : ℕ × ℕ} (hc : W c) :
    Addable (addCell μ b) c ↔ Addable μ c ∧ c ≠ b := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨b1, b2⟩ := b
  simp only [Addable, mem_addCell hab, not_or] at hab ⊢
  constructor
  · rintro ⟨⟨hcb, hcμ⟩, hup, hleft⟩
    refine ⟨⟨hcμ, fun h0 => ?_, fun h0 => ?_⟩, hcb⟩
    · rcases hup h0 with h | h
      · exfalso
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        have := (hW _ _ hb).1
        rw [Nat.sub_add_cancel h0] at this
        exact this hc
      · exact h
    · rcases hleft h0 with h | h
      · exfalso
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        have := (hW _ _ hb).2
        rw [Nat.sub_add_cancel h0] at this
        exact this hc
      · exact h
  · rintro ⟨⟨hcμ, hup, hleft⟩, hcb⟩
    exact ⟨⟨hcb, hcμ⟩, fun h0 => Or.inr (hup h0), fun h0 => Or.inr (hleft h0)⟩

/-- Lemma A.1 (adding, removable boxes): if `b` is an addable box of colour `W`, the removable
boxes of colour `W` of `μ + b` are `b` and those of `μ`. -/
theorem removable_addCell_iff (hb : W b) (hab : Addable μ b) {c : ℕ × ℕ} (hc : W c) :
    Removable (addCell μ b) c ↔ c = b ∨ Removable μ c := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨b1, b2⟩ := b
  have hab' := hab
  simp only [Removable, mem_addCell hab, not_or] at hab' ⊢
  obtain ⟨hbμ, -, -⟩ := hab'
  constructor
  · rintro ⟨hcm, ⟨-, hd⟩, ⟨-, hr⟩⟩
    rcases hcm with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hd, hr⟩
  · rintro (h | ⟨hcμ, hd, hr⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      refine ⟨Or.inl rfl, ⟨fun e => by simp at e, fun hm => hbμ ?_⟩,
        ⟨fun e => by simp at e, fun hm => hbμ ?_⟩⟩
      · exact μ.up_left_mem (Nat.le_succ _) le_rfl hm
      · exact μ.up_left_mem le_rfl (Nat.le_succ _) hm
    · refine ⟨Or.inr hcμ, ⟨fun e => ?_, hd⟩, ⟨fun e => ?_, hr⟩⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        exact (hW _ _ hc).1 hb
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        exact (hW _ _ hc).2 hb

end LemmaA1

/-! ### Finite sets of addable and removable boxes -/

section Finsets

variable (W : ℕ × ℕ → Prop) [DecidablePred W]

/-- The addable boxes of colour `W`. -/
def addableCells (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  ((range (μ.colLen 0 + 1)) ×ˢ (range (μ.rowLen 0 + 1))).filter (fun c => W c ∧ Addable μ c)

/-- The removable boxes of colour `W`. -/
def removableCells (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  μ.cells.filter (fun c => W c ∧ Removable μ c)

variable {W}

theorem mem_addableCells {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ addableCells W μ ↔ W c ∧ Addable μ c := by
  unfold addableCells
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨addable_bound h.2, h⟩

theorem mem_removableCells {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ removableCells W μ ↔ W c ∧ Removable μ c := by
  unfold removableCells
  rw [Finset.mem_filter, YoungDiagram.mem_cells]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h.2.1, h⟩

end Finsets

/-! ### Young diagrams as a box system -/

/-- Young diagrams, with addable and removable boxes of colour `W` (a checkerboard colour), form a
box system. -/
def ydSystem (W : ℕ × ℕ → Prop) [DecidablePred W] (hW : Checker W) :
    BoxSystem YoungDiagram (ℕ × ℕ) where
  cells := YoungDiagram.cells
  cells_injective := fun _ _ h => YoungDiagram.ext h
  A := addableCells W
  R := removableCells W
  add := addCell
  rem := remCell
  notMem_cells_of_mem_A := by
    intro μ b h
    rw [YoungDiagram.mem_cells]
    exact (mem_addableCells.mp h).2.1
  cells_add := fun h => cells_addCell (mem_addableCells.mp h).2
  mem_cells_of_mem_R := fun h => (YoungDiagram.mem_cells _).mpr (mem_removableCells.mp h).2.1
  cells_rem := fun h => cells_remCell (mem_removableCells.mp h).2
  A_add := by
    intro μ b h
    obtain ⟨hb, hab⟩ := mem_addableCells.mp h
    ext c
    rw [Finset.mem_erase, mem_addableCells, mem_addableCells]
    constructor
    · rintro ⟨hc, hac⟩
      obtain ⟨h1, h2⟩ := (addable_addCell_iff hW hb hab hc).mp hac
      exact ⟨h2, hc, h1⟩
    · rintro ⟨h2, hc, h1⟩
      exact ⟨hc, (addable_addCell_iff hW hb hab hc).mpr ⟨h1, h2⟩⟩
  R_add := by
    intro μ b h
    obtain ⟨hb, hab⟩ := mem_addableCells.mp h
    ext c
    rw [Finset.mem_insert, mem_removableCells, mem_removableCells]
    constructor
    · rintro ⟨hc, hrc⟩
      rcases (removable_addCell_iff hW hb hab hc).mp hrc with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨hc, h'⟩
    · rintro (rfl | ⟨hc, h'⟩)
      · exact ⟨hb, (removable_addCell_iff hW hb hab hb).mpr (Or.inl rfl)⟩
      · exact ⟨hc, (removable_addCell_iff hW hb hab hc).mpr (Or.inr h')⟩
  mem_A_rem := by
    intro μ b h
    obtain ⟨hb, hrb⟩ := mem_removableCells.mp h
    rw [mem_addableCells]
    refine ⟨hb, ?_, ?_, ?_⟩
    · rw [mem_remCell hrb]; exact fun h' => h'.1 rfl
    · intro h0
      rw [mem_remCell hrb]
      refine ⟨fun e => ?_, μ.up_left_mem (Nat.sub_le _ _) le_rfl hrb.1⟩
      have := congrArg Prod.fst e
      simp only at this; omega
    · intro h0
      rw [mem_remCell hrb]
      refine ⟨fun e => ?_, μ.up_left_mem le_rfl (Nat.sub_le _ _) hrb.1⟩
      have := congrArg Prod.snd e
      simp only at this; omega

namespace BoxSystem

variable {P B : Type*} [DecidableEq B]

/-- Restriction of a box system to a class of shapes closed under adding addable boxes and
removing removable boxes. -/
def restrict (S : BoxSystem P B) (G : P → Prop)
    (hadd : ∀ p b, G p → b ∈ S.A p → G (S.add p b))
    (hrem : ∀ p b, G p → b ∈ S.R p → G (S.rem p b)) : BoxSystem {p // G p} B where
  cells p := S.cells p.1
  cells_injective := fun _ _ h => Subtype.ext (S.cells_injective h)
  A p := S.A p.1
  R p := S.R p.1
  add p b := if h : b ∈ S.A p.1 then ⟨S.add p.1 b, hadd _ _ p.2 h⟩ else p
  rem p b := if h : b ∈ S.R p.1 then ⟨S.rem p.1 b, hrem _ _ p.2 h⟩ else p
  notMem_cells_of_mem_A := fun h => S.notMem_cells_of_mem_A h
  cells_add := by intro p b h; simp only [h, ↓reduceDIte]; exact S.cells_add h
  mem_cells_of_mem_R := fun h => S.mem_cells_of_mem_R h
  cells_rem := by intro p b h; simp only [h, ↓reduceDIte]; exact S.cells_rem h
  A_add := by intro p b h; simp only [h, ↓reduceDIte]; exact S.A_add h
  R_add := by intro p b h; simp only [h, ↓reduceDIte]; exact S.R_add h
  mem_A_rem := by intro p b h; simp only [h, ↓reduceDIte]; exact S.mem_A_rem h

theorem restrict_add_val (S : BoxSystem P B) (G : P → Prop) (hadd hrem) {p : {p // G p}} {b : B}
    (h : b ∈ S.A p.1) : ((S.restrict G hadd hrem).add p b).1 = S.add p.1 b := by
  simp [restrict, h]

theorem restrict_crit_iff (S : BoxSystem P B) (G : P → Prop) (hadd hrem) (p : {p // G p}) :
    (S.restrict G hadd hrem).Crit p ↔ S.Crit p.1 := Iff.rfl

end BoxSystem

/-- White boxes: the box system underlying the differential on `OΛ` (Proposition 3.11). -/
def whiteSystem : BoxSystem YoungDiagram (ℕ × ℕ) := ydSystem IsWhite checker_white

/-- Black boxes (for the black case of Lemma A.1). -/
def blackSystem : BoxSystem YoungDiagram (ℕ × ℕ) := ydSystem IsBlack checker_black

/-- Partitions with at most `n` rows. -/
def LengthLE (n : ℕ) (μ : YoungDiagram) : Prop := ∀ c ∈ μ, c.1 < n

theorem lengthLE_iff (n : ℕ) (μ : YoungDiagram) : LengthLE n μ ↔ μ.colLen 0 ≤ n := by
  constructor
  · intro h
    by_contra hc
    have : (n, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    exact absurd (h _ this) (lt_irrefl n)
  · intro h c hc
    have : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) hc
    rw [YoungDiagram.mem_iff_lt_colLen] at this
    omega

/-- The box system underlying the differential on `OΛ_n`: partitions of length `≤ n`, white
boxes in the first `n` rows (a Schur function `s_μ` with `ℓ(μ) > n` vanishes in `OΛ_n`). -/
def whiteSystemLen (n : ℕ) : BoxSystem {μ : YoungDiagram // LengthLE n μ} (ℕ × ℕ) :=
  (ydSystem (fun c => IsWhite c ∧ c.1 < n) (checker_white.and _)).restrict (LengthLE n)
    (by
      intro μ b hμ hb c hc
      obtain ⟨⟨-, hbn⟩, hab⟩ := mem_addableCells.mp hb
      change c ∈ addCell μ b at hc
      rcases (mem_addCell hab c).mp hc with rfl | h
      · exact hbn
      · exact hμ c h)
    (by
      intro μ b hμ hb c hc
      obtain ⟨-, hrb⟩ := mem_removableCells.mp hb
      change c ∈ remCell μ b at hc
      exact hμ c ((mem_remCell hrb c).mp hc).2)

/-- **Lemma A.1** (Ellis–Qi).  Adding or removing a white (respectively black) box `b` to a
partition `μ` results in no new addable white (respectively black) boxes: the addable boxes of
that colour of `μ + b` are those of `μ` other than `b`, and those of `μ - b` are those of `μ`
together with `b` itself.  (The removable boxes behave dually.) -/
theorem lemma_A_1 (μ : YoungDiagram) (b : ℕ × ℕ) :
    (b ∈ addableCells IsWhite μ →
        addableCells IsWhite (addCell μ b) = (addableCells IsWhite μ).erase b) ∧
    (b ∈ removableCells IsWhite μ →
        addableCells IsWhite (remCell μ b) = insert b (addableCells IsWhite μ)) ∧
    (b ∈ addableCells IsBlack μ →
        addableCells IsBlack (addCell μ b) = (addableCells IsBlack μ).erase b) ∧
    (b ∈ removableCells IsBlack μ →
        addableCells IsBlack (remCell μ b) = insert b (addableCells IsBlack μ)) :=
  ⟨fun h => whiteSystem.A_add h, fun h => whiteSystem.A_rem h,
    fun h => blackSystem.A_add h, fun h => blackSystem.A_rem h⟩

/-! ### Lima partitions -/

/-- A *Lima partition*: all parts are even and rows come in equal pairs,
`μ_{2k} = μ_{2k+1}` (rows indexed from `0`); equivalently every value occurs an even number of
times (`isLima_iff_printed`). -/
def IsLima (μ : YoungDiagram) : Prop :=
  ∀ k, Even (μ.rowLen (2 * k)) ∧ μ.rowLen (2 * k + 1) = μ.rowLen (2 * k)

theorem count_map_range_succ (r : ℕ → ℕ) (v m : ℕ) :
    ((List.range (m + 1)).map r).count v =
      ((List.range m).map r).count v + if r m = v then 1 else 0 := by
  rw [List.range_succ, List.map_append, List.count_append]
  simp [List.count_singleton]

theorem even_count_of_pairs (r : ℕ → ℕ) (v k : ℕ) (h : ∀ j < k, r (2 * j + 1) = r (2 * j)) :
    Even (((List.range (2 * k)).map r).count v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, count_map_range_succ, count_map_range_succ,
      h k (by omega)]
    have := ih fun j hj => h j (by omega)
    split_ifs <;> simp_all

theorem count_map_range_stable (r : ℕ → ℕ) (v m : ℕ) (h : ∀ i, m ≤ i → r i ≠ v) :
    ∀ M, m ≤ M → ((List.range M).map r).count v = ((List.range m).map r).count v := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hM ih => simp only [count_map_range_succ, ih, h M hM, ↓reduceIte, add_zero]

/-- The printed definition (Ellis–Qi, A.1.2): all parts are even, and any particular value
occurs an even number of times. -/
theorem isLima_iff_printed (μ : YoungDiagram) :
    IsLima μ ↔ (∀ x ∈ μ.rowLens, Even x) ∧ ∀ v, Even (μ.rowLens.count v) := by
  have hrl : μ.rowLens = (List.range (μ.colLen 0)).map μ.rowLen := rfl
  have hpos : ∀ i, i < μ.colLen 0 ↔ 0 < μ.rowLen i := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun v => ?_⟩
    · rw [hrl, List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
      · subst hk; exact (h k).1
      · subst hk; rw [(h k).2]; exact (h k).1
    · rcases Nat.eq_zero_or_pos v with rfl | hv
      · rw [List.count_eq_zero_of_not_mem fun hm => lt_irrefl 0 (μ.pos_of_mem_rowLens 0 hm)]
        exact ⟨0, rfl⟩
      · rw [hrl, ← count_map_range_stable μ.rowLen v (μ.colLen 0) (fun i hi e => by
            have := (hpos i).not.mp (by omega); omega) (2 * μ.colLen 0) (by omega)]
        exact even_count_of_pairs _ _ _ fun j _ => (h j).2
  · rintro ⟨hev, hcount⟩
    have hpair : ∀ k, μ.rowLen (2 * k + 1) = μ.rowLen (2 * k) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        set v := μ.rowLen (2 * k)
        have hle : μ.rowLen (2 * k + 1) ≤ v := μ.rowLen_anti _ _ (by omega)
        by_contra hne
        have hlt : μ.rowLen (2 * k + 1) < v := lt_of_le_of_ne hle hne
        have hL : 2 * k + 1 ≤ μ.colLen 0 := (hpos (2 * k)).mpr (by omega)
        have hstable := count_map_range_stable μ.rowLen v (2 * k + 1) (fun i hi => by
          have := μ.rowLen_anti _ _ hi; omega) (μ.colLen 0) hL
        have h1 := even_count_of_pairs μ.rowLen v k (fun j hj => ih j hj)
        have h2 := hcount v
        rw [hrl, hstable, count_map_range_succ] at h2
        simp only [v, eq_self, ↓reduceIte] at h2
        exact (Nat.not_even_iff_odd.mpr (h1.add_one)) h2
    intro k
    refine ⟨?_, hpair k⟩
    rcases Nat.eq_zero_or_pos (μ.rowLen (2 * k)) with h0 | h0
    · rw [h0]; exact ⟨0, rfl⟩
    · exact hev _ (by rw [hrl, List.mem_map]; exact ⟨2 * k, List.mem_range.mpr ((hpos _).mpr h0), rfl⟩)

theorem addable_iff_rowLen (μ : YoungDiagram) (i j : ℕ) :
    Addable μ (i, j) ↔ j = μ.rowLen i ∧ (0 < i → μ.rowLen i < μ.rowLen (i - 1)) := by
  simp only [Addable, YoungDiagram.mem_iff_lt_rowLen, not_lt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hj : j = μ.rowLen i := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · omega
      · have := h3 h0; omega
    subst hj
    exact ⟨rfl, h2⟩
  · rintro ⟨rfl, h2⟩
    exact ⟨le_rfl, h2, fun h0 => by omega⟩

theorem removable_iff_rowLen (μ : YoungDiagram) (i j : ℕ) :
    Removable μ (i, j) ↔ j + 1 = μ.rowLen i ∧ μ.rowLen (i + 1) ≤ j := by
  simp only [Removable, YoungDiagram.mem_iff_lt_rowLen, not_lt]
  omega

theorem even_iff_mod (m : ℕ) : Even m ↔ m % 2 = 0 := Nat.even_iff

/-- A Lima partition has no addable and no removable white boxes. -/
theorem noWhite_of_isLima {μ : YoungDiagram} (h : IsLima μ) :
    (∀ c, IsWhite c → ¬ Addable μ c) ∧ (∀ c, IsWhite c → ¬ Removable μ c) := by
  constructor
  · rintro ⟨i, j⟩ hw ha
    rw [addable_iff_rowLen] at ha
    obtain ⟨rfl, hup⟩ := ha
    unfold IsWhite at hw
    simp only at hw
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
    · subst hk
      have := (even_iff_mod _).mp (h k).1
      omega
    · subst hk
      have := hup (by omega)
      rw [show 2 * k + 1 - 1 = 2 * k by omega, (h k).2] at this
      exact lt_irrefl _ this
  · rintro ⟨i, j⟩ hw hr
    rw [removable_iff_rowLen] at hr
    unfold IsWhite at hw
    simp only at hw
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
    · subst hk
      have := (h k).2
      omega
    · subst hk
      have h1 := (even_iff_mod _).mp (h k).1
      have h2 := (h k).2
      omega

/-- A partition of length `≤ n` with no addable white box in the first `n` rows and no removable
white box is a Lima partition (the induction in the proof of Proposition A.2). -/
theorem isLima_of_noWhite {μ : YoungDiagram} {n : ℕ} (hμ : LengthLE n μ)
    (hA : ∀ c, IsWhite c → c.1 < n → ¬ Addable μ c) (hR : ∀ c, IsWhite c → ¬ Removable μ c) :
    IsLima μ := by
  intro k
  induction k with
  | zero =>
    show Even (μ.rowLen 0) ∧ μ.rowLen 1 = μ.rowLen 0
    have hev : Even (μ.rowLen 0) := by
      rw [even_iff_mod]
      by_contra hodd
      have hpos : 0 < μ.rowLen 0 := by omega
      have h0 : (0, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hpos
      refine hA (0, μ.rowLen 0) (by unfold IsWhite; simp only; omega) (hμ (0, 0) h0) ?_
      rw [addable_iff_rowLen]
      exact ⟨rfl, fun h => absurd h (lt_irrefl 0)⟩
    refine ⟨hev, ?_⟩
    have hle := μ.rowLen_anti 0 1 (Nat.zero_le 1)
    by_contra hne
    have hlt : μ.rowLen 1 < μ.rowLen 0 := lt_of_le_of_ne hle hne
    have hev' := (even_iff_mod _).mp hev
    refine hR (0, μ.rowLen 0 - 1) (by unfold IsWhite; simp only; omega) ?_
    rw [removable_iff_rowLen, Nat.zero_add]
    omega
  | succ k ih =>
    show Even (μ.rowLen (2 * k + 2)) ∧ μ.rowLen (2 * k + 3) = μ.rowLen (2 * k + 2)
    obtain ⟨ihe, ihr⟩ := ih
    have ihe' := (even_iff_mod _).mp ihe
    have hev : Even (μ.rowLen (2 * k + 2)) := by
      rw [even_iff_mod]
      by_contra hodd
      have hpos : 0 < μ.rowLen (2 * k + 2) := by omega
      have h0 : (2 * k + 2, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hpos
      have hle := μ.rowLen_anti (2 * k + 1) (2 * k + 2) (by omega)
      refine hA (2 * k + 2, μ.rowLen (2 * k + 2)) (by unfold IsWhite; simp only; omega)
        (hμ (2 * k + 2, 0) h0) ?_
      rw [addable_iff_rowLen]
      refine ⟨rfl, fun _ => ?_⟩
      rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega]
      omega
    refine ⟨hev, ?_⟩
    have hle := μ.rowLen_anti (2 * k + 2) (2 * k + 3) (by omega)
    by_contra hne
    have hlt : μ.rowLen (2 * k + 3) < μ.rowLen (2 * k + 2) := lt_of_le_of_ne hle hne
    have hev' := (even_iff_mod _).mp hev
    refine hR (2 * k + 2, μ.rowLen (2 * k + 2) - 1) (by unfold IsWhite; simp only; omega) ?_
    rw [removable_iff_rowLen, show 2 * k + 2 + 1 = 2 * k + 3 by ring]
    omega

theorem whiteSystem_crit_iff_noWhite (μ : YoungDiagram) :
    whiteSystem.Crit μ ↔
      (∀ c, IsWhite c → ¬ Addable μ c) ∧ (∀ c, IsWhite c → ¬ Removable μ c) := by
  rw [BoxSystem.crit_iff]
  simp only [whiteSystem, ydSystem, Finset.eq_empty_iff_forall_notMem, mem_addableCells,
    mem_removableCells, not_and]

/-- **Proposition A.2 (1), combinatorial part.** A partition has no addable and no removable
white boxes iff it is a Lima partition. -/
theorem whiteSystem_crit_iff (μ : YoungDiagram) : whiteSystem.Crit μ ↔ IsLima μ := by
  rw [whiteSystem_crit_iff_noWhite]
  refine ⟨fun h => isLima_of_noWhite (n := μ.colLen 0 + 1) ?_ (fun c hc _ => h.1 c hc) h.2,
    noWhite_of_isLima⟩
  intro c hc
  have : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) hc
  rw [YoungDiagram.mem_iff_lt_colLen] at this
  omega

/-- **Proposition A.2 (2), combinatorial part.** A partition of length `≤ n` has no addable white
box in its first `n` rows and no removable white box iff it is a Lima partition. -/
theorem whiteSystemLen_crit_iff {n : ℕ} (μ : {μ : YoungDiagram // LengthLE n μ}) :
    (whiteSystemLen n).Crit μ ↔ IsLima μ.1 := by
  rw [whiteSystemLen, BoxSystem.restrict_crit_iff, BoxSystem.crit_iff]
  simp only [ydSystem, Finset.eq_empty_iff_forall_notMem, mem_addableCells,
    mem_removableCells, not_and]
  constructor
  · rintro ⟨hA, hR⟩
    refine isLima_of_noWhite μ.2 (fun c hc hn => hA c ⟨hc, hn⟩) (fun c hc hr => ?_)
    exact hR c ⟨hc, μ.2 c hr.1⟩ hr
  · intro h
    obtain ⟨hA, hR⟩ := noWhite_of_isLima h
    exact ⟨fun c hc => hA c hc.1, fun c hc => hR c hc.1⟩

/-! ### The signs of Proposition 3.11 -/

/-- The sign `(-1)^{|λ/i| + i - 1}` of Proposition 3.11 for adding the box `b` in row `i`
(`1`-based; `b.1 = i - 1` here): `|λ/i|` is the number of boxes in the rows above row `i`. -/
def schurSign {k : Type*} [CommRing k] (μ : YoungDiagram) (b : ℕ × ℕ) : kˣ :=
  (-1) ^ ((∑ r ∈ range b.1, μ.rowLen r) + b.1)

theorem rowLen_eq_of {ν : YoungDiagram} {r m : ℕ} (h : ∀ j, (r, j) ∈ ν ↔ j < m) :
    ν.rowLen r = m := by
  apply le_antisymm
  · by_contra hc
    exact lt_irrefl m ((h m).mp (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)))
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · omega
    · have := YoungDiagram.mem_iff_lt_rowLen.mp ((h (m - 1)).mpr (by omega))
      omega

theorem rowLen_addCell {μ : YoungDiagram} {b : ℕ × ℕ} (h : Addable μ b) (r : ℕ) :
    (addCell μ b).rowLen r = μ.rowLen r + if r = b.1 then 1 else 0 := by
  obtain ⟨i, j⟩ := b
  have hj := ((addable_iff_rowLen μ i j).mp h).1
  apply rowLen_eq_of
  intro j'
  rw [mem_addCell h, YoungDiagram.mem_iff_lt_rowLen, Prod.mk.injEq]
  split_ifs with hr
  · subst hr; omega
  · simp only [hr, false_and, false_or]; omega

theorem schurSign_addCell {k : Type*} [CommRing k] {μ : YoungDiagram} {b b' : ℕ × ℕ}
    (h : Addable μ b) :
    (schurSign (addCell μ b) b' : kˣ) =
      (-1) ^ ((∑ r ∈ range b'.1, μ.rowLen r) + b'.1 + if b.1 < b'.1 then 1 else 0) := by
  unfold schurSign
  congr 1
  simp only [rowLen_addCell h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  ring

/-- With the signs of Proposition 3.11 every square anticommutes, for any checkerboard colour
(in particular for white boxes, in `OΛ` and in `OΛ_n`). -/
theorem squareCond_schurSign {k : Type*} [CommRing k] {W : ℕ × ℕ → Prop} [DecidablePred W]
    (hW : Checker W) :
    (ydSystem W hW).SquareCond (fun μ b => (schurSign μ b : kˣ)) := by
  intro μ b b' hb hb' hne
  obtain ⟨-, hab⟩ := mem_addableCells.mp hb
  obtain ⟨-, hab'⟩ := mem_addableCells.mp hb'
  change ((schurSign μ b : kˣ) : k) * (schurSign (addCell μ b) b' : kˣ) +
    ((schurSign μ b' : kˣ) : k) * (schurSign (addCell μ b') b : kˣ) = 0
  rw [schurSign_addCell hab, schurSign_addCell hab']
  unfold schurSign
  have hrow : b.1 ≠ b'.1 := by
    intro e
    obtain ⟨i, j⟩ := b
    obtain ⟨i', j'⟩ := b'
    simp only at e
    subst e
    have h1 := ((addable_iff_rowLen μ i j).mp hab).1
    have h2 := ((addable_iff_rowLen μ i j').mp hab').1
    exact hne (Prod.ext rfl (h1.trans h2.symm))
  set E := (∑ r ∈ range b.1, μ.rowLen r) + b.1
  set E' := (∑ r ∈ range b'.1, μ.rowLen r) + b'.1
  rcases Nat.lt_or_gt_of_ne hrow with hlt | hlt
  · have h2 : ¬ b'.1 < b.1 := by omega
    simp only [hlt, h2, ↓reduceIte, add_zero]
    push_cast
    ring
  · have h2 : ¬ b.1 < b'.1 := by omega
    simp only [hlt, h2, ↓reduceIte, add_zero]
    push_cast
    ring

end OddMath.Frontier.EQLima
