import OddMath.Frontier.EKDualBases
import OddMath.Frontier.KostkaModuleInversion
import OddMath.Frontier.EKDualBasesControls

/-! PRE-production controls for EK1107.5610v2 §3.3, Cor 3.8–3.9 (printed pp27–29).

Compiled BEFORE `EKSchurOrthonormal`; nothing here mentions the production `s_λ`.

* Two exact evaluation bridges, proved for ALL inputs (no sampled enumeration):
  `Mh_eq_PL` (the source M′ = (h,h) Gram entry, via Prop 3.1's signed natural-matrix
  sum, row-peeling recursion) and `signedKostka_eq_KW` (the source (3.7) odd Kostka
  number, via a bijection of the actual fixed-content tableau fibre with filtered
  permutations of the content word, preserving `wr(T)` and hence `sign(T)`).
* Exhaustive degree-d shape lists for d ≤ 4, the literal (3.9) matrix identity for
  d = 0,…,4 (hypothesis side, sign (-1)^{λ₂+λ₄+…}), negative controls.
* Degree 1–3 hand fixtures for s_λ in the h-basis (predicted by hand from (3.6) with
  hand odd Kostka numbers), their (3.6) relations and their actual Gram matrices in Q,
  including norms +1 for s_(2) and -1 for s_(1,1) and the sign (-1)^{C(λᵀ,2)} at λ=(1,1).
-/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace OddMath.Frontier.EKSchurOrthonormalControls
open EKPairingMatrices EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases
open TableauDominance TableauContent TableauSign TableauRowWord
open EKPartitionSpanning (hPartition)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## Literal source statistics -/

/-- `λ₂ + λ₄ + λ₆ + …` of the partition list `(λ₁, λ₂, …)` (0-based odd positions). -/
def evenParts (L : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range L.length, if i % 2 = 1 then L.getD i 0 else 0

/-- `C(λᵀ, 2) = Σ_j C(λᵀ_j, 2)`, with `λᵀ` Mathlib's actual transpose diagram. -/
def transposeChoose (μ : YoungDiagram) : ℕ :=
  (μ.transpose.rowLens.map (fun a => a.choose 2)).sum

/-! ## Bridge A: the source M′ entries by exact row-peeling recursion -/

/-- Peel the LAST row platform: Prop 2.2-type convolution with a single row. -/
def P : (r : ℕ) → (Fin r → ℕ) → {c : ℕ} → (Fin c → ℕ) → ℤ
  | 0, _, _, α => if ∀ j, α j = 0 then 1 else 0
  | r+1, β, _, α => ∑ u : Splits α, (-1 : ℤ) ^ crossCols (upper u) (lower u) *
      P r (fun i => β (Fin.castSucc i)) (upper u) *
      (if ∑ j, lower u j = β (Fin.last r) then 1 else 0)

def PL (L M : List ℕ) : ℤ := P L.length (fun i => L.get i) (c := M.length) (fun j => M.get j)

private theorem single_row {c : ℕ} (b : ℕ) (α : Fin c → ℕ) :
    pairing (fun _ : Fin 1 => b) α = if ∑ j, α j = b then 1 else 0 := by
  by_cases h : ∑ j, α j = b
  · rw [if_pos h, ← h]; exact pairing_single_row α
  · rw [if_neg h]
    apply pairing_degree_mismatch
    simpa using fun h' => h h'.symm

theorem pairing_eq_P : ∀ (r : ℕ) (β : Fin r → ℕ) {c : ℕ} (α : Fin c → ℕ),
    pairing β α = P r β α
  | 0, β, c, α => by
    simp only [P]
    by_cases h : ∀ j, α j = 0
    · rw [if_pos h]
      have hα : α = fun _ => 0 := funext h
      have hβ : β = fun _ => 0 := funext (fun i => Fin.elim0 i)
      subst hα; subst hβ
      exact pairing_zero_zero 0 c
    · rw [if_neg h]
      push_neg at h
      obtain ⟨j, hj⟩ := h
      apply pairing_degree_mismatch
      have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (α k))
        (Finset.mem_univ j)
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      omega
  | r+1, β, c, α => by
    have hβ : β = Fin.addCases (fun i : Fin r => β (Fin.castSucc i))
        (fun _ : Fin 1 => β (Fin.last r)) := by
      funext i
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · rw [Fin.addCases_left]; rfl
      · rw [Fin.addCases_right]
        congr 1
        apply Fin.ext
        have := k.isLt
        simp only [Fin.coe_natAdd, Fin.val_last]
        omega
    conv_lhs => rw [hβ]
    rw [pairing_convolution]
    simp only [P]
    apply Finset.sum_congr rfl
    intro u _
    rw [pairing_eq_P r _ (upper u), single_row]

/-- Pure reindexing along equal lengths changes nothing. -/
private theorem pairing_reindex {r r' c c' : ℕ} (hr : r = r') (hc : c = c')
    (β : Fin r' → ℕ) (α : Fin c' → ℕ) :
    pairing (fun i : Fin r => β (Fin.cast hr i)) (fun j : Fin c => α (Fin.cast hc j)) =
      pairing β α := by
  subst hr; subst hc; rfl

theorem pairing_rows (ν μ : YoungDiagram) :
    pairing (EKSemiorthogonality.rows ν) (EKSemiorthogonality.rows μ) =
      PL ν.rowLens μ.rowLens := by
  unfold PL
  rw [← pairing_eq_P, ← pairing_reindex (YoungDiagram.length_rowLens (μ := ν)).symm
    (YoungDiagram.length_rowLens (μ := μ)).symm]
  congr 1 <;> funext i <;> simp [EKSemiorthogonality.rows, YoungDiagram.get_rowLens]

/-- Every source M′ = (h,h) entry, any degree, as the computable recursion. -/
theorem Mh_eq_PL (d : ℕ) (ν μ : DegreeShape d) : Mh d ν μ = PL ν.val.rowLens μ.val.rowLens := by
  rw [proposition_3_1_Mh, ← pairing_rows]
  rfl

/-! ## Bridge B: the (3.7) odd Kostka number by an exact fibre bijection -/

def validFill (cs : List (ℕ × ℕ)) (w : List ℕ) : Prop :=
  w.length = cs.length ∧ ∀ x ∈ cs.zip w, 0 < x.2 ∧ ∀ y ∈ cs.zip w,
    (x.1.1 = y.1.1 → x.1.2 < y.1.2 → x.2 ≤ y.2) ∧ (x.1.2 = y.1.2 → x.1.1 < y.1.1 → x.2 < y.2)

instance (cs : List (ℕ × ℕ)) (w : List ℕ) : Decidable (validFill cs w) := by
  unfold validFill; infer_instance

/-- Candidate row words: distinct rearrangements of the content word, filtered. -/
def words (cs : List (ℕ × ℕ)) (cw : List ℕ) : Finset (List ℕ) :=
  cw.permutations'.toFinset.filter (fun w => validFill cs w)

/-- `sign(T_λ) · Σ_T sign(T)`, with `sign = (-1)^{inversions of the row word}`. -/
def KW (cs : List (ℕ × ℕ)) (cw : List ℕ) : ℤ :=
  (-1 : ℤ) ^ inversions (cs.map (fun p => p.1 + 1)) *
    ∑ w ∈ words cs cw, (-1 : ℤ) ^ inversions w

/-- Bottom-to-top, left-to-right cells of the diagram with row lengths `L`. -/
def cellsOf (L : List ℕ) : List (ℕ × ℕ) :=
  ((List.range L.length).reverse).flatMap (fun i => (List.range (L.getD i 0)).map (fun j => (i, j)))

def KL (L M : List ℕ) : ℤ := KW (cellsOf L) ((cellsOf M).map (fun p => p.1 + 1))

private def find : List (ℕ × ℕ) → List ℕ → ℕ × ℕ → ℕ
  | c :: cs, a :: w, p => if p = c then a else find cs w p
  | _, _, _ => 0

private theorem find_mem_zip : ∀ (cs : List (ℕ × ℕ)) (w : List ℕ) (p : ℕ × ℕ),
    w.length = cs.length → p ∈ cs → (p, find cs w p) ∈ cs.zip w
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, hl, _ => by simp at hl
  | c :: cs, a :: w, p, hl, hp => by
    by_cases hpc : p = c
    · subst hpc; simp [find]
    · have hp' : p ∈ cs := by simpa [hpc] using hp
      have := find_mem_zip cs w p (by simpa using hl) hp'
      simp [find, hpc, this]

private theorem map_find : ∀ (cs : List (ℕ × ℕ)) (w : List ℕ),
    cs.Nodup → w.length = cs.length → cs.map (find cs w) = w
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | c :: cs, a :: w, hn, hl => by
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, find, if_pos rfl]
    congr 1
    conv_rhs => rw [← map_find cs w hn.2 (by simpa using hl)]
    apply List.map_congr_left
    intro p hp
    have : p ≠ c := fun h => hn.1 (h ▸ hp)
    simp [find, this]

private theorem mem_zip_map : ∀ (cs : List (ℕ × ℕ)) (e : ℕ × ℕ → ℕ) (x : (ℕ × ℕ) × ℕ),
    x ∈ cs.zip (cs.map e) → x.1 ∈ cs ∧ x.2 = e x.1
  | [], _, _, h => by simp at h
  | c :: cs, e, x, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := mem_zip_map cs e x h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-- The tableau with prescribed row word (valid fillings only). -/
private def ofWord (μ : YoungDiagram) (w : List ℕ) (hv : validFill (rowCells μ) w) :
    PositiveTableau μ where
  entry i j := if (i, j) ∈ μ then find (rowCells μ) w (i, j) else 0
  row_weak' := by
    intro i j1 j2 hj hp
    have hp1 : (i, j1) ∈ μ := μ.up_left_mem le_rfl hj.le hp
    simp only [if_pos hp1, if_pos hp]
    have m1 := find_mem_zip (rowCells μ) w (i, j1) hv.1 ((mem_rowCells μ _).2 hp1)
    have m2 := find_mem_zip (rowCells μ) w (i, j2) hv.1 ((mem_rowCells μ _).2 hp)
    exact ((hv.2 _ m1).2 _ m2).1 rfl hj
  col_strict' := by
    intro i1 i2 j hi hp
    have hp1 : (i1, j) ∈ μ := μ.up_left_mem hi.le le_rfl hp
    simp only [if_pos hp1, if_pos hp]
    have m1 := find_mem_zip (rowCells μ) w (i1, j) hv.1 ((mem_rowCells μ _).2 hp1)
    have m2 := find_mem_zip (rowCells μ) w (i2, j) hv.1 ((mem_rowCells μ _).2 hp)
    exact ((hv.2 _ m1).2 _ m2).2 rfl hi
  zeros' := by
    intro i j hp
    exact if_neg hp
  positive := by
    intro i j hp
    simp only [if_pos hp]
    exact (hv.2 _ (find_mem_zip (rowCells μ) w (i, j) hv.1 ((mem_rowCells μ _).2 hp))).1

private theorem rowWord_ofWord (μ : YoungDiagram) (w : List ℕ) (hv : validFill (rowCells μ) w) :
    rowWord (ofWord μ w hv) = w := by
  unfold rowWord
  conv_rhs => rw [← map_find (rowCells μ) w (rowCells_nodup μ) hv.1]
  apply List.map_congr_left
  intro p hp
  have hp' : (p.1, p.2) ∈ μ := by simpa using (mem_rowCells μ p).1 hp
  change (if (p.1, p.2) ∈ μ then find (rowCells μ) w (p.1, p.2) else 0) = _
  rw [if_pos hp']

private theorem canonical_rowWord (μ : YoungDiagram) :
    rowWord (canonicalTableau μ) = (rowCells μ).map (fun p => p.1 + 1) := by
  unfold rowWord
  apply List.map_congr_left
  intro p hp
  exact canonical_entry ((mem_rowCells μ p).1 hp)

private theorem rowWord_valid (μ : YoungDiagram) (T : PositiveTableau μ) :
    validFill (rowCells μ) (rowWord T) := by
  refine ⟨by simp [rowWord], ?_⟩
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_zip_map _ _ x hx
  have hxμ : (x.1.1, x.1.2) ∈ μ := by simpa using (mem_rowCells μ _).1 hx1
  refine ⟨by rw [hx2]; exact T.positive hxμ, ?_⟩
  intro y hy
  obtain ⟨hy1, hy2⟩ := mem_zip_map _ _ y hy
  have hyμ : (y.1.1, y.1.2) ∈ μ := by simpa using (mem_rowCells μ _).1 hy1
  rw [hx2, hy2]
  constructor
  · intro h1 h2
    have := T.row_weak' (i := x.1.1) h2 (by rw [h1]; exact hyμ)
    rw [h1] at this ⊢
    exact this
  · intro h1 h2
    have := T.col_strict' (j := x.1.2) h2 (by rw [h1]; exact hyμ)
    rw [h1] at this ⊢
    exact this

/-- (3.7) for ALL shapes: the actual fibre sum equals the filtered-word sum. -/
theorem signedKostka_eq_KW (lam mu : YoungDiagram) :
    signedKostka lam mu = KW (rowCells lam) ((rowCells mu).map (fun p => p.1 + 1)) := by
  classical
  unfold signedKostka KW
  congr 1
  · unfold tableauSign
    rw [canonical_rowWord]
  · have hcount (k : ℕ) : ((rowCells mu).map (fun p => p.1 + 1)).count k = shapeContent mu k := by
      rw [← canonical_rowWord, rowWord_count, content_canonical]
    apply Finset.sum_bij (fun T _ => rowWord T)
    · intro T hT
      simp only [words, Finset.mem_filter, List.mem_toFinset, List.mem_permutations']
      refine ⟨List.perm_iff_count.2 (fun k => ?_), rowWord_valid lam T⟩
      rw [rowWord_count, (mem_tableauxOfContent T _).1 hT, hcount]
    · intro T₁ _ T₂ _ h
      apply ext_cells
      intro p hp
      have := (List.map_inj_left.1 h) p ((mem_rowCells lam p).2 hp)
      exact this
    · intro w hw
      simp only [words, Finset.mem_filter, List.mem_toFinset, List.mem_permutations'] at hw
      refine ⟨ofWord lam w hw.2, ?_, rowWord_ofWord lam w hw.2⟩
      rw [mem_tableauxOfContent]
      ext k
      rw [← rowWord_count, rowWord_ofWord, hw.1.count_eq, hcount]
    · intro T _
      rfl

/-! ## Exhaustive shapes, d ≤ 4 -/

instance : IsAntisymm (ℕ × ℕ) RowLE := ⟨by
  intro a b h1 h2
  unfold RowLE at h1 h2
  exact Prod.ext (by omega) (by omega)⟩

theorem rowCells_eq_of (μ : YoungDiagram) (l : List (ℕ × ℕ)) (hs : l.Sorted RowLE)
    (hn : l.Nodup) (hc : l.toFinset = μ.cells) : rowCells μ = l := by
  apply List.eq_of_perm_of_sorted _ (rowCells_sorted μ) hs
  apply List.perm_of_nodup_nodup_toFinset_eq (rowCells_nodup μ) hn
  ext p
  simp [hc]

/-! ## Exhaustive shapes, d ≤ 4 (literal Young diagrams from row lengths) -/

def sh0 : DegreeShape 0 :=
  ⟨YoungDiagram.ofRowLens [] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh0_rows : sh0.val.rowLens = [] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh0_cells : rowCells sh0.val = [] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh0_transpose : sh0.val.transpose.rowLens = [] := by
  have h : sh0.val.transpose = YoungDiagram.ofRowLens [] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh0_signs : transposeChoose sh0.val = 0 ∧ evenParts sh0.val.rowLens = 0 := by
  unfold transposeChoose; rw [sh0_transpose, sh0_rows]; decide

def sh1 : DegreeShape 1 :=
  ⟨YoungDiagram.ofRowLens [1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh1_rows : sh1.val.rowLens = [1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh1_cells : rowCells sh1.val = [(0,0)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh1_transpose : sh1.val.transpose.rowLens = [1] := by
  have h : sh1.val.transpose = YoungDiagram.ofRowLens [1] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh1_signs : transposeChoose sh1.val = 0 ∧ evenParts sh1.val.rowLens = 0 := by
  unfold transposeChoose; rw [sh1_transpose, sh1_rows]; decide

def sh2 : DegreeShape 2 :=
  ⟨YoungDiagram.ofRowLens [2] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh2_rows : sh2.val.rowLens = [2] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh2_cells : rowCells sh2.val = [(0,0), (0,1)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh2_transpose : sh2.val.transpose.rowLens = [1,1] := by
  have h : sh2.val.transpose = YoungDiagram.ofRowLens [1,1] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh2_signs : transposeChoose sh2.val = 0 ∧ evenParts sh2.val.rowLens = 0 := by
  unfold transposeChoose; rw [sh2_transpose, sh2_rows]; decide

def sh11 : DegreeShape 2 :=
  ⟨YoungDiagram.ofRowLens [1,1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh11_rows : sh11.val.rowLens = [1,1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh11_cells : rowCells sh11.val = [(1,0), (0,0)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh11_transpose : sh11.val.transpose.rowLens = [2] := by
  have h : sh11.val.transpose = YoungDiagram.ofRowLens [2] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh11_signs : transposeChoose sh11.val = 1 ∧ evenParts sh11.val.rowLens = 1 := by
  unfold transposeChoose; rw [sh11_transpose, sh11_rows]; decide

def sh3 : DegreeShape 3 :=
  ⟨YoungDiagram.ofRowLens [3] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh3_rows : sh3.val.rowLens = [3] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh3_cells : rowCells sh3.val = [(0,0), (0,1), (0,2)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh3_transpose : sh3.val.transpose.rowLens = [1,1,1] := by
  have h : sh3.val.transpose = YoungDiagram.ofRowLens [1,1,1] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh3_signs : transposeChoose sh3.val = 0 ∧ evenParts sh3.val.rowLens = 0 := by
  unfold transposeChoose; rw [sh3_transpose, sh3_rows]; decide

def sh21 : DegreeShape 3 :=
  ⟨YoungDiagram.ofRowLens [2,1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh21_rows : sh21.val.rowLens = [2,1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh21_cells : rowCells sh21.val = [(1,0), (0,0), (0,1)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh21_transpose : sh21.val.transpose.rowLens = [2,1] := by
  have h : sh21.val.transpose = YoungDiagram.ofRowLens [2,1] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh21_signs : transposeChoose sh21.val = 1 ∧ evenParts sh21.val.rowLens = 1 := by
  unfold transposeChoose; rw [sh21_transpose, sh21_rows]; decide

def sh111 : DegreeShape 3 :=
  ⟨YoungDiagram.ofRowLens [1,1,1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh111_rows : sh111.val.rowLens = [1,1,1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh111_cells : rowCells sh111.val = [(2,0), (1,0), (0,0)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh111_transpose : sh111.val.transpose.rowLens = [3] := by
  have h : sh111.val.transpose = YoungDiagram.ofRowLens [3] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh111_signs : transposeChoose sh111.val = 3 ∧ evenParts sh111.val.rowLens = 1 := by
  unfold transposeChoose; rw [sh111_transpose, sh111_rows]; decide

def sh4 : DegreeShape 4 :=
  ⟨YoungDiagram.ofRowLens [4] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh4_rows : sh4.val.rowLens = [4] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh4_cells : rowCells sh4.val = [(0,0), (0,1), (0,2), (0,3)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh4_transpose : sh4.val.transpose.rowLens = [1,1,1,1] := by
  have h : sh4.val.transpose = YoungDiagram.ofRowLens [1,1,1,1] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh4_signs : transposeChoose sh4.val = 0 ∧ evenParts sh4.val.rowLens = 0 := by
  unfold transposeChoose; rw [sh4_transpose, sh4_rows]; decide

def sh31 : DegreeShape 4 :=
  ⟨YoungDiagram.ofRowLens [3,1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh31_rows : sh31.val.rowLens = [3,1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh31_cells : rowCells sh31.val = [(1,0), (0,0), (0,1), (0,2)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh31_transpose : sh31.val.transpose.rowLens = [2,1,1] := by
  have h : sh31.val.transpose = YoungDiagram.ofRowLens [2,1,1] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh31_signs : transposeChoose sh31.val = 1 ∧ evenParts sh31.val.rowLens = 1 := by
  unfold transposeChoose; rw [sh31_transpose, sh31_rows]; decide

def sh22 : DegreeShape 4 :=
  ⟨YoungDiagram.ofRowLens [2,2] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh22_rows : sh22.val.rowLens = [2,2] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh22_cells : rowCells sh22.val = [(1,0), (1,1), (0,0), (0,1)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh22_transpose : sh22.val.transpose.rowLens = [2,2] := by
  have h : sh22.val.transpose = YoungDiagram.ofRowLens [2,2] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh22_signs : transposeChoose sh22.val = 2 ∧ evenParts sh22.val.rowLens = 2 := by
  unfold transposeChoose; rw [sh22_transpose, sh22_rows]; decide

def sh211 : DegreeShape 4 :=
  ⟨YoungDiagram.ofRowLens [2,1,1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh211_rows : sh211.val.rowLens = [2,1,1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh211_cells : rowCells sh211.val = [(2,0), (1,0), (0,0), (0,1)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh211_transpose : sh211.val.transpose.rowLens = [3,1] := by
  have h : sh211.val.transpose = YoungDiagram.ofRowLens [3,1] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh211_signs : transposeChoose sh211.val = 3 ∧ evenParts sh211.val.rowLens = 1 := by
  unfold transposeChoose; rw [sh211_transpose, sh211_rows]; decide

def sh1111 : DegreeShape 4 :=
  ⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
@[simp] theorem sh1111_rows : sh1111.val.rowLens = [1,1,1,1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh1111_cells : rowCells sh1111.val = [(3,0), (2,0), (1,0), (0,0)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem sh1111_transpose : sh1111.val.transpose.rowLens = [4] := by
  have h : sh1111.val.transpose = YoungDiagram.ofRowLens [4] (by decide) :=
    YoungDiagram.ext (by decide)
  rw [h]; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem sh1111_signs : transposeChoose sh1111.val = 6 ∧ evenParts sh1111.val.rowLens = 2 := by
  unfold transposeChoose; rw [sh1111_transpose, sh1111_rows]; decide

/-! ## Exact tables (all ordered pairs, d ≤ 4) -/

theorem K_0_0 : signedKostka sh0.val sh0.val = 1 := by
  rw [signedKostka_eq_KW, sh0_cells]; decide
theorem Mh_0_0 : Mh 0 sh0 sh0 = 1 := by
  rw [Mh_eq_PL, sh0_rows]; decide

theorem K_1_1 : signedKostka sh1.val sh1.val = 1 := by
  rw [signedKostka_eq_KW, sh1_cells]; decide
theorem Mh_1_1 : Mh 1 sh1 sh1 = 1 := by
  rw [Mh_eq_PL, sh1_rows]; decide

theorem K_2_2 : signedKostka sh2.val sh2.val = 1 := by
  rw [signedKostka_eq_KW, sh2_cells]; decide
theorem K_2_11 : signedKostka sh2.val sh11.val = 1 := by
  rw [signedKostka_eq_KW, sh2_cells, sh11_cells]; decide
theorem K_11_2 : signedKostka sh11.val sh2.val = 0 := by
  rw [signedKostka_eq_KW, sh11_cells, sh2_cells]; decide
theorem K_11_11 : signedKostka sh11.val sh11.val = 1 := by
  rw [signedKostka_eq_KW, sh11_cells]; decide
theorem Mh_2_2 : Mh 2 sh2 sh2 = 1 := by
  rw [Mh_eq_PL, sh2_rows]; decide
theorem Mh_2_11 : Mh 2 sh2 sh11 = 1 := by
  rw [Mh_eq_PL, sh2_rows, sh11_rows]; decide
theorem Mh_11_2 : Mh 2 sh11 sh2 = 1 := by
  rw [Mh_eq_PL, sh11_rows, sh2_rows]; decide
theorem Mh_11_11 : Mh 2 sh11 sh11 = 0 := by
  rw [Mh_eq_PL, sh11_rows]; decide

theorem K_3_3 : signedKostka sh3.val sh3.val = 1 := by
  rw [signedKostka_eq_KW, sh3_cells]; decide
theorem K_3_21 : signedKostka sh3.val sh21.val = 1 := by
  rw [signedKostka_eq_KW, sh3_cells, sh21_cells]; decide
theorem K_3_111 : signedKostka sh3.val sh111.val = 1 := by
  rw [signedKostka_eq_KW, sh3_cells, sh111_cells]; decide
theorem K_21_3 : signedKostka sh21.val sh3.val = 0 := by
  rw [signedKostka_eq_KW, sh21_cells, sh3_cells]; decide
theorem K_21_21 : signedKostka sh21.val sh21.val = 1 := by
  rw [signedKostka_eq_KW, sh21_cells]; decide
theorem K_21_111 : signedKostka sh21.val sh111.val = 0 := by
  rw [signedKostka_eq_KW, sh21_cells, sh111_cells]; decide
theorem K_111_3 : signedKostka sh111.val sh3.val = 0 := by
  rw [signedKostka_eq_KW, sh111_cells, sh3_cells]; decide
theorem K_111_21 : signedKostka sh111.val sh21.val = 0 := by
  rw [signedKostka_eq_KW, sh111_cells, sh21_cells]; decide
theorem K_111_111 : signedKostka sh111.val sh111.val = 1 := by
  rw [signedKostka_eq_KW, sh111_cells]; decide
theorem Mh_3_3 : Mh 3 sh3 sh3 = 1 := by
  rw [Mh_eq_PL, sh3_rows]; decide
theorem Mh_3_21 : Mh 3 sh3 sh21 = 1 := by
  rw [Mh_eq_PL, sh3_rows, sh21_rows]; decide
theorem Mh_3_111 : Mh 3 sh3 sh111 = 1 := by
  rw [Mh_eq_PL, sh3_rows, sh111_rows]; decide
theorem Mh_21_3 : Mh 3 sh21 sh3 = 1 := by
  rw [Mh_eq_PL, sh21_rows, sh3_rows]; decide
theorem Mh_21_21 : Mh 3 sh21 sh21 = 0 := by
  rw [Mh_eq_PL, sh21_rows]; decide
theorem Mh_21_111 : Mh 3 sh21 sh111 = 1 := by
  rw [Mh_eq_PL, sh21_rows, sh111_rows]; decide
theorem Mh_111_3 : Mh 3 sh111 sh3 = 1 := by
  rw [Mh_eq_PL, sh111_rows, sh3_rows]; decide
theorem Mh_111_21 : Mh 3 sh111 sh21 = 1 := by
  rw [Mh_eq_PL, sh111_rows, sh21_rows]; decide
theorem Mh_111_111 : Mh 3 sh111 sh111 = 0 := by
  rw [Mh_eq_PL, sh111_rows]; decide

theorem K_4_4 : signedKostka sh4.val sh4.val = 1 := by
  rw [signedKostka_eq_KW, sh4_cells]; decide
theorem K_4_31 : signedKostka sh4.val sh31.val = 1 := by
  rw [signedKostka_eq_KW, sh4_cells, sh31_cells]; decide
theorem K_4_22 : signedKostka sh4.val sh22.val = 1 := by
  rw [signedKostka_eq_KW, sh4_cells, sh22_cells]; decide
theorem K_4_211 : signedKostka sh4.val sh211.val = 1 := by
  rw [signedKostka_eq_KW, sh4_cells, sh211_cells]; decide
theorem K_4_1111 : signedKostka sh4.val sh1111.val = 1 := by
  rw [signedKostka_eq_KW, sh4_cells, sh1111_cells]; decide
theorem K_31_4 : signedKostka sh31.val sh4.val = 0 := by
  rw [signedKostka_eq_KW, sh31_cells, sh4_cells]; decide
theorem K_31_31 : signedKostka sh31.val sh31.val = 1 := by
  rw [signedKostka_eq_KW, sh31_cells]; decide
theorem K_31_22 : signedKostka sh31.val sh22.val = -1 := by
  rw [signedKostka_eq_KW, sh31_cells, sh22_cells]; decide
theorem K_31_211 : signedKostka sh31.val sh211.val = 0 := by
  rw [signedKostka_eq_KW, sh31_cells, sh211_cells]; decide
theorem K_31_1111 : signedKostka sh31.val sh1111.val = 1 := by
  rw [signedKostka_eq_KW, sh31_cells, sh1111_cells]; decide
theorem K_22_4 : signedKostka sh22.val sh4.val = 0 := by
  rw [signedKostka_eq_KW, sh22_cells, sh4_cells]; decide
theorem K_22_31 : signedKostka sh22.val sh31.val = 0 := by
  rw [signedKostka_eq_KW, sh22_cells, sh31_cells]; decide
theorem K_22_22 : signedKostka sh22.val sh22.val = 1 := by
  rw [signedKostka_eq_KW, sh22_cells]; decide
theorem K_22_211 : signedKostka sh22.val sh211.val = 1 := by
  rw [signedKostka_eq_KW, sh22_cells, sh211_cells]; decide
theorem K_22_1111 : signedKostka sh22.val sh1111.val = 0 := by
  rw [signedKostka_eq_KW, sh22_cells, sh1111_cells]; decide
theorem K_211_4 : signedKostka sh211.val sh4.val = 0 := by
  rw [signedKostka_eq_KW, sh211_cells, sh4_cells]; decide
theorem K_211_31 : signedKostka sh211.val sh31.val = 0 := by
  rw [signedKostka_eq_KW, sh211_cells, sh31_cells]; decide
theorem K_211_22 : signedKostka sh211.val sh22.val = 0 := by
  rw [signedKostka_eq_KW, sh211_cells, sh22_cells]; decide
theorem K_211_211 : signedKostka sh211.val sh211.val = 1 := by
  rw [signedKostka_eq_KW, sh211_cells]; decide
theorem K_211_1111 : signedKostka sh211.val sh1111.val = 1 := by
  rw [signedKostka_eq_KW, sh211_cells, sh1111_cells]; decide
theorem K_1111_4 : signedKostka sh1111.val sh4.val = 0 := by
  rw [signedKostka_eq_KW, sh1111_cells, sh4_cells]; decide
theorem K_1111_31 : signedKostka sh1111.val sh31.val = 0 := by
  rw [signedKostka_eq_KW, sh1111_cells, sh31_cells]; decide
theorem K_1111_22 : signedKostka sh1111.val sh22.val = 0 := by
  rw [signedKostka_eq_KW, sh1111_cells, sh22_cells]; decide
theorem K_1111_211 : signedKostka sh1111.val sh211.val = 0 := by
  rw [signedKostka_eq_KW, sh1111_cells, sh211_cells]; decide
theorem K_1111_1111 : signedKostka sh1111.val sh1111.val = 1 := by
  rw [signedKostka_eq_KW, sh1111_cells]; decide
theorem Mh_4_4 : Mh 4 sh4 sh4 = 1 := by
  rw [Mh_eq_PL, sh4_rows]; decide
theorem Mh_4_31 : Mh 4 sh4 sh31 = 1 := by
  rw [Mh_eq_PL, sh4_rows, sh31_rows]; decide
theorem Mh_4_22 : Mh 4 sh4 sh22 = 1 := by
  rw [Mh_eq_PL, sh4_rows, sh22_rows]; decide
theorem Mh_4_211 : Mh 4 sh4 sh211 = 1 := by
  rw [Mh_eq_PL, sh4_rows, sh211_rows]; decide
theorem Mh_4_1111 : Mh 4 sh4 sh1111 = 1 := by
  rw [Mh_eq_PL, sh4_rows, sh1111_rows]; decide
theorem Mh_31_4 : Mh 4 sh31 sh4 = 1 := by
  rw [Mh_eq_PL, sh31_rows, sh4_rows]; decide
theorem Mh_31_31 : Mh 4 sh31 sh31 = 0 := by
  rw [Mh_eq_PL, sh31_rows]; decide
theorem Mh_31_22 : Mh 4 sh31 sh22 = 2 := by
  rw [Mh_eq_PL, sh31_rows, sh22_rows]; decide
theorem Mh_31_211 : Mh 4 sh31 sh211 = 1 := by
  rw [Mh_eq_PL, sh31_rows, sh211_rows]; decide
theorem Mh_31_1111 : Mh 4 sh31 sh1111 = 0 := by
  rw [Mh_eq_PL, sh31_rows, sh1111_rows]; decide
theorem Mh_22_4 : Mh 4 sh22 sh4 = 1 := by
  rw [Mh_eq_PL, sh22_rows, sh4_rows]; decide
theorem Mh_22_31 : Mh 4 sh22 sh31 = 2 := by
  rw [Mh_eq_PL, sh22_rows, sh31_rows]; decide
theorem Mh_22_22 : Mh 4 sh22 sh22 = 1 := by
  rw [Mh_eq_PL, sh22_rows]; decide
theorem Mh_22_211 : Mh 4 sh22 sh211 = 2 := by
  rw [Mh_eq_PL, sh22_rows, sh211_rows]; decide
theorem Mh_22_1111 : Mh 4 sh22 sh1111 = 2 := by
  rw [Mh_eq_PL, sh22_rows, sh1111_rows]; decide
theorem Mh_211_4 : Mh 4 sh211 sh4 = 1 := by
  rw [Mh_eq_PL, sh211_rows, sh4_rows]; decide
theorem Mh_211_31 : Mh 4 sh211 sh31 = 1 := by
  rw [Mh_eq_PL, sh211_rows, sh31_rows]; decide
theorem Mh_211_22 : Mh 4 sh211 sh22 = 2 := by
  rw [Mh_eq_PL, sh211_rows, sh22_rows]; decide
theorem Mh_211_211 : Mh 4 sh211 sh211 = 1 := by
  rw [Mh_eq_PL, sh211_rows]; decide
theorem Mh_211_1111 : Mh 4 sh211 sh1111 = 0 := by
  rw [Mh_eq_PL, sh211_rows, sh1111_rows]; decide
theorem Mh_1111_4 : Mh 4 sh1111 sh4 = 1 := by
  rw [Mh_eq_PL, sh1111_rows, sh4_rows]; decide
theorem Mh_1111_31 : Mh 4 sh1111 sh31 = 0 := by
  rw [Mh_eq_PL, sh1111_rows, sh31_rows]; decide
theorem Mh_1111_22 : Mh 4 sh1111 sh22 = 2 := by
  rw [Mh_eq_PL, sh1111_rows, sh22_rows]; decide
theorem Mh_1111_211 : Mh 4 sh1111 sh211 = 0 := by
  rw [Mh_eq_PL, sh1111_rows, sh211_rows]; decide
theorem Mh_1111_1111 : Mh 4 sh1111 sh1111 = 0 := by
  rw [Mh_eq_PL, sh1111_rows]; decide

/-! ## Exhaustiveness and finite sums over ALL degree-d shapes -/

theorem shape_eq_iff {d : ℕ} {μ ν : DegreeShape d} : μ = ν ↔ μ.val.rowLens = ν.val.rowLens :=
  ⟨fun h => h ▸ rfl, fun h => Subtype.ext (YoungDiagram.equivListRowLens.injective (Subtype.ext h))⟩

/-- Every partition list of size at most four, with no enumeration hypothesis. -/
theorem small_partition (l : List ℕ) (hs : l.Sorted (· ≥ ·)) (hp : ∀ x ∈ l, 0 < x)
    (hl : l.sum ≤ 4) :
    l = [] ∨ l = [1] ∨ l = [2] ∨ l = [1,1] ∨ l = [3] ∨ l = [2,1] ∨ l = [1,1,1] ∨
      l = [4] ∨ l = [3,1] ∨ l = [2,2] ∨ l = [2,1,1] ∨ l = [1,1,1,1] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩
  · simp
  · have ha := hp a (by simp)
    simp only [List.sum_cons, List.sum_nil] at hl
    have : a ≤ 4 := by omega
    interval_cases a <;> simp
  · have ha := hp a (by simp); have hb := hp b (by simp)
    simp only [List.sorted_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq, List.not_mem_nil, false_implies, implies_true, and_true,
      List.sorted_nil] at hs
    simp only [List.sum_cons, List.sum_nil] at hl
    have : a ≤ 4 := by omega
    have : b ≤ 4 := by omega
    interval_cases a <;> interval_cases b <;> simp_all
  · have ha := hp a (by simp); have hb := hp b (by simp); have hc := hp c (by simp)
    simp only [List.sorted_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq, List.not_mem_nil, false_implies, implies_true, and_true,
      List.sorted_nil] at hs
    simp only [List.sum_cons, List.sum_nil] at hl
    have : a ≤ 4 := by omega
    have : b ≤ 4 := by omega
    have : c ≤ 4 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all
  · have ha := hp a (by simp); have hb := hp b (by simp); have hc := hp c (by simp)
    have he := hp e (by simp)
    simp only [List.sum_cons, List.sum_nil] at hl
    have : a = 1 ∧ b = 1 ∧ c = 1 ∧ e = 1 := by omega
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    simp
  · have ha := hp a (by simp); have hb := hp b (by simp); have hc := hp c (by simp)
    have he := hp e (by simp); have hf := hp f (by simp)
    simp only [List.sum_cons] at hl
    omega

theorem sum_list {d : ℕ} {M : Type*} [AddCommMonoid M] (l : List (DegreeShape d))
    (hn : (l.map fun μ => μ.val.rowLens).Nodup) (hex : ∀ μ, μ ∈ l) (f : DegreeShape d → M) :
    ∑ μ, f μ = (l.map f).sum := by
  rw [← List.sum_toFinset f (List.Nodup.of_map _ hn)]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext μ
  simp [hex]

theorem exhaust0 (μ : DegreeShape 0) : μ = sh0 := by
  have hs : μ.val.rowLens.sum = 0 := (rowLens_sum μ.val).trans μ.property
  rcases small_partition μ.val.rowLens (YoungDiagram.rowLens_sorted _)
    (YoungDiagram.pos_of_mem_rowLens _) (by omega) with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals (rw [h] at hs; simp at hs)
  all_goals simp [shape_eq_iff, h]

theorem sum0 {M : Type*} [AddCommMonoid M] (f : DegreeShape 0 → M) :
    ∑ μ, f μ = f sh0 := by
  have hex : ∀ μ, μ ∈ [sh0] := by
    intro μ
    rcases exhaust0 μ with rfl
    all_goals simp
  rw [sum_list [sh0] (by simp) hex]
  simp

/-- Literal (3.9) in degree 0: M′_{μρ} = Σ_λ (-1)^{λ₂+λ₄+…} K_{λμ} K_{λρ}. -/
theorem identity39_0 (μ ρ : DegreeShape 0) :
    Mh 0 μ ρ = ∑ lam : DegreeShape 0, (-1 : ℤ) ^ evenParts lam.val.rowLens *
      signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  rw [sum0]
  rcases exhaust0 μ with rfl
  all_goals rcases exhaust0 ρ with rfl
  all_goals simp only [K_0_0, Mh_0_0, sh0_rows]
  all_goals decide

theorem exhaust1 (μ : DegreeShape 1) : μ = sh1 := by
  have hs : μ.val.rowLens.sum = 1 := (rowLens_sum μ.val).trans μ.property
  rcases small_partition μ.val.rowLens (YoungDiagram.rowLens_sorted _)
    (YoungDiagram.pos_of_mem_rowLens _) (by omega) with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals (rw [h] at hs; simp at hs)
  all_goals simp [shape_eq_iff, h]

theorem sum1 {M : Type*} [AddCommMonoid M] (f : DegreeShape 1 → M) :
    ∑ μ, f μ = f sh1 := by
  have hex : ∀ μ, μ ∈ [sh1] := by
    intro μ
    rcases exhaust1 μ with rfl
    all_goals simp
  rw [sum_list [sh1] (by simp) hex]
  simp

/-- Literal (3.9) in degree 1: M′_{μρ} = Σ_λ (-1)^{λ₂+λ₄+…} K_{λμ} K_{λρ}. -/
theorem identity39_1 (μ ρ : DegreeShape 1) :
    Mh 1 μ ρ = ∑ lam : DegreeShape 1, (-1 : ℤ) ^ evenParts lam.val.rowLens *
      signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  rw [sum1]
  rcases exhaust1 μ with rfl
  all_goals rcases exhaust1 ρ with rfl
  all_goals simp only [K_1_1, Mh_1_1, sh1_rows]
  all_goals decide

theorem exhaust2 (μ : DegreeShape 2) : μ = sh2 ∨ μ = sh11 := by
  have hs : μ.val.rowLens.sum = 2 := (rowLens_sum μ.val).trans μ.property
  rcases small_partition μ.val.rowLens (YoungDiagram.rowLens_sorted _)
    (YoungDiagram.pos_of_mem_rowLens _) (by omega) with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals (rw [h] at hs; simp at hs)
  all_goals simp [shape_eq_iff, h]

theorem sum2 {M : Type*} [AddCommMonoid M] (f : DegreeShape 2 → M) :
    ∑ μ, f μ = f sh2 + (f sh11) := by
  have hex : ∀ μ, μ ∈ [sh2, sh11] := by
    intro μ
    rcases exhaust2 μ with rfl|rfl
    all_goals simp
  rw [sum_list [sh2, sh11] (by simp) hex]
  simp

/-- Literal (3.9) in degree 2: M′_{μρ} = Σ_λ (-1)^{λ₂+λ₄+…} K_{λμ} K_{λρ}. -/
theorem identity39_2 (μ ρ : DegreeShape 2) :
    Mh 2 μ ρ = ∑ lam : DegreeShape 2, (-1 : ℤ) ^ evenParts lam.val.rowLens *
      signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  rw [sum2]
  rcases exhaust2 μ with rfl|rfl
  all_goals rcases exhaust2 ρ with rfl|rfl
  all_goals simp only [K_2_2, K_2_11, K_11_2, K_11_11, Mh_2_2, Mh_2_11, Mh_11_2, Mh_11_11, sh2_rows, sh11_rows]
  all_goals decide

theorem exhaust3 (μ : DegreeShape 3) : μ = sh3 ∨ μ = sh21 ∨ μ = sh111 := by
  have hs : μ.val.rowLens.sum = 3 := (rowLens_sum μ.val).trans μ.property
  rcases small_partition μ.val.rowLens (YoungDiagram.rowLens_sorted _)
    (YoungDiagram.pos_of_mem_rowLens _) (by omega) with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals (rw [h] at hs; simp at hs)
  all_goals simp [shape_eq_iff, h]

theorem sum3 {M : Type*} [AddCommMonoid M] (f : DegreeShape 3 → M) :
    ∑ μ, f μ = f sh3 + (f sh21 + (f sh111)) := by
  have hex : ∀ μ, μ ∈ [sh3, sh21, sh111] := by
    intro μ
    rcases exhaust3 μ with rfl|rfl|rfl
    all_goals simp
  rw [sum_list [sh3, sh21, sh111] (by simp) hex]
  simp

/-- Literal (3.9) in degree 3: M′_{μρ} = Σ_λ (-1)^{λ₂+λ₄+…} K_{λμ} K_{λρ}. -/
theorem identity39_3 (μ ρ : DegreeShape 3) :
    Mh 3 μ ρ = ∑ lam : DegreeShape 3, (-1 : ℤ) ^ evenParts lam.val.rowLens *
      signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  rw [sum3]
  rcases exhaust3 μ with rfl|rfl|rfl
  all_goals rcases exhaust3 ρ with rfl|rfl|rfl
  all_goals simp only [K_3_3, K_3_21, K_3_111, K_21_3, K_21_21, K_21_111, K_111_3, K_111_21, K_111_111, Mh_3_3, Mh_3_21, Mh_3_111, Mh_21_3, Mh_21_21, Mh_21_111, Mh_111_3, Mh_111_21, Mh_111_111, sh3_rows, sh21_rows, sh111_rows]
  all_goals decide

theorem exhaust4 (μ : DegreeShape 4) : μ = sh4 ∨ μ = sh31 ∨ μ = sh22 ∨ μ = sh211 ∨ μ = sh1111 := by
  have hs : μ.val.rowLens.sum = 4 := (rowLens_sum μ.val).trans μ.property
  rcases small_partition μ.val.rowLens (YoungDiagram.rowLens_sorted _)
    (YoungDiagram.pos_of_mem_rowLens _) (by omega) with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals (rw [h] at hs; simp at hs)
  all_goals simp [shape_eq_iff, h]

theorem sum4 {M : Type*} [AddCommMonoid M] (f : DegreeShape 4 → M) :
    ∑ μ, f μ = f sh4 + (f sh31 + (f sh22 + (f sh211 + (f sh1111)))) := by
  have hex : ∀ μ, μ ∈ [sh4, sh31, sh22, sh211, sh1111] := by
    intro μ
    rcases exhaust4 μ with rfl|rfl|rfl|rfl|rfl
    all_goals simp
  rw [sum_list [sh4, sh31, sh22, sh211, sh1111] (by simp) hex]
  simp

/-- Literal (3.9) in degree 4: M′_{μρ} = Σ_λ (-1)^{λ₂+λ₄+…} K_{λμ} K_{λρ}. -/
theorem identity39_4 (μ ρ : DegreeShape 4) :
    Mh 4 μ ρ = ∑ lam : DegreeShape 4, (-1 : ℤ) ^ evenParts lam.val.rowLens *
      signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  rw [sum4]
  rcases exhaust4 μ with rfl|rfl|rfl|rfl|rfl
  all_goals rcases exhaust4 ρ with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [K_4_4, K_4_31, K_4_22, K_4_211, K_4_1111, K_31_4, K_31_31, K_31_22, K_31_211, K_31_1111, K_22_4, K_22_31, K_22_22, K_22_211, K_22_1111, K_211_4, K_211_31, K_211_22, K_211_211, K_211_1111, K_1111_4, K_1111_31, K_1111_22, K_1111_211, K_1111_1111, Mh_4_4, Mh_4_31, Mh_4_22, Mh_4_211, Mh_4_1111, Mh_31_4, Mh_31_31, Mh_31_22, Mh_31_211, Mh_31_1111, Mh_22_4, Mh_22_31, Mh_22_22, Mh_22_211, Mh_22_1111, Mh_211_4, Mh_211_31, Mh_211_22, Mh_211_211, Mh_211_1111, Mh_1111_4, Mh_1111_31, Mh_1111_22, Mh_1111_211, Mh_1111_1111, sh4_rows, sh31_rows, sh22_rows, sh211_rows, sh1111_rows]
  all_goals decide

/-! ## Independent cross-check against the inherited degree-2 Gram controls -/

theorem sh2_eq_row2 : sh2 = EKDualBasesControls.row2 := by
  rw [shape_eq_iff, sh2_rows, EKDualBasesControls.row2_rows]
theorem sh11_eq_col2 : sh11 = EKDualBasesControls.col2 := by
  rw [shape_eq_iff, sh11_rows, EKDualBasesControls.col2_rows]

/-- Bridge-A values agree with the inherited hand computation in actual Q. -/
theorem bridge_matches_inherited_degree_two :
    Mh 2 sh2 sh2 = 1 ∧ Mh 2 sh2 sh11 = 1 ∧ Mh 2 sh11 sh2 = 1 ∧ Mh 2 sh11 sh11 = 0 := by
  rw [sh2_eq_row2, sh11_eq_col2]
  obtain ⟨-, -, -, -, h1, h2, h3, h4, -⟩ := EKDualBasesControls.degree_two_gram
  exact ⟨h1, h2, h3, h4⟩

/-! ## Degree 1–3 hand fixtures for s_λ in the h-basis

Hand prediction from (3.6) `h_μ = Σ_λ K_{λμ} s_λ`, with hand odd Kostka numbers
`K_{(2),(1,1)} = 1`, `K_{(3),μ} = 1`, `K_{(2,1),(1,1,1)} = 0` (the two standard tableaux
of shape (2,1) have row words 312, 213 with opposite signs):
`s_(1) = h_1`, `s_(2) = h_2`, `s_(1,1) = h_1h_1 - h_2`, `s_(3) = h_3`,
`s_(2,1) = h_2h_1 - h_3`, `s_(1,1,1) = h_1h_1h_1 - h_3`. -/

def hand1 : DegreeShape 1 → Q := fun _ => hPartition sh1.val
def hand2 : DegreeShape 2 → Q := fun lam =>
  if lam.val.rowLens = [2] then hPartition sh2.val else hPartition sh11.val - hPartition sh2.val
def hand3 : DegreeShape 3 → Q := fun lam =>
  if lam.val.rowLens = [3] then hPartition sh3.val
  else if lam.val.rowLens = [2,1] then hPartition sh21.val - hPartition sh3.val
  else hPartition sh111.val - hPartition sh3.val

theorem hand_values :
    hand1 sh1 = EKElementaryQuotient.h 1 ∧
    hand2 sh2 = EKElementaryQuotient.h 2 ∧
    hand2 sh11 = EKElementaryQuotient.h 1 * EKElementaryQuotient.h 1 - EKElementaryQuotient.h 2 ∧
    hand3 sh3 = EKElementaryQuotient.h 3 ∧
    hand3 sh21 = EKElementaryQuotient.h 2 * EKElementaryQuotient.h 1 - EKElementaryQuotient.h 3 ∧
    hand3 sh111 = EKElementaryQuotient.h 1 * EKElementaryQuotient.h 1 * EKElementaryQuotient.h 1 -
      EKElementaryQuotient.h 3 := by
  simp [hand1, hand2, hand3, hPartition, mul_assoc]

/-- (3.6) for the hand predictions, with the actual odd Kostka numbers. -/
theorem hand1_defining (μ : DegreeShape 1) :
    hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • hand1 lam := by
  rw [sum1]
  rcases exhaust1 μ with rfl
  simp [hand1, K_1_1]

theorem hand2_defining (μ : DegreeShape 2) :
    hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • hand2 lam := by
  rw [sum2]
  rcases exhaust2 μ with rfl|rfl
  all_goals simp [hand2, K_2_2, K_2_11, K_11_2, K_11_11]

theorem hand3_defining (μ : DegreeShape 3) :
    hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • hand3 lam := by
  rw [sum3]
  rcases exhaust3 μ with rfl|rfl|rfl
  all_goals simp [hand3, K_3_3, K_3_21, K_3_111, K_21_3, K_21_21, K_21_111, K_111_3,
    K_111_21, K_111_111]

theorem pair_hh {d : ℕ} (ν μ : DegreeShape d) :
    quotientPairing (hPartition ν.val) (hPartition μ.val) = Mh d ν μ := rfl

/-- The sign fixture: λ = (1,1) has `C(λᵀ,2) = C(2,2) = 1` and `λ₂ = 1`. -/
theorem sign_fixture :
    (-1 : ℤ) ^ transposeChoose sh11.val = -1 ∧ (-1 : ℤ) ^ evenParts sh11.val.rowLens = -1 ∧
    (-1 : ℤ) ^ transposeChoose sh2.val = 1 ∧ (-1 : ℤ) ^ transposeChoose sh21.val = -1 ∧
    (-1 : ℤ) ^ transposeChoose sh111.val = -1 ∧ (-1 : ℤ) ^ transposeChoose sh3.val = 1 := by
  rw [sh11_signs.1, sh11_signs.2, sh2_signs.1, sh21_signs.1, sh111_signs.1, sh3_signs.1]
  decide

theorem hand1_gram (lam μ : DegreeShape 1) :
    quotientPairing (hand1 lam) (hand1 μ) = if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 := by
  rcases exhaust1 lam with rfl
  rcases exhaust1 μ with rfl
  simp [hand1, pair_hh, Mh_1_1, sh1_signs]

theorem hand2_gram (lam μ : DegreeShape 2) :
    quotientPairing (hand2 lam) (hand2 μ) = if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 := by
  rcases exhaust2 lam with rfl|rfl
  all_goals rcases exhaust2 μ with rfl|rfl
  all_goals simp [hand2, pair_hh, Mh_2_2, Mh_2_11, Mh_11_2, Mh_11_11, sh2_signs, sh11_signs,
    shape_eq_iff]

theorem hand3_gram (lam μ : DegreeShape 3) :
    quotientPairing (hand3 lam) (hand3 μ) = if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 := by
  rcases exhaust3 lam with rfl|rfl|rfl
  all_goals rcases exhaust3 μ with rfl|rfl|rfl
  all_goals simp [hand3, pair_hh, Mh_3_3, Mh_3_21, Mh_3_111, Mh_21_3, Mh_21_21, Mh_21_111,
    Mh_111_3, Mh_111_21, Mh_111_111, sh3_signs, sh21_signs, sh111_signs, shape_eq_iff]

/-- Required d = 2 fixture: norms +1 and -1 (NOT positive definite). -/
theorem degree_two_norms :
    quotientPairing (hand2 sh2) (hand2 sh2) = 1 ∧ quotientPairing (hand2 sh11) (hand2 sh11) = -1 ∧
    quotientPairing (hand2 sh2) (hand2 sh11) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hand2_gram, if_pos rfl, sh2_signs.1]; rfl
  · rw [hand2_gram, if_pos rfl, sh11_signs.1]; rfl
  · rw [hand2_gram, if_neg (by rw [shape_eq_iff]; simp)]

/-! ## Negative controls (each would-be simplification is REJECTED in actual Q) -/

/-- Dropping the sign: unsigned Kostka orthogonality fails at d = 2. -/
theorem unsigned_rejected :
    Mh 2 sh11 sh11 ≠ ∑ lam : DegreeShape 2, signedKostka lam.val sh11.val * signedKostka lam.val sh11.val := by
  rw [sum2, Mh_11_11, K_2_11, K_11_11]; decide

/-- Wrong parity statistic `λ₁ + λ₃ + …` (a global (-1)^d twist) fails at d = 3. -/
theorem odd_parts_rejected :
    Mh 3 sh3 sh3 ≠ ∑ lam : DegreeShape 3, (-1 : ℤ) ^ (lam.val.rowLens.sum - evenParts lam.val.rowLens) *
      signedKostka lam.val sh3.val * signedKostka lam.val sh3.val := by
  rw [sum3, Mh_3_3, K_3_3, K_21_3, K_111_3, sh3_rows, sh21_rows, sh111_rows]; decide

/-- The source M′ is (h,h), not EK's (e,h) matrix M: substituting M fails at d = 2. -/
theorem eh_matrix_rejected :
    M 2 sh2 sh2 ≠ ∑ lam : DegreeShape 2, (-1 : ℤ) ^ evenParts lam.val.rowLens *
      signedKostka lam.val sh2.val * signedKostka lam.val sh2.val := by
  have hM : M 2 sh2 sh2 = 0 := by
    rw [sh2_eq_row2]; exact EKDualBasesControls.degree_two_gram.1
  rw [hM, sum2, K_2_2, K_11_2, sh2_rows, sh11_rows]; decide

/-- Transposed Kostka indices `K_{μλ}K_{ρλ}` fail at d = 2. -/
theorem transposed_kostka_rejected :
    Mh 2 sh2 sh2 ≠ ∑ lam : DegreeShape 2, (-1 : ℤ) ^ evenParts lam.val.rowLens *
      signedKostka sh2.val lam.val * signedKostka sh2.val lam.val := by
  rw [sum2, Mh_2_2, K_2_2, K_2_11, sh2_rows, sh11_rows]; decide

/-- The two source forms of the sign are literally different numbers (e.g. (2,2,1):
`C(λᵀ,2) = C(3,2)+C(2,2) = 4`, `λ₂+λ₄ = 2`); only their parities agree. -/
theorem statistics_differ : evenParts [2,2,1] = 2 ∧ evenParts [3,2,2,1] = 3 ∧
    transposeChoose sh22.val = 2 ∧ evenParts sh22.val.rowLens = 2 ∧
    transposeChoose sh211.val = 3 ∧ evenParts sh211.val.rowLens = 1 := by
  refine ⟨by decide, by decide, sh22_signs.1, sh22_signs.2, sh211_signs.1, sh211_signs.2⟩

/-! ## Source Examples 3.5 and 3.6 (printed p27), reproduced through bridge B -/

def y221 : YoungDiagram := YoungDiagram.ofRowLens [2,2,1] (by decide)
def y11111 : YoungDiagram := YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)
def y311 : YoungDiagram := YoungDiagram.ofRowLens [3,1,1] (by decide)
def y2111 : YoungDiagram := YoungDiagram.ofRowLens [2,1,1,1] (by decide)

theorem y221_cells : rowCells y221 = [(2,0), (1,0), (1,1), (0,0), (0,1)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem y11111_cells : rowCells y11111 = [(4,0), (3,0), (2,0), (1,0), (0,0)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem y311_cells : rowCells y311 = [(2,0), (1,0), (0,0), (0,1), (0,2)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)
theorem y2111_cells : rowCells y2111 = [(3,0), (2,0), (1,0), (0,0), (0,1)] :=
  rowCells_eq_of _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- Example 3.5: five standard tableaux with signs + − − + −, sign(T_(2,2,1)) = 1. -/
theorem example_3_5 : signedKostka y221 y11111 = -1 ∧
    tableauSign (canonicalTableau y221) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [signedKostka_eq_KW, y221_cells, y11111_cells]; decide
  · unfold tableauSign rowWord
    rw [y221_cells, List.map_congr_left (fun p hp => canonical_entry
      ((mem_rowCells _ _).1 (y221_cells ▸ hp)))]
    decide

set_option maxRecDepth 100000 in
/-- Example 3.6: signs − + −, sign(T_(3,1,1)) = −1. -/
theorem example_3_6 : signedKostka y311 y2111 = 1 ∧
    tableauSign (canonicalTableau y311) = -1 := by
  refine ⟨?_, ?_⟩
  · rw [signedKostka_eq_KW, y311_cells, y2111_cells]; decide
  · unfold tableauSign rowWord
    rw [y311_cells, List.map_congr_left (fun p hp => canonical_entry
      ((mem_rowCells _ _).1 (y311_cells ▸ hp)))]
    decide
end OddMath.Frontier.EKSchurOrthonormalControls
