import OddMath.Frontier.EKDualBases
import OddMath.Frontier.KostkaModuleInversion
import OddMath.Frontier.TableauDominance
import OddMath.Frontier.SignedKostkaInvertibility
import OddMath.Frontier.EKMixedPairing

/-! PRE-production controls for EK1107.5610v2 p.30, Corollary 3.12 (3.14) and
Corollary 3.13 "Odd RSK II" (3.15).  Compiled BEFORE
`EKOddRSKII`; nothing here imports production.

* Unconditional exact checks for EVERY degree d ≤ 4 (all shapes, exhaustiveness proved):
  - (3.15) both printed equalities, on the literal entries of `EKDualBases.Me` = (e,e);
  - (3.14) first equation in the actual homogeneous piece of Q, with s_λ the unique
    solution of (3.6) (`KostkaModuleInversion.recover` of the existing h-basis);
  - (3.14) second equation (forgotten basis `EKDualBases.fBasis`) in actual Q.
* Negative controls: transposition-omitted variants of (3.15) and (3.14, first) are REFUTED
  in degree 2.
* Evaluation bridges proved for ALL inputs: odd Kostka numbers (bridge B), and the
  colored row-peeling recursion for the inherited matrix sum of EK Prop 2.6 (bridge C),
  giving M = (e,h) and M″ = (e,e) entries.

Attribution: the statistics, bridge B, shape fixtures, odd Kostka tables and exhaustiveness
blocks are reproduced VERBATIM (namespace changed, (h,h) bridge dropped) from
an earlier development version of `EKSchurOrthonormalControls` (sha256
a79379c4fb32776aac30be7af1e081b4e7cf7937a95d269b3212395038f7d6fc).
Bridge C's single-row and zero-row lemmas reproduce private proofs of the inherited
`EKMixedPairing`.  Finite checks are controls only.
-/
noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace OddMath.Frontier.EKOddRSKIIControls
open EKPairingMatrices EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases
open TableauDominance TableauContent TableauSign TableauRowWord
open EKPartitionSpanning (hPartition ePartition)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## Literal source statistics -/

/-- `λ₂ + λ₄ + λ₆ + …` of the partition list `(λ₁, λ₂, …)` (0-based odd positions). -/
noncomputable def evenParts (L : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range L.length, if i % 2 = 1 then L.getD i 0 else 0

/-- `C(λᵀ, 2) = Σ_j C(λᵀ_j, 2)`, with `λᵀ` Mathlib's actual transpose diagram. -/
noncomputable def transposeChoose (μ : YoungDiagram) : ℕ :=
  (μ.transpose.rowLens.map (fun a => a.choose 2)).sum

/-! ## Bridge A: the source M′ entries by exact row-peeling recursion -/

/-! ## Bridge B: the (3.7) odd Kostka number by an exact fibre bijection -/

noncomputable def validFill (cs : List (ℕ × ℕ)) (w : List ℕ) : Prop :=
  w.length = cs.length ∧ ∀ x ∈ cs.zip w, 0 < x.2 ∧ ∀ y ∈ cs.zip w,
    (x.1.1 = y.1.1 → x.1.2 < y.1.2 → x.2 ≤ y.2) ∧ (x.1.2 = y.1.2 → x.1.1 < y.1.1 → x.2 < y.2)

noncomputable instance (cs : List (ℕ × ℕ)) (w : List ℕ) : Decidable (validFill cs w) := by
  unfold validFill; infer_instance

/-- Candidate row words: distinct rearrangements of the content word, filtered. -/
noncomputable def words (cs : List (ℕ × ℕ)) (cw : List ℕ) : Finset (List ℕ) :=
  cw.permutations'.toFinset.filter (fun w => validFill cs w)

/-- `sign(T_λ) · Σ_T sign(T)`, with `sign = (-1)^{inversions of the row word}`. -/
noncomputable def KW (cs : List (ℕ × ℕ)) (cw : List ℕ) : ℤ :=
  (-1 : ℤ) ^ inversions (cs.map (fun p => p.1 + 1)) *
    ∑ w ∈ words cs cw, (-1 : ℤ) ^ inversions w

/-- Bottom-to-top, left-to-right cells of the diagram with row lengths `L`. -/
noncomputable def cellsOf (L : List ℕ) : List (ℕ × ℕ) :=
  ((List.range L.length).reverse).flatMap (fun i => (List.range (L.getD i 0)).map (fun j => (i, j)))

noncomputable def KL (L M : List ℕ) : ℤ := KW (cellsOf L) ((cellsOf M).map (fun p => p.1 + 1))

private noncomputable def find : List (ℕ × ℕ) → List ℕ → ℕ × ℕ → ℕ
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
private noncomputable def ofWord (μ : YoungDiagram) (w : List ℕ) (hv : validFill (rowCells μ) w) :
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

noncomputable def sh0 : DegreeShape 0 :=
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

noncomputable def sh1 : DegreeShape 1 :=
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

noncomputable def sh2 : DegreeShape 2 :=
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

noncomputable def sh11 : DegreeShape 2 :=
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

noncomputable def sh3 : DegreeShape 3 :=
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

noncomputable def sh21 : DegreeShape 3 :=
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

noncomputable def sh111 : DegreeShape 3 :=
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

noncomputable def sh4 : DegreeShape 4 :=
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

noncomputable def sh31 : DegreeShape 4 :=
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

noncomputable def sh22 : DegreeShape 4 :=
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

noncomputable def sh211 : DegreeShape 4 :=
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

noncomputable def sh1111 : DegreeShape 4 :=
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

theorem K_1_1 : signedKostka sh1.val sh1.val = 1 := by
  rw [signedKostka_eq_KW, sh1_cells]; decide

theorem K_2_2 : signedKostka sh2.val sh2.val = 1 := by
  rw [signedKostka_eq_KW, sh2_cells]; decide
theorem K_2_11 : signedKostka sh2.val sh11.val = 1 := by
  rw [signedKostka_eq_KW, sh2_cells, sh11_cells]; decide
theorem K_11_2 : signedKostka sh11.val sh2.val = 0 := by
  rw [signedKostka_eq_KW, sh11_cells, sh2_cells]; decide
theorem K_11_11 : signedKostka sh11.val sh11.val = 1 := by
  rw [signedKostka_eq_KW, sh11_cells]; decide

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


/-! ## Independent cross-check against the inherited degree-2 Gram controls -/


/-! ## Bridge C: colored row-peeling recursion (EK Prop 2.6 matrix sum), all inputs -/

open EKMixedPairing (matrixSum matrixWeight cell matrixSum_convolution matrixSum_mismatch)

theorem yd_eq_of_rowLens {a b : YoungDiagram} (h : a.rowLens = b.rowLens) : a = b :=
  YoungDiagram.equivListRowLens.injective (Subtype.ext h)

/-- Peel the LAST row platform; the single-row factor is the inherited cell weight. -/
noncomputable def PM : (r : ℕ) → (Fin r → ℕ) → (Fin r → Bool) → {c : ℕ} → (Fin c → ℕ) → (Fin c → Bool) → ℤ
  | 0, _, _, _, α, _ => if ∑ j, α j = 0 then 1 else 0
  | r+1, β, η, _, α, ε => ∑ u : Splits α, (-1 : ℤ) ^ crossCols (upper u) (lower u) *
      PM r (fun i => β (Fin.castSucc i)) (fun i => η (Fin.castSucc i)) (upper u) ε *
      (if β (Fin.last r) = ∑ j, lower u j then ∏ j, cell (η (Fin.last r)) (ε j) (lower u j) else 0)

theorem ms_singleton {c : ℕ} (m : ℕ) (b : Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    matrixSum (fun _ : Fin 1 => m) (fun _ => b) α ε =
      if m = ∑ j, α j then ∏ j, cell b (ε j) (α j) else 0 := by
  classical
  by_cases h : m = ∑ j, α j
  · rw [if_pos h]
    let N0 : Mat (fun _ : Fin 1 => m) α := ⟨fun _ j => α j, by
      constructor
      · funext i; exact h.symm
      · funext j; simp [colSum]⟩
    have unique (N : Mat (fun _ : Fin 1 => m) α) : N = N0 := by
      apply Subtype.ext
      funext i j
      have hh := congrFun N.property.2 j
      simpa [colSum, Fin.sum_univ_one, Subsingleton.elim i (0 : Fin 1)] using hh
    unfold matrixSum
    rw [Finset.sum_eq_single N0]
    · simp [N0, matrixWeight, crossing]
    · intro N _ hne; exact (hne (unique N)).elim
    · simp
  · rw [if_neg h]
    exact matrixSum_mismatch _ _ _ _ (by simpa using h)

theorem ms_zeroRows {c : ℕ} (β : Fin 0 → ℕ) (η : Fin 0 → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    matrixSum β η α ε = if (∑ j, α j) = 0 then 1 else 0 := by
  classical
  by_cases h : (∑ j, α j) = 0
  · rw [if_pos h]
    have hz (j : Fin c) : α j = 0 := (Finset.sum_eq_zero_iff.mp h) j (Finset.mem_univ j)
    let N0 : Mat β α := ⟨fun i => Fin.elim0 i, by
      constructor
      · funext i; exact Fin.elim0 i
      · funext j; simp [colSum, hz]⟩
    unfold matrixSum
    rw [Finset.sum_eq_single N0]
    · simp [matrixWeight, crossing]
    · intro N _ hne
      exact (hne (Subtype.ext (funext fun i => Fin.elim0 i))).elim
    · simp
  · rw [if_neg h]
    exact matrixSum_mismatch _ _ _ _ (by simpa [eq_comm] using h)

private theorem split_last {X : Type} {r : ℕ} (β : Fin (r+1) → X) :
    β = Fin.addCases (fun i : Fin r => β (Fin.castSucc i)) (fun _ : Fin 1 => β (Fin.last r)) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · rw [Fin.addCases_left]; rfl
  · rw [Fin.addCases_right]
    congr 1
    apply Fin.ext
    have := k.isLt
    simp only [Fin.coe_natAdd, Fin.val_last]
    omega

theorem matrixSum_eq_PM : ∀ (r : ℕ) (β : Fin r → ℕ) (η : Fin r → Bool) {c : ℕ}
    (α : Fin c → ℕ) (ε : Fin c → Bool), matrixSum β η α ε = PM r β η α ε
  | 0, β, η, c, α, ε => by rw [ms_zeroRows]; rfl
  | r+1, β, η, c, α, ε => by
    conv_lhs => rw [split_last β, split_last η]
    rw [matrixSum_convolution]
    simp only [PM]
    apply Finset.sum_congr rfl
    intro u _
    rw [matrixSum_eq_PM r _ _ (upper u), ms_singleton]

noncomputable def PML (L : List ℕ) (b : Bool) (K : List ℕ) (e : Bool) : ℤ :=
  PM L.length (fun i => L.get i) (fun _ => b) (c := K.length) (fun j => K.get j) (fun _ => e)

private theorem ms_reindex {r r' c c' : ℕ} (hr : r = r') (hc : c = c')
    (β : Fin r' → ℕ) (b : Bool) (α : Fin c' → ℕ) (e : Bool) :
    matrixSum (fun i : Fin r => β (Fin.cast hr i)) (fun _ => b)
      (fun j : Fin c => α (Fin.cast hc j)) (fun _ => e) =
      matrixSum β (fun _ => b) α (fun _ => e) := by
  subst hr; subst hc; rfl

theorem ms_rows (ν μ : YoungDiagram) (b e : Bool) :
    matrixSum (EKSemiorthogonality.rows ν) (fun _ => b) (EKSemiorthogonality.rows μ) (fun _ => e) =
      PML ν.rowLens b μ.rowLens e := by
  unfold PML
  rw [← matrixSum_eq_PM, ← ms_reindex (YoungDiagram.length_rowLens (μ := ν)).symm
    (YoungDiagram.length_rowLens (μ := μ)).symm]
  congr 1 <;> funext i <;> simp [EKSemiorthogonality.rows, YoungDiagram.get_rowLens]

/-- Every source M″ = (e,e) entry, any degree, as the computable recursion. -/
theorem Me_eq_PML (d : ℕ) (ν μ : DegreeShape d) :
    Me d ν μ = PML ν.val.rowLens true μ.val.rowLens true := by
  change quotientPairing (EKSemiorthogonality.ePartition ν.val)
    (EKSemiorthogonality.ePartition μ.val) = _
  rw [EKSemiorthogonality.ePartition_eq_mixed, EKSemiorthogonality.ePartition_eq_mixed,
    EKMixedPairing.quotientPairing_eq_matrixSum, ms_rows]

/-- Every source M = (e,h) entry (row index colored e), any degree. -/
theorem M_eq_PML (d : ℕ) (ν μ : DegreeShape d) :
    M d ν μ = PML ν.val.rowLens true μ.val.rowLens false := by
  change quotientPairing (EKSemiorthogonality.ePartition ν.val)
    (EKSemiorthogonality.hPartition μ.val) = _
  rw [EKSemiorthogonality.ePartition_eq_mixed, EKSemiorthogonality.hPartition_eq_mixed,
    EKMixedPairing.quotientPairing_eq_matrixSum, ms_rows]

/-! ## Source signs and the dual coefficient system -/

/-- `(μ choose 2) = Σ_i C(μ_i, 2)` (EK p.10 notation), over the actual row lengths. -/
noncomputable def rowChoose (μ : YoungDiagram) : ℕ := (μ.rowLens.map (fun a => a.choose 2)).sum

/-- `(-1)^{(μ 2)+|μ|}`, with `|μ| = d` for a degree-d shape. -/
noncomputable def Esrc (d : ℕ) (μ : DegreeShape d) : ℤ := (-1) ^ (rowChoose μ.val + d)

/-- `(-1)^{ℓ(w_λ)+(λᵀ 2)+|λ|}`, the sign on the left of the second (3.14) equation. -/
noncomputable def sigmaSrc (d : ℕ) (lam : DegreeShape d) : ℤ :=
  (-1) ^ (EKSemiorthogonality.ell lam.val + transposeChoose lam.val + d)

/-- Candidate e-pairings `(e_ν, s_λ)` read off from the printed second (3.14) equation. -/
noncomputable def Xsrc (d : ℕ) (ν lam : DegreeShape d) : ℤ :=
  sigmaSrc d lam * Esrc d ν * signedKostka lam.val.transpose ν.val

/-! ## Actual s_λ and exact reductions to integer identities (all degrees) -/

/-- s_λ: the unique solution of (3.6) in the actual degree-d piece. -/
noncomputable def sC (d : ℕ) : DegreeShape d → degreePiece d :=
  KostkaModuleInversion.recover d (degreeHBasis d)

theorem sC_defining (d : ℕ) (j : DegreeShape d) :
    ∑ lam, signedKostka lam.val j.val • sC d lam = degreeHBasis d j :=
  congrFun (KostkaModuleInversion.rightInverse d (degreeHBasis d)) j

theorem pair_ee (d : ℕ) (ν μ : DegreeShape d) :
    quotientPairing (ePartition ν.val) (ePartition μ.val) = Me d ν μ := rfl

/-- The e-pairings of s are forced by any integer solution of X·K = M. -/
theorem pair_e_sC (d : ℕ) (X : DegreeShape d → DegreeShape d → ℤ)
    (hX : ∀ ν j, ∑ lam, X ν lam * signedKostka lam.val j.val = M d ν j)
    (ν lam : DegreeShape d) :
    quotientPairing (ePartition ν.val) (sC d lam).val = X ν lam := by
  have hsol : ∀ j, ∑ i, quotientPairing (ePartition ν.val) (sC d i).val *
      signedKostka i.val j.val = M d ν j := by
    intro j
    have h := congrArg (fun y : degreePiece d => quotientPairing (ePartition ν.val) y.val)
      (sC_defining d j)
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, smul_eq_mul,
      degreeHBasis_apply] at h
    change _ = quotientPairing (ePartition ν.val) (hPartition j.val)
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    ring
  obtain ⟨c, _, huniq⟩ := DegreeShapes.degree_unique_solution d (fun j => M d ν j)
  have h1 := huniq _ hsol
  have h2 := huniq (X ν) (fun j => hX ν j)
  exact congrFun (h1.trans h2.symm) lam

/-- Elements of the degree piece are separated by their e-pairings. -/
theorem ext_e (d : ℕ) (x y : degreePiece d)
    (h : ∀ ν : DegreeShape d, quotientPairing (ePartition ν.val) x.val =
      quotientPairing (ePartition ν.val) y.val) : x = y := by
  apply (fBasis d).repr.injective
  ext ν
  rw [f_coordinates, f_coordinates, h]

theorem neg_one_sq (n : ℕ) : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- Second (3.14) equation in actual Q from the integer system X·K = M. -/
theorem second_of_dual (d : ℕ)
    (hX : ∀ ν j, ∑ lam, Xsrc d ν lam * signedKostka lam.val j.val = M d ν j)
    (lam : DegreeShape d) :
    ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + transposeChoose lam.val + lam.val.card)) • sC d lam =
      ∑ μ, ((-1 : ℤ) ^ (rowChoose μ.val + μ.val.card) * signedKostka lam.val.transpose μ.val) •
        fBasis d μ := by
  apply ext_e
  intro ν
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, smul_eq_mul,
    pair_e_sC d _ hX, e_f, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, lam.property, ν.property]
  unfold Xsrc sigmaSrc Esrc
  rw [← mul_assoc, ← mul_assoc, neg_one_sq, one_mul]

/-- First (3.14) equation in actual Q from X·K = M and the paired numeric identity. -/
theorem first_of_numeric (d : ℕ)
    (hX : ∀ ν j, ∑ lam, Xsrc d ν lam * signedKostka lam.val j.val = M d ν j)
    (hF : ∀ ν μ, Esrc d μ * Me d ν μ = ∑ lam, (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + d) *
      signedKostka lam.val.transpose μ.val * Xsrc d ν lam)
    (μ : DegreeShape d) :
    ((-1 : ℤ) ^ (rowChoose μ.val + μ.val.card)) • degreeEBasis d μ =
      ∑ lam, ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card) *
        signedKostka lam.val.transpose μ.val) • sC d lam := by
  apply ext_e
  intro ν
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, smul_eq_mul,
    pair_e_sC d _ hX, degreeEBasis_apply, pair_ee, μ.property]
  have hc : ∀ lam : DegreeShape d, lam.val.card = d := fun lam => lam.property
  simp only [hc]
  exact hF ν μ


/-! ### Degree 0: exact M = (e,h), M″ = (e,e), transposes and statistics -/

theorem sh0_T : sh0.val.transpose = sh0.val :=
  yd_eq_of_rowLens (by rw [sh0_transpose, sh0_rows])
theorem sh0_ell : EKSemiorthogonality.ell sh0.val = 0 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh0_rc : rowChoose sh0.val = 0 := by
  unfold rowChoose; rw [sh0_rows]; decide
theorem sh0_cc : transposeChoose sh0.val = 0 := sh0_signs.1
theorem sh0_ev : evenParts sh0.val.rowLens = 0 := sh0_signs.2
theorem Me_0_0 : Me 0 sh0 sh0 = 1 := by
  rw [Me_eq_PML, sh0_rows]; decide
theorem Meh_0_0 : M 0 sh0 sh0 = 1 := by
  rw [M_eq_PML, sh0_rows]; decide

/-- Degree 0: the dual row-vector system X·K = M with X_{νλ} = σ_λ E_ν K_{λᵀν}. -/
theorem dual0 (ν j : DegreeShape 0) :
    ∑ lam : DegreeShape 0, Xsrc 0 ν lam * signedKostka lam.val j.val = M 0 ν j := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum0]
  rcases exhaust0 ν with rfl
  all_goals rcases exhaust0 j with rfl
  all_goals simp only [sh0_T, sh0_ell, sh0_rc, sh0_cc, sh0_ev, K_0_0, Me_0_0, Meh_0_0]
  all_goals decide

/-- Degree 0: the numeric content of the first (3.14) equation after pairing with e_ν. -/
theorem first0 (ν μ : DegreeShape 0) :
    Esrc 0 μ * Me 0 ν μ = ∑ lam : DegreeShape 0,
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + 0) * signedKostka lam.val.transpose μ.val * Xsrc 0 ν lam := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum0]
  rcases exhaust0 ν with rfl
  all_goals rcases exhaust0 μ with rfl
  all_goals simp only [sh0_T, sh0_ell, sh0_rc, sh0_cc, sh0_ev, K_0_0, Me_0_0, Meh_0_0]
  all_goals decide

/-- Degree 0: (3.15), both printed equalities, literal entries of `EKDualBases.Me`. -/
theorem odd_rsk_II_0 (μ ρ : DegreeShape 0) :
    (-1 : ℤ) ^ (rowChoose μ.val + 0 + (rowChoose ρ.val + 0)) * Me 0 μ ρ =
      ∑ lam : DegreeShape 0, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val ∧
    ∑ lam : DegreeShape 0, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val =
      ∑ lam : DegreeShape 0, (-1 : ℤ) ^ evenParts lam.val.rowLens *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val := by
  simp only [sum0]
  rcases exhaust0 μ with rfl
  all_goals rcases exhaust0 ρ with rfl
  all_goals simp only [sh0_T, sh0_ell, sh0_rc, sh0_cc, sh0_ev, K_0_0, Me_0_0, Meh_0_0]
  all_goals decide


/-! ### Degree 1: exact M = (e,h), M″ = (e,e), transposes and statistics -/

theorem sh1_T : sh1.val.transpose = sh1.val :=
  yd_eq_of_rowLens (by rw [sh1_transpose, sh1_rows])
theorem sh1_ell : EKSemiorthogonality.ell sh1.val = 0 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh1_rc : rowChoose sh1.val = 0 := by
  unfold rowChoose; rw [sh1_rows]; decide
theorem sh1_cc : transposeChoose sh1.val = 0 := sh1_signs.1
theorem sh1_ev : evenParts sh1.val.rowLens = 0 := sh1_signs.2
theorem Me_1_1 : Me 1 sh1 sh1 = 1 := by
  rw [Me_eq_PML, sh1_rows]; decide
theorem Meh_1_1 : M 1 sh1 sh1 = 1 := by
  rw [M_eq_PML, sh1_rows]; decide

/-- Degree 1: the dual row-vector system X·K = M with X_{νλ} = σ_λ E_ν K_{λᵀν}. -/
theorem dual1 (ν j : DegreeShape 1) :
    ∑ lam : DegreeShape 1, Xsrc 1 ν lam * signedKostka lam.val j.val = M 1 ν j := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum1]
  rcases exhaust1 ν with rfl
  all_goals rcases exhaust1 j with rfl
  all_goals simp only [sh1_T, sh1_ell, sh1_rc, sh1_cc, sh1_ev, K_1_1, Me_1_1, Meh_1_1]
  all_goals decide

/-- Degree 1: the numeric content of the first (3.14) equation after pairing with e_ν. -/
theorem first1 (ν μ : DegreeShape 1) :
    Esrc 1 μ * Me 1 ν μ = ∑ lam : DegreeShape 1,
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + 1) * signedKostka lam.val.transpose μ.val * Xsrc 1 ν lam := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum1]
  rcases exhaust1 ν with rfl
  all_goals rcases exhaust1 μ with rfl
  all_goals simp only [sh1_T, sh1_ell, sh1_rc, sh1_cc, sh1_ev, K_1_1, Me_1_1, Meh_1_1]
  all_goals decide

/-- Degree 1: (3.15), both printed equalities, literal entries of `EKDualBases.Me`. -/
theorem odd_rsk_II_1 (μ ρ : DegreeShape 1) :
    (-1 : ℤ) ^ (rowChoose μ.val + 1 + (rowChoose ρ.val + 1)) * Me 1 μ ρ =
      ∑ lam : DegreeShape 1, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val ∧
    ∑ lam : DegreeShape 1, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val =
      ∑ lam : DegreeShape 1, (-1 : ℤ) ^ evenParts lam.val.rowLens *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val := by
  simp only [sum1]
  rcases exhaust1 μ with rfl
  all_goals rcases exhaust1 ρ with rfl
  all_goals simp only [sh1_T, sh1_ell, sh1_rc, sh1_cc, sh1_ev, K_1_1, Me_1_1, Meh_1_1]
  all_goals decide


/-! ### Degree 2: exact M = (e,h), M″ = (e,e), transposes and statistics -/

theorem sh2_T : sh2.val.transpose = sh11.val :=
  yd_eq_of_rowLens (by rw [sh2_transpose, sh11_rows])
theorem sh2_ell : EKSemiorthogonality.ell sh2.val = 0 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh2_rc : rowChoose sh2.val = 1 := by
  unfold rowChoose; rw [sh2_rows]; decide
theorem sh2_cc : transposeChoose sh2.val = 0 := sh2_signs.1
theorem sh2_ev : evenParts sh2.val.rowLens = 0 := sh2_signs.2
theorem sh11_T : sh11.val.transpose = sh2.val :=
  yd_eq_of_rowLens (by rw [sh11_transpose, sh2_rows])
theorem sh11_ell : EKSemiorthogonality.ell sh11.val = 0 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh11_rc : rowChoose sh11.val = 0 := by
  unfold rowChoose; rw [sh11_rows]; decide
theorem sh11_cc : transposeChoose sh11.val = 1 := sh11_signs.1
theorem sh11_ev : evenParts sh11.val.rowLens = 1 := sh11_signs.2
theorem Me_2_2 : Me 2 sh2 sh2 = -1 := by
  rw [Me_eq_PML, sh2_rows]; decide
theorem Meh_2_2 : M 2 sh2 sh2 = 0 := by
  rw [M_eq_PML, sh2_rows]; decide
theorem Me_2_11 : Me 2 sh2 sh11 = 1 := by
  rw [Me_eq_PML, sh2_rows, sh11_rows]; decide
theorem Meh_2_11 : M 2 sh2 sh11 = 1 := by
  rw [M_eq_PML, sh2_rows, sh11_rows]; decide
theorem Me_11_2 : Me 2 sh11 sh2 = 1 := by
  rw [Me_eq_PML, sh11_rows, sh2_rows]; decide
theorem Meh_11_2 : M 2 sh11 sh2 = 1 := by
  rw [M_eq_PML, sh11_rows, sh2_rows]; decide
theorem Me_11_11 : Me 2 sh11 sh11 = 0 := by
  rw [Me_eq_PML, sh11_rows]; decide
theorem Meh_11_11 : M 2 sh11 sh11 = 0 := by
  rw [M_eq_PML, sh11_rows]; decide

/-- Degree 2: the dual row-vector system X·K = M with X_{νλ} = σ_λ E_ν K_{λᵀν}. -/
theorem dual2 (ν j : DegreeShape 2) :
    ∑ lam : DegreeShape 2, Xsrc 2 ν lam * signedKostka lam.val j.val = M 2 ν j := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum2]
  rcases exhaust2 ν with rfl|rfl
  all_goals rcases exhaust2 j with rfl|rfl
  all_goals simp only [sh2_T, sh2_ell, sh2_rc, sh2_cc, sh2_ev, sh11_T, sh11_ell, sh11_rc, sh11_cc, sh11_ev, K_2_2, Me_2_2, Meh_2_2, K_2_11, Me_2_11, Meh_2_11, K_11_2, Me_11_2, Meh_11_2, K_11_11, Me_11_11, Meh_11_11]
  all_goals decide

/-- Degree 2: the numeric content of the first (3.14) equation after pairing with e_ν. -/
theorem first2 (ν μ : DegreeShape 2) :
    Esrc 2 μ * Me 2 ν μ = ∑ lam : DegreeShape 2,
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + 2) * signedKostka lam.val.transpose μ.val * Xsrc 2 ν lam := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum2]
  rcases exhaust2 ν with rfl|rfl
  all_goals rcases exhaust2 μ with rfl|rfl
  all_goals simp only [sh2_T, sh2_ell, sh2_rc, sh2_cc, sh2_ev, sh11_T, sh11_ell, sh11_rc, sh11_cc, sh11_ev, K_2_2, Me_2_2, Meh_2_2, K_2_11, Me_2_11, Meh_2_11, K_11_2, Me_11_2, Meh_11_2, K_11_11, Me_11_11, Meh_11_11]
  all_goals decide

/-- Degree 2: (3.15), both printed equalities, literal entries of `EKDualBases.Me`. -/
theorem odd_rsk_II_2 (μ ρ : DegreeShape 2) :
    (-1 : ℤ) ^ (rowChoose μ.val + 2 + (rowChoose ρ.val + 2)) * Me 2 μ ρ =
      ∑ lam : DegreeShape 2, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val ∧
    ∑ lam : DegreeShape 2, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val =
      ∑ lam : DegreeShape 2, (-1 : ℤ) ^ evenParts lam.val.rowLens *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val := by
  simp only [sum2]
  rcases exhaust2 μ with rfl|rfl
  all_goals rcases exhaust2 ρ with rfl|rfl
  all_goals simp only [sh2_T, sh2_ell, sh2_rc, sh2_cc, sh2_ev, sh11_T, sh11_ell, sh11_rc, sh11_cc, sh11_ev, K_2_2, Me_2_2, Meh_2_2, K_2_11, Me_2_11, Meh_2_11, K_11_2, Me_11_2, Meh_11_2, K_11_11, Me_11_11, Meh_11_11]
  all_goals decide


/-! ### Degree 3: exact M = (e,h), M″ = (e,e), transposes and statistics -/

theorem sh3_T : sh3.val.transpose = sh111.val :=
  yd_eq_of_rowLens (by rw [sh3_transpose, sh111_rows])
theorem sh3_ell : EKSemiorthogonality.ell sh3.val = 0 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh3_rc : rowChoose sh3.val = 3 := by
  unfold rowChoose; rw [sh3_rows]; decide
theorem sh3_cc : transposeChoose sh3.val = 0 := sh3_signs.1
theorem sh3_ev : evenParts sh3.val.rowLens = 0 := sh3_signs.2
theorem sh21_T : sh21.val.transpose = sh21.val :=
  yd_eq_of_rowLens (by rw [sh21_transpose, sh21_rows])
theorem sh21_ell : EKSemiorthogonality.ell sh21.val = 1 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh21_rc : rowChoose sh21.val = 1 := by
  unfold rowChoose; rw [sh21_rows]; decide
theorem sh21_cc : transposeChoose sh21.val = 1 := sh21_signs.1
theorem sh21_ev : evenParts sh21.val.rowLens = 1 := sh21_signs.2
theorem sh111_T : sh111.val.transpose = sh3.val :=
  yd_eq_of_rowLens (by rw [sh111_transpose, sh3_rows])
theorem sh111_ell : EKSemiorthogonality.ell sh111.val = 0 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh111_rc : rowChoose sh111.val = 0 := by
  unfold rowChoose; rw [sh111_rows]; decide
theorem sh111_cc : transposeChoose sh111.val = 3 := sh111_signs.1
theorem sh111_ev : evenParts sh111.val.rowLens = 1 := sh111_signs.2
theorem Me_3_3 : Me 3 sh3 sh3 = -1 := by
  rw [Me_eq_PML, sh3_rows]; decide
theorem Meh_3_3 : M 3 sh3 sh3 = 0 := by
  rw [M_eq_PML, sh3_rows]; decide
theorem Me_3_21 : Me 3 sh3 sh21 = -1 := by
  rw [Me_eq_PML, sh3_rows, sh21_rows]; decide
theorem Meh_3_21 : M 3 sh3 sh21 = 0 := by
  rw [M_eq_PML, sh3_rows, sh21_rows]; decide
theorem Me_3_111 : Me 3 sh3 sh111 = 1 := by
  rw [Me_eq_PML, sh3_rows, sh111_rows]; decide
theorem Meh_3_111 : M 3 sh3 sh111 = 1 := by
  rw [M_eq_PML, sh3_rows, sh111_rows]; decide
theorem Me_21_3 : Me 3 sh21 sh3 = -1 := by
  rw [Me_eq_PML, sh21_rows, sh3_rows]; decide
theorem Meh_21_3 : M 3 sh21 sh3 = 0 := by
  rw [M_eq_PML, sh21_rows, sh3_rows]; decide
theorem Me_21_21 : Me 3 sh21 sh21 = -2 := by
  rw [Me_eq_PML, sh21_rows]; decide
theorem Meh_21_21 : M 3 sh21 sh21 = -1 := by
  rw [M_eq_PML, sh21_rows]; decide
theorem Me_21_111 : Me 3 sh21 sh111 = 1 := by
  rw [Me_eq_PML, sh21_rows, sh111_rows]; decide
theorem Meh_21_111 : M 3 sh21 sh111 = 1 := by
  rw [M_eq_PML, sh21_rows, sh111_rows]; decide
theorem Me_111_3 : Me 3 sh111 sh3 = 1 := by
  rw [Me_eq_PML, sh111_rows, sh3_rows]; decide
theorem Meh_111_3 : M 3 sh111 sh3 = 1 := by
  rw [M_eq_PML, sh111_rows, sh3_rows]; decide
theorem Me_111_21 : Me 3 sh111 sh21 = 1 := by
  rw [Me_eq_PML, sh111_rows, sh21_rows]; decide
theorem Meh_111_21 : M 3 sh111 sh21 = 1 := by
  rw [M_eq_PML, sh111_rows, sh21_rows]; decide
theorem Me_111_111 : Me 3 sh111 sh111 = 0 := by
  rw [Me_eq_PML, sh111_rows]; decide
theorem Meh_111_111 : M 3 sh111 sh111 = 0 := by
  rw [M_eq_PML, sh111_rows]; decide

/-- Degree 3: the dual row-vector system X·K = M with X_{νλ} = σ_λ E_ν K_{λᵀν}. -/
theorem dual3 (ν j : DegreeShape 3) :
    ∑ lam : DegreeShape 3, Xsrc 3 ν lam * signedKostka lam.val j.val = M 3 ν j := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum3]
  rcases exhaust3 ν with rfl|rfl|rfl
  all_goals rcases exhaust3 j with rfl|rfl|rfl
  all_goals simp only [sh3_T, sh3_ell, sh3_rc, sh3_cc, sh3_ev, sh21_T, sh21_ell, sh21_rc, sh21_cc, sh21_ev, sh111_T, sh111_ell, sh111_rc, sh111_cc, sh111_ev, K_3_3, Me_3_3, Meh_3_3, K_3_21, Me_3_21, Meh_3_21, K_3_111, Me_3_111, Meh_3_111, K_21_3, Me_21_3, Meh_21_3, K_21_21, Me_21_21, Meh_21_21, K_21_111, Me_21_111, Meh_21_111, K_111_3, Me_111_3, Meh_111_3, K_111_21, Me_111_21, Meh_111_21, K_111_111, Me_111_111, Meh_111_111]
  all_goals decide

/-- Degree 3: the numeric content of the first (3.14) equation after pairing with e_ν. -/
theorem first3 (ν μ : DegreeShape 3) :
    Esrc 3 μ * Me 3 ν μ = ∑ lam : DegreeShape 3,
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + 3) * signedKostka lam.val.transpose μ.val * Xsrc 3 ν lam := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum3]
  rcases exhaust3 ν with rfl|rfl|rfl
  all_goals rcases exhaust3 μ with rfl|rfl|rfl
  all_goals simp only [sh3_T, sh3_ell, sh3_rc, sh3_cc, sh3_ev, sh21_T, sh21_ell, sh21_rc, sh21_cc, sh21_ev, sh111_T, sh111_ell, sh111_rc, sh111_cc, sh111_ev, K_3_3, Me_3_3, Meh_3_3, K_3_21, Me_3_21, Meh_3_21, K_3_111, Me_3_111, Meh_3_111, K_21_3, Me_21_3, Meh_21_3, K_21_21, Me_21_21, Meh_21_21, K_21_111, Me_21_111, Meh_21_111, K_111_3, Me_111_3, Meh_111_3, K_111_21, Me_111_21, Meh_111_21, K_111_111, Me_111_111, Meh_111_111]
  all_goals decide

/-- Degree 3: (3.15), both printed equalities, literal entries of `EKDualBases.Me`. -/
theorem odd_rsk_II_3 (μ ρ : DegreeShape 3) :
    (-1 : ℤ) ^ (rowChoose μ.val + 3 + (rowChoose ρ.val + 3)) * Me 3 μ ρ =
      ∑ lam : DegreeShape 3, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val ∧
    ∑ lam : DegreeShape 3, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val =
      ∑ lam : DegreeShape 3, (-1 : ℤ) ^ evenParts lam.val.rowLens *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val := by
  simp only [sum3]
  rcases exhaust3 μ with rfl|rfl|rfl
  all_goals rcases exhaust3 ρ with rfl|rfl|rfl
  all_goals simp only [sh3_T, sh3_ell, sh3_rc, sh3_cc, sh3_ev, sh21_T, sh21_ell, sh21_rc, sh21_cc, sh21_ev, sh111_T, sh111_ell, sh111_rc, sh111_cc, sh111_ev, K_3_3, Me_3_3, Meh_3_3, K_3_21, Me_3_21, Meh_3_21, K_3_111, Me_3_111, Meh_3_111, K_21_3, Me_21_3, Meh_21_3, K_21_21, Me_21_21, Meh_21_21, K_21_111, Me_21_111, Meh_21_111, K_111_3, Me_111_3, Meh_111_3, K_111_21, Me_111_21, Meh_111_21, K_111_111, Me_111_111, Meh_111_111]
  all_goals decide


/-! ### Degree 4: exact M = (e,h), M″ = (e,e), transposes and statistics -/

theorem sh4_T : sh4.val.transpose = sh1111.val :=
  yd_eq_of_rowLens (by rw [sh4_transpose, sh1111_rows])
theorem sh4_ell : EKSemiorthogonality.ell sh4.val = 0 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh4_rc : rowChoose sh4.val = 6 := by
  unfold rowChoose; rw [sh4_rows]; decide
theorem sh4_cc : transposeChoose sh4.val = 0 := sh4_signs.1
theorem sh4_ev : evenParts sh4.val.rowLens = 0 := sh4_signs.2
theorem sh31_T : sh31.val.transpose = sh211.val :=
  yd_eq_of_rowLens (by rw [sh31_transpose, sh211_rows])
theorem sh31_ell : EKSemiorthogonality.ell sh31.val = 2 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh31_rc : rowChoose sh31.val = 3 := by
  unfold rowChoose; rw [sh31_rows]; decide
theorem sh31_cc : transposeChoose sh31.val = 1 := sh31_signs.1
theorem sh31_ev : evenParts sh31.val.rowLens = 1 := sh31_signs.2
theorem sh22_T : sh22.val.transpose = sh22.val :=
  yd_eq_of_rowLens (by rw [sh22_transpose, sh22_rows])
theorem sh22_ell : EKSemiorthogonality.ell sh22.val = 1 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh22_rc : rowChoose sh22.val = 2 := by
  unfold rowChoose; rw [sh22_rows]; decide
theorem sh22_cc : transposeChoose sh22.val = 2 := sh22_signs.1
theorem sh22_ev : evenParts sh22.val.rowLens = 2 := sh22_signs.2
theorem sh211_T : sh211.val.transpose = sh31.val :=
  yd_eq_of_rowLens (by rw [sh211_transpose, sh31_rows])
theorem sh211_ell : EKSemiorthogonality.ell sh211.val = 2 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh211_rc : rowChoose sh211.val = 1 := by
  unfold rowChoose; rw [sh211_rows]; decide
theorem sh211_cc : transposeChoose sh211.val = 3 := sh211_signs.1
theorem sh211_ev : evenParts sh211.val.rowLens = 1 := sh211_signs.2
theorem sh1111_T : sh1111.val.transpose = sh4.val :=
  yd_eq_of_rowLens (by rw [sh1111_transpose, sh4_rows])
theorem sh1111_ell : EKSemiorthogonality.ell sh1111.val = 0 := by
  unfold EKSemiorthogonality.ell; decide
theorem sh1111_rc : rowChoose sh1111.val = 0 := by
  unfold rowChoose; rw [sh1111_rows]; decide
theorem sh1111_cc : transposeChoose sh1111.val = 6 := sh1111_signs.1
theorem sh1111_ev : evenParts sh1111.val.rowLens = 2 := sh1111_signs.2
theorem Me_4_4 : Me 4 sh4 sh4 = 1 := by
  rw [Me_eq_PML, sh4_rows]; decide
theorem Meh_4_4 : M 4 sh4 sh4 = 0 := by
  rw [M_eq_PML, sh4_rows]; decide
theorem Me_4_31 : Me 4 sh4 sh31 = -1 := by
  rw [Me_eq_PML, sh4_rows, sh31_rows]; decide
theorem Meh_4_31 : M 4 sh4 sh31 = 0 := by
  rw [M_eq_PML, sh4_rows, sh31_rows]; decide
theorem Me_4_22 : Me 4 sh4 sh22 = 1 := by
  rw [Me_eq_PML, sh4_rows, sh22_rows]; decide
theorem Meh_4_22 : M 4 sh4 sh22 = 0 := by
  rw [M_eq_PML, sh4_rows, sh22_rows]; decide
theorem Me_4_211 : Me 4 sh4 sh211 = -1 := by
  rw [Me_eq_PML, sh4_rows, sh211_rows]; decide
theorem Meh_4_211 : M 4 sh4 sh211 = 0 := by
  rw [M_eq_PML, sh4_rows, sh211_rows]; decide
theorem Me_4_1111 : Me 4 sh4 sh1111 = 1 := by
  rw [Me_eq_PML, sh4_rows, sh1111_rows]; decide
theorem Meh_4_1111 : M 4 sh4 sh1111 = 1 := by
  rw [M_eq_PML, sh4_rows, sh1111_rows]; decide
theorem Me_31_4 : Me 4 sh31 sh4 = -1 := by
  rw [Me_eq_PML, sh31_rows, sh4_rows]; decide
theorem Meh_31_4 : M 4 sh31 sh4 = 0 := by
  rw [M_eq_PML, sh31_rows, sh4_rows]; decide
theorem Me_31_31 : Me 4 sh31 sh31 = 0 := by
  rw [Me_eq_PML, sh31_rows]; decide
theorem Meh_31_31 : M 4 sh31 sh31 = 0 := by
  rw [M_eq_PML, sh31_rows]; decide
theorem Me_31_22 : Me 4 sh31 sh22 = -2 := by
  rw [Me_eq_PML, sh31_rows, sh22_rows]; decide
theorem Meh_31_22 : M 4 sh31 sh22 = 0 := by
  rw [M_eq_PML, sh31_rows, sh22_rows]; decide
theorem Me_31_211 : Me 4 sh31 sh211 = 1 := by
  rw [Me_eq_PML, sh31_rows, sh211_rows]; decide
theorem Meh_31_211 : M 4 sh31 sh211 = 1 := by
  rw [M_eq_PML, sh31_rows, sh211_rows]; decide
theorem Me_31_1111 : Me 4 sh31 sh1111 = 0 := by
  rw [Me_eq_PML, sh31_rows, sh1111_rows]; decide
theorem Meh_31_1111 : M 4 sh31 sh1111 = 0 := by
  rw [M_eq_PML, sh31_rows, sh1111_rows]; decide
theorem Me_22_4 : Me 4 sh22 sh4 = 1 := by
  rw [Me_eq_PML, sh22_rows, sh4_rows]; decide
theorem Meh_22_4 : M 4 sh22 sh4 = 0 := by
  rw [M_eq_PML, sh22_rows, sh4_rows]; decide
theorem Me_22_31 : Me 4 sh22 sh31 = -2 := by
  rw [Me_eq_PML, sh22_rows, sh31_rows]; decide
theorem Meh_22_31 : M 4 sh22 sh31 = 0 := by
  rw [M_eq_PML, sh22_rows, sh31_rows]; decide
theorem Me_22_22 : Me 4 sh22 sh22 = 1 := by
  rw [Me_eq_PML, sh22_rows]; decide
theorem Meh_22_22 : M 4 sh22 sh22 = -1 := by
  rw [M_eq_PML, sh22_rows]; decide
theorem Me_22_211 : Me 4 sh22 sh211 = -2 := by
  rw [Me_eq_PML, sh22_rows, sh211_rows]; decide
theorem Meh_22_211 : M 4 sh22 sh211 = 0 := by
  rw [M_eq_PML, sh22_rows, sh211_rows]; decide
theorem Me_22_1111 : Me 4 sh22 sh1111 = 2 := by
  rw [Me_eq_PML, sh22_rows, sh1111_rows]; decide
theorem Meh_22_1111 : M 4 sh22 sh1111 = 2 := by
  rw [M_eq_PML, sh22_rows, sh1111_rows]; decide
theorem Me_211_4 : Me 4 sh211 sh4 = -1 := by
  rw [Me_eq_PML, sh211_rows, sh4_rows]; decide
theorem Meh_211_4 : M 4 sh211 sh4 = 0 := by
  rw [M_eq_PML, sh211_rows, sh4_rows]; decide
theorem Me_211_31 : Me 4 sh211 sh31 = 1 := by
  rw [Me_eq_PML, sh211_rows, sh31_rows]; decide
theorem Meh_211_31 : M 4 sh211 sh31 = 1 := by
  rw [M_eq_PML, sh211_rows, sh31_rows]; decide
theorem Me_211_22 : Me 4 sh211 sh22 = -2 := by
  rw [Me_eq_PML, sh211_rows, sh22_rows]; decide
theorem Meh_211_22 : M 4 sh211 sh22 = 0 := by
  rw [M_eq_PML, sh211_rows, sh22_rows]; decide
theorem Me_211_211 : Me 4 sh211 sh211 = 1 := by
  rw [Me_eq_PML, sh211_rows]; decide
theorem Meh_211_211 : M 4 sh211 sh211 = 1 := by
  rw [M_eq_PML, sh211_rows]; decide
theorem Me_211_1111 : Me 4 sh211 sh1111 = 0 := by
  rw [Me_eq_PML, sh211_rows, sh1111_rows]; decide
theorem Meh_211_1111 : M 4 sh211 sh1111 = 0 := by
  rw [M_eq_PML, sh211_rows, sh1111_rows]; decide
theorem Me_1111_4 : Me 4 sh1111 sh4 = 1 := by
  rw [Me_eq_PML, sh1111_rows, sh4_rows]; decide
theorem Meh_1111_4 : M 4 sh1111 sh4 = 1 := by
  rw [M_eq_PML, sh1111_rows, sh4_rows]; decide
theorem Me_1111_31 : Me 4 sh1111 sh31 = 0 := by
  rw [Me_eq_PML, sh1111_rows, sh31_rows]; decide
theorem Meh_1111_31 : M 4 sh1111 sh31 = 0 := by
  rw [M_eq_PML, sh1111_rows, sh31_rows]; decide
theorem Me_1111_22 : Me 4 sh1111 sh22 = 2 := by
  rw [Me_eq_PML, sh1111_rows, sh22_rows]; decide
theorem Meh_1111_22 : M 4 sh1111 sh22 = 2 := by
  rw [M_eq_PML, sh1111_rows, sh22_rows]; decide
theorem Me_1111_211 : Me 4 sh1111 sh211 = 0 := by
  rw [Me_eq_PML, sh1111_rows, sh211_rows]; decide
theorem Meh_1111_211 : M 4 sh1111 sh211 = 0 := by
  rw [M_eq_PML, sh1111_rows, sh211_rows]; decide
theorem Me_1111_1111 : Me 4 sh1111 sh1111 = 0 := by
  rw [Me_eq_PML, sh1111_rows]; decide
theorem Meh_1111_1111 : M 4 sh1111 sh1111 = 0 := by
  rw [M_eq_PML, sh1111_rows]; decide

/-- Degree 4: the dual row-vector system X·K = M with X_{νλ} = σ_λ E_ν K_{λᵀν}. -/
theorem dual4 (ν j : DegreeShape 4) :
    ∑ lam : DegreeShape 4, Xsrc 4 ν lam * signedKostka lam.val j.val = M 4 ν j := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum4]
  rcases exhaust4 ν with rfl|rfl|rfl|rfl|rfl
  all_goals rcases exhaust4 j with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [sh4_T, sh4_ell, sh4_rc, sh4_cc, sh4_ev, sh31_T, sh31_ell, sh31_rc, sh31_cc, sh31_ev, sh22_T, sh22_ell, sh22_rc, sh22_cc, sh22_ev, sh211_T, sh211_ell, sh211_rc, sh211_cc, sh211_ev, sh1111_T, sh1111_ell, sh1111_rc, sh1111_cc, sh1111_ev, K_4_4, Me_4_4, Meh_4_4, K_4_31, Me_4_31, Meh_4_31, K_4_22, Me_4_22, Meh_4_22, K_4_211, Me_4_211, Meh_4_211, K_4_1111, Me_4_1111, Meh_4_1111, K_31_4, Me_31_4, Meh_31_4, K_31_31, Me_31_31, Meh_31_31, K_31_22, Me_31_22, Meh_31_22, K_31_211, Me_31_211, Meh_31_211, K_31_1111, Me_31_1111, Meh_31_1111, K_22_4, Me_22_4, Meh_22_4, K_22_31, Me_22_31, Meh_22_31, K_22_22, Me_22_22, Meh_22_22, K_22_211, Me_22_211, Meh_22_211, K_22_1111, Me_22_1111, Meh_22_1111, K_211_4, Me_211_4, Meh_211_4, K_211_31, Me_211_31, Meh_211_31, K_211_22, Me_211_22, Meh_211_22, K_211_211, Me_211_211, Meh_211_211, K_211_1111, Me_211_1111, Meh_211_1111, K_1111_4, Me_1111_4, Meh_1111_4, K_1111_31, Me_1111_31, Meh_1111_31, K_1111_22, Me_1111_22, Meh_1111_22, K_1111_211, Me_1111_211, Meh_1111_211, K_1111_1111, Me_1111_1111, Meh_1111_1111]
  all_goals decide

/-- Degree 4: the numeric content of the first (3.14) equation after pairing with e_ν. -/
theorem first4 (ν μ : DegreeShape 4) :
    Esrc 4 μ * Me 4 ν μ = ∑ lam : DegreeShape 4,
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + 4) * signedKostka lam.val.transpose μ.val * Xsrc 4 ν lam := by
  unfold Xsrc sigmaSrc Esrc
  simp only [sum4]
  rcases exhaust4 ν with rfl|rfl|rfl|rfl|rfl
  all_goals rcases exhaust4 μ with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [sh4_T, sh4_ell, sh4_rc, sh4_cc, sh4_ev, sh31_T, sh31_ell, sh31_rc, sh31_cc, sh31_ev, sh22_T, sh22_ell, sh22_rc, sh22_cc, sh22_ev, sh211_T, sh211_ell, sh211_rc, sh211_cc, sh211_ev, sh1111_T, sh1111_ell, sh1111_rc, sh1111_cc, sh1111_ev, K_4_4, Me_4_4, Meh_4_4, K_4_31, Me_4_31, Meh_4_31, K_4_22, Me_4_22, Meh_4_22, K_4_211, Me_4_211, Meh_4_211, K_4_1111, Me_4_1111, Meh_4_1111, K_31_4, Me_31_4, Meh_31_4, K_31_31, Me_31_31, Meh_31_31, K_31_22, Me_31_22, Meh_31_22, K_31_211, Me_31_211, Meh_31_211, K_31_1111, Me_31_1111, Meh_31_1111, K_22_4, Me_22_4, Meh_22_4, K_22_31, Me_22_31, Meh_22_31, K_22_22, Me_22_22, Meh_22_22, K_22_211, Me_22_211, Meh_22_211, K_22_1111, Me_22_1111, Meh_22_1111, K_211_4, Me_211_4, Meh_211_4, K_211_31, Me_211_31, Meh_211_31, K_211_22, Me_211_22, Meh_211_22, K_211_211, Me_211_211, Meh_211_211, K_211_1111, Me_211_1111, Meh_211_1111, K_1111_4, Me_1111_4, Meh_1111_4, K_1111_31, Me_1111_31, Meh_1111_31, K_1111_22, Me_1111_22, Meh_1111_22, K_1111_211, Me_1111_211, Meh_1111_211, K_1111_1111, Me_1111_1111, Meh_1111_1111]
  all_goals decide

/-- Degree 4: (3.15), both printed equalities, literal entries of `EKDualBases.Me`. -/
theorem odd_rsk_II_4 (μ ρ : DegreeShape 4) :
    (-1 : ℤ) ^ (rowChoose μ.val + 4 + (rowChoose ρ.val + 4)) * Me 4 μ ρ =
      ∑ lam : DegreeShape 4, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val ∧
    ∑ lam : DegreeShape 4, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val =
      ∑ lam : DegreeShape 4, (-1 : ℤ) ^ evenParts lam.val.rowLens *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val := by
  simp only [sum4]
  rcases exhaust4 μ with rfl|rfl|rfl|rfl|rfl
  all_goals rcases exhaust4 ρ with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [sh4_T, sh4_ell, sh4_rc, sh4_cc, sh4_ev, sh31_T, sh31_ell, sh31_rc, sh31_cc, sh31_ev, sh22_T, sh22_ell, sh22_rc, sh22_cc, sh22_ev, sh211_T, sh211_ell, sh211_rc, sh211_cc, sh211_ev, sh1111_T, sh1111_ell, sh1111_rc, sh1111_cc, sh1111_ev, K_4_4, Me_4_4, Meh_4_4, K_4_31, Me_4_31, Meh_4_31, K_4_22, Me_4_22, Meh_4_22, K_4_211, Me_4_211, Meh_4_211, K_4_1111, Me_4_1111, Meh_4_1111, K_31_4, Me_31_4, Meh_31_4, K_31_31, Me_31_31, Meh_31_31, K_31_22, Me_31_22, Meh_31_22, K_31_211, Me_31_211, Meh_31_211, K_31_1111, Me_31_1111, Meh_31_1111, K_22_4, Me_22_4, Meh_22_4, K_22_31, Me_22_31, Meh_22_31, K_22_22, Me_22_22, Meh_22_22, K_22_211, Me_22_211, Meh_22_211, K_22_1111, Me_22_1111, Meh_22_1111, K_211_4, Me_211_4, Meh_211_4, K_211_31, Me_211_31, Meh_211_31, K_211_22, Me_211_22, Meh_211_22, K_211_211, Me_211_211, Meh_211_211, K_211_1111, Me_211_1111, Meh_211_1111, K_1111_4, Me_1111_4, Meh_1111_4, K_1111_31, Me_1111_31, Meh_1111_31, K_1111_22, Me_1111_22, Meh_1111_22, K_1111_211, Me_1111_211, Meh_1111_211, K_1111_1111, Me_1111_1111, Meh_1111_1111]
  all_goals decide


/-! ## Unconditional (3.14) in actual Q for every degree d ≤ 4 -/

theorem dual_le_four (d : ℕ) (hd : d ≤ 4) :
    ∀ ν j : DegreeShape d, ∑ lam, Xsrc d ν lam * signedKostka lam.val j.val = M d ν j := by
  interval_cases d
  exacts [dual0, dual1, dual2, dual3, dual4]

theorem first_le_four (d : ℕ) (hd : d ≤ 4) :
    ∀ ν μ : DegreeShape d, Esrc d μ * Me d ν μ = ∑ lam, (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + d) *
      signedKostka lam.val.transpose μ.val * Xsrc d ν lam := by
  interval_cases d
  exacts [first0, first1, first2, first3, first4]

/-- (3.14), first equation, as printed, in actual Q, d ≤ 4:
`(-1)^{(μ 2)+|μ|} e_μ = Σ_λ (-1)^{ℓ(w_λ)+|λ|} K_{λᵀμ} s_λ`. -/
theorem cor_3_12_first_le_four (d : ℕ) (hd : d ≤ 4) (μ : DegreeShape d) :
    ((-1 : ℤ) ^ (rowChoose μ.val + μ.val.card)) • degreeEBasis d μ =
      ∑ lam, ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card) *
        signedKostka lam.val.transpose μ.val) • sC d lam :=
  first_of_numeric d (dual_le_four d hd) (first_le_four d hd) μ

/-- (3.14), second equation, as printed, in actual Q, d ≤ 4:
`(-1)^{ℓ(w_λ)+(λᵀ 2)+|λ|} s_λ = Σ_μ (-1)^{(μ 2)+|μ|} K_{λᵀμ} f_μ`. -/
theorem cor_3_12_second_le_four (d : ℕ) (hd : d ≤ 4) (lam : DegreeShape d) :
    ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + transposeChoose lam.val + lam.val.card)) • sC d lam =
      ∑ μ, ((-1 : ℤ) ^ (rowChoose μ.val + μ.val.card) * signedKostka lam.val.transpose μ.val) •
        fBasis d μ :=
  second_of_dual d (dual_le_four d hd) lam

/-- (3.15), both printed equalities, literal `EKDualBases.Me`, every d ≤ 4. -/
theorem cor_3_13_le_four (d : ℕ) (hd : d ≤ 4) (μ ρ : DegreeShape d) :
    (-1 : ℤ) ^ (rowChoose μ.val + d + (rowChoose ρ.val + d)) * Me d μ ρ =
      ∑ lam : DegreeShape d, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val ∧
    ∑ lam : DegreeShape d, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val =
      ∑ lam : DegreeShape d, (-1 : ℤ) ^ evenParts lam.val.rowLens *
        signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val := by
  interval_cases d
  exacts [odd_rsk_II_0 μ ρ, odd_rsk_II_1 μ ρ, odd_rsk_II_2 μ ρ, odd_rsk_II_3 μ ρ, odd_rsk_II_4 μ ρ]

/-! ## Negative controls: transposition omitted (must FAIL) -/

/-- (3.15) with `K_{λμ}K_{λρ}` in place of `K_{λᵀμ}K_{λᵀρ}` is FALSE in degree 2. -/
theorem omitted_transpose_3_15_fails :
    ¬ ∀ μ ρ : DegreeShape 2, (-1 : ℤ) ^ (rowChoose μ.val + 2 + (rowChoose ρ.val + 2)) * Me 2 μ ρ =
      ∑ lam : DegreeShape 2, (-1 : ℤ) ^ transposeChoose lam.val *
        signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  intro h
  have h1 := h sh2 sh2
  simp only [sum2, sh2_rc, Me_2_2, sh2_cc, sh11_cc, K_2_2, K_11_2] at h1
  revert h1
  decide

/-- (3.14, first) with `K_{λμ}` in place of `K_{λᵀμ}` is FALSE in actual Q, degree 2. -/
theorem omitted_transpose_3_14_fails :
    ¬ ((-1 : ℤ) ^ (rowChoose sh2.val + sh2.val.card)) • degreeEBasis 2 sh2 =
      ∑ lam, ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card) *
        signedKostka lam.val sh2.val) • sC 2 lam := by
  intro h
  have h1 := congrArg (fun y : degreePiece 2 => quotientPairing (ePartition sh2.val) y.val) h
  simp only [sum2] at h1
  simp only [Submodule.coe_add, map_add, Submodule.coe_smul, map_zsmul, smul_eq_mul,
    pair_e_sC 2 _ dual2, degreeEBasis_apply, pair_ee] at h1
  unfold Xsrc sigmaSrc Esrc at h1
  simp only [sh2.property, sh11.property, sh2_T, sh11_T, sh2_ell, sh11_ell, sh2_rc, sh11_rc,
    sh2_cc, sh11_cc, K_2_2, K_2_11, K_11_2, K_11_11, Me_2_2] at h1
  revert h1
  decide

end OddMath.Frontier.EKOddRSKIIControls

