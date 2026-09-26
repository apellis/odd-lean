import OddMath.Frontier.OddLREvenExample
import OddMath.Frontier.OddLRRuleLemma47
import OddMath.Frontier.OddLRRuleExample
import OddMath.Frontier.OddLRHiveTableau

/-!
# The worked examples of Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1

Each example of E is stated about the library's own objects (`PositiveTableau`, `SkewTableau`,
`TableauRowWord.rowWord`, `TableauDominance.tableauSign`, `OddLRTableau.SkewTableau.sign`,
`OddLRHive.AS`, `OddLRTableau.signBetween`, `SkewPolynomial`) and checked by kernel computation.

* §2.1, p.6: `T = 112/23` has `w_r(T) = 23112` and `sign(T) = (-1)^5 = -1`; `T_{(21)} = 11/2`,
  `sign(T_{(21)}) = (-1)^2 = 1`; `T_{(311)} = 111/2/3`, `sign(T_{(311)}) = (-1)^7 = -1`
  (`sign_example`, `sign_T21`, `sign_T311`).
* Example 2.4, p.7: for `T = 1122/2334/344/56`, `dN(T) = 16`, `E^>(T) = 28`, `sW(T) = 47`
  (`example_2_4`), with E's direction counts `eastGreater`, `southWest` (§2.2).
* Example 3.2, p.8: the word `53422331112` is the row word of `1112/2233/34/5`, and of no
  other tableau (`example_3_2`).
* Example 4.4, p.13: for `λ = (3,3,2,1)`, `μ = (2,1,1)`, `S = ::1/:12/:2/3`, `Ŝ = 001/012/02/3`
  and `sign(S) = (-1)^{18} = 1` (`example_4_4`).
* Remark 4.5, p.13: the one-box skew tableaux of shapes `(1,1)/(1)` and `(2)/(1)` with the same
  entry have opposite signs (`remark_4_5`).
* Example 4.13, p.17, at the level of tableaux: for `S = ::1/:2/1` (`OddLRRule.exS2`),
  `OddLRHive.AS 3 S` is the displayed triangle `OddLRHive.exA` and `Q_△(A_S) = 6 = N^<(S)`
  (`example_4_13_tableau`).
* §4.2, p.13: `sign(x₁x₂x₃, x₁x₃x₂) = -1` in `OPol_3` (`signBetween_example`).
-/

namespace OddMath.Frontier.OddLRExamples

open scoped BigOperators
open TableauSign TableauRowWord OddLRTableau OddLREven

/-! ## Row lengths of explicit diagrams -/

theorem rowLen_ofRowLens' (w : List ℕ) (hw : w.Sorted (· ≥ ·)) (r : ℕ) :
    (YoungDiagram.ofRowLens w hw).rowLen r = w.getD r 0 := by
  apply le_antisymm
  · by_contra h
    push_neg at h
    have := (mem_ofRowLens_iff (hw := hw) (p := (r, w.getD r 0))).mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    exact lt_irrefl _ this.2
  · by_contra h
    push_neg at h
    have hr : r < w.length := by
      by_contra hr
      rw [List.getD_eq_default _ _ (by omega)] at h
      omega
    have := (mem_ofRowLens_iff (hw := hw) (p := (r, (YoungDiagram.ofRowLens w hw).rowLen r))).mpr
      ⟨hr, h⟩
    exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp this)

/-! ## §2.1: signs of tableaux -/

/-- `T = 112/23`, E §2.1, p.6. -/
def T112_23 : PositiveTableau (YoungDiagram.ofRowLens [3, 2] (by decide)) :=
  posTab [[1, 1, 2], [2, 3]] (by decide) 2 3 (by decide) (by decide) (by decide) (by decide)

/-- E §2.1, p.6: `w_r(T) = 23112` and `sign(T) = (-1)^5 = -1` for `T = 112/23`. -/
theorem sign_example :
    rowWord T112_23 = [2, 3, 1, 1, 2] ∧ inversions (rowWord T112_23) = 5 ∧
      TableauDominance.tableauSign T112_23 = -1 := by
  have h : rowWord T112_23 = [2, 3, 1, 1, 2] := by
    rw [T112_23, rowWord_posTab]; decide
  refine ⟨h, by rw [h]; decide, ?_⟩
  rw [TableauDominance.tableauSign, h]; decide

theorem rowWord_canonical (w : List ℕ) (hw : w.Sorted (· ≥ ·)) :
    rowWord (TableauDominance.canonicalTableau (YoungDiagram.ofRowLens w hw)) =
      (rowCellsOf w).map (fun p => if p ∈ YoungDiagram.ofRowLens w hw then p.1 + 1 else 0) := by
  rw [rowWord, rowCells_ofRowLens]
  rfl

/-- E §2.1, p.6: `T_{(21)} = 11/2`, `w_r(T_{(21)}) = 211`, `sign(T_{(21)}) = (-1)^2 = 1`. -/
theorem sign_T21 :
    rowWord (TableauDominance.canonicalTableau (yd [2, 1])) = [2, 1, 1] ∧
      inversions (rowWord (TableauDominance.canonicalTableau (yd [2, 1]))) = 2 ∧
      TableauDominance.tableauSign (TableauDominance.canonicalTableau (yd [2, 1])) = 1 := by
  have h : rowWord (TableauDominance.canonicalTableau (yd [2, 1])) = [2, 1, 1] := by
    rw [rowWord_canonical]; decide
  refine ⟨h, by rw [h]; decide, ?_⟩
  rw [TableauDominance.tableauSign, h]; decide

/-- E §2.1, p.6: `T_{(311)} = 111/2/3`, `w_r = 32111`, `sign(T_{(311)}) = (-1)^7 = -1`. -/
theorem sign_T311 :
    rowWord (TableauDominance.canonicalTableau (yd [3, 1, 1])) = [3, 2, 1, 1, 1] ∧
      inversions (rowWord (TableauDominance.canonicalTableau (yd [3, 1, 1]))) = 7 ∧
      TableauDominance.tableauSign (TableauDominance.canonicalTableau (yd [3, 1, 1])) = -1 := by
  have h : rowWord (TableauDominance.canonicalTableau (yd [3, 1, 1])) = [3, 2, 1, 1, 1] := by
    rw [rowWord_canonical]; decide
  refine ⟨h, by rw [h]; decide, ?_⟩
  rw [TableauDominance.tableauSign, h]; decide

/-! ## Example 2.4: boxterpretations -/

/-- `E^>(T)` (E §2.2): for each box `B`, the boxes East of `B` (in a column strictly to the
right) with entry greater than that of `B`. -/
def eastGreater {mu : YoungDiagram} (T : PositiveTableau mu) : ℕ :=
  ∑ p ∈ mu.cells, (mu.cells.filter (fun q => p.2 < q.2 ∧ T.entry p.1 p.2 < T.entry q.1 q.2)).card

/-- `sW(λ)` (E §2.2): for each box `B`, the boxes southWest of `B`: south (in the row of `B`
or below) and West (in a column strictly to the left). -/
def southWest (mu : YoungDiagram) : ℕ :=
  ∑ p ∈ mu.cells, (mu.cells.filter (fun q => p.1 ≤ q.1 ∧ q.2 < p.2)).card

/-- `T = 1122/2334/344/56`, E Example 2.4. -/
def T24 : PositiveTableau (YoungDiagram.ofRowLens [4, 4, 3, 2] (by decide)) :=
  posTab [[1, 1, 2, 2], [2, 3, 3, 4], [3, 4, 4], [5, 6]] (by decide) 4 4 (by decide) (by decide)
    (by decide) (by decide)

/-- **E Example 2.4**: `dN(T) = 16`, `E^>(T) = 28`, `sW(T) = 47`. -/
theorem example_2_4 :
    TableauStripSigns.directNorth (YoungDiagram.ofRowLens [4, 4, 3, 2] (by decide)) = 16 ∧
      eastGreater T24 = 28 ∧ southWest (YoungDiagram.ofRowLens [4, 4, 3, 2] (by decide)) = 47 := by
  refine ⟨by decide, ?_, by decide⟩
  unfold eastGreater
  simp only [T24, posTab_entry]
  decide

/-! ## Example 3.2: reading a tableau from its row word -/

/-- `1112/2233/34/5`, E Example 3.2. -/
def T32 : PositiveTableau (YoungDiagram.ofRowLens [4, 4, 2, 1] (by decide)) :=
  posTab [[1, 1, 1, 2], [2, 2, 3, 3], [3, 4], [5]] (by decide) 4 4 (by decide) (by decide)
    (by decide) (by decide)

/-- **E Example 3.2**: `w = 53422331112` is the row word of `T = 1112/2233/34/5`, and `T` is the
only tableau (of any shape) with row word `w`. -/
theorem example_3_2 :
    rowWord T32 = [5, 3, 4, 2, 2, 3, 3, 1, 1, 1, 2] ∧
      ∀ (kap : YoungDiagram) (T : PositiveTableau kap), rowWord T = [5, 3, 4, 2, 2, 3, 3, 1, 1, 1, 2] →
        (⟨kap, T⟩ : Σ κ : YoungDiagram, PositiveTableau κ) = ⟨_, T32⟩ := by
  have h : rowWord T32 = [5, 3, 4, 2, 2, 3, 3, 1, 1, 1, 2] := by
    rw [T32, rowWord_posTab]; decide
  refine ⟨h, fun kap T hT => ?_⟩
  apply OddLRRule.sigma_eq_of_nrows
  rw [← OddLRRule.P_rowWord, ← OddLRRule.P_rowWord, hT, h]

/-! ## Example 4.4 and Remark 4.5: signs of skew tableaux -/

/-- `S = ::1/:12/:2/3` of shape `(3,3,2,1)/(2,1,1)`, E Example 4.4, given by its row word `32121`. -/
def S44 : SkewTableau (yd [3, 3, 2, 1]) (yd [2, 1, 1]) :=
  ofWord _ _ [(3, 0), (2, 1), (1, 1), (1, 2), (0, 2)] (by rw [cellsL_ofRowLens]; decide)
    (by decide) [3, 2, 1, 2, 1] (by decide)

/-- **E Example 4.4**: `Ŝ = 001/012/02/3` (row word `302012001`), `N^<(Ŝ) = 18`, so
`sign(S) = (-1)^{18} = 1`. -/
theorem example_4_4 :
    S44.hatWord = [3, 0, 2, 0, 1, 2, 0, 0, 1] ∧ S44.Nlt = 18 ∧ S44.sign = 1 := by
  have h : S44.hatWord = [3, 0, 2, 0, 1, 2, 0, 0, 1] := by
    unfold SkewTableau.hatWord
    rw [rowCells_ofRowLens]
    decide
  have h2 : S44.Nlt = 18 := by unfold SkewTableau.Nlt; rw [h]; decide
  exact ⟨h, h2, by rw [SkewTableau.sign, h2]; norm_num⟩

theorem validW_single (p : ℕ × ℕ) {a : ℕ} (ha : 0 < a) : ValidW [p] [a] := by
  refine ⟨rfl, by simpa using ha, ?_, ?_⟩ <;>
  · intro i hi j hj _ h2
    simp only [List.length_singleton] at hi hj
    interval_cases i
    interval_cases j
    exact absurd h2 (lt_irrefl _)

/-- The skew tableau of shape `(1,1)/(1)` with entry `a`. -/
def Scol (a : ℕ) (ha : 0 < a) : SkewTableau (yd [1, 1]) (yd [1]) :=
  ofWord _ _ [(1, 0)] (by rw [cellsL_ofRowLens]; decide) (by decide) [a] (validW_single _ ha)

/-- The skew tableau of shape `(2)/(1)` with entry `a`. -/
def Srow (a : ℕ) (ha : 0 < a) : SkewTableau (yd [2]) (yd [1]) :=
  ofWord _ _ [(0, 1)] (by rw [cellsL_ofRowLens]; decide) (by decide) [a] (validW_single _ ha)

/-- **E Remark 4.5**: `(1,1)/(1)` and `(2)/(1)` both consist of a single box, but filled with
equal entries the two skew tableaux have opposite signs: `Ŝ = 0/a` has `N^< = 1` and
`Ŝ = 0a` has `N^< = 0`. -/
theorem remark_4_5 (a : ℕ) (ha : 0 < a) :
    (Scol a ha).sign = -1 ∧ (Srow a ha).sign = 1 ∧ (Scol a ha).sign = -(Srow a ha).sign := by
  have h1 : (Scol a ha).hatWord = [a, 0] := by
    unfold SkewTableau.hatWord
    rw [rowCells_ofRowLens, show rowCellsOf [1, 1] = [(1, 0), (0, 0)] by decide]
    simp only [List.map_cons, List.map_nil]
    have he : ∀ i j, (Scol a ha).entry i j = wordEntry (yd [1, 1]) (yd [1]) [(1, 0)] [a] i j :=
      fun _ _ => rfl
    simp only [he]
    unfold wordEntry
    rw [if_pos (by decide), if_neg (by decide), show idx [(1, 0)] (1, 0) = 0 by decide]
    rfl
  have h2 : (Srow a ha).hatWord = [0, a] := by
    unfold SkewTableau.hatWord
    rw [rowCells_ofRowLens, show rowCellsOf [2] = [(0, 0), (0, 1)] by decide]
    simp only [List.map_cons, List.map_nil]
    have he : ∀ i j, (Srow a ha).entry i j = wordEntry (yd [2]) (yd [1]) [(0, 1)] [a] i j :=
      fun _ _ => rfl
    simp only [he]
    unfold wordEntry
    rw [if_neg (by decide), if_pos (by decide), show idx [(0, 1)] (0, 1) = 0 by decide]
    rfl
  have e1 : (Scol a ha).sign = -1 := by
    rw [SkewTableau.sign, SkewTableau.Nlt, h1]
    simp [inversions, ha]
  have e2 : (Srow a ha).sign = 1 := by
    rw [SkewTableau.sign, SkewTableau.Nlt, h2]
    simp [inversions]
  exact ⟨e1, e2, by rw [e1, e2]⟩

/-! ## Example 4.13 at the level of tableaux -/

/-- **E Example 4.13**: for `S = ::1/:2/1` (`OddLRRule.exS2`), `A_S` is the displayed triangle
(`OddLRHive.exA`), and `Q_△(A_S) = 6 = N^<(S)`. -/
theorem example_4_13_tableau :
    OddLRHive.AS 3 OddLRRule.exS2 = OddLRHive.exA ∧ OddLRHive.Qtri (OddLRHive.AS 3 OddLRRule.exS2) = 6 ∧
      (OddLRRule.exS2.Nlt : ℤ) = OddLRHive.Qtri (OddLRHive.AS 3 OddLRRule.exS2) := by
  have hA : OddLRHive.AS 3 OddLRRule.exS2 = OddLRHive.exA := by
    funext x
    simp only [OddLRHive.AS, OddLRHive.SkewTab.rowCount, OddLRRule.shape321, rowLen_ofRowLens']
    revert x
    decide
  have hlr : IsLR OddLRRule.exS2 := by
    have : OddLRRule.exS2 ∈ lrTableaux OddLRRule.shape321 OddLRRule.shape21 OddLRRule.shape21 := by
      rw [OddLRRule.lrTableaux_ex]; simp
    exact (mem_lrTableaux.mp this).2
  refine ⟨hA, by rw [hA]; exact OddLRHive.example_4_13, ?_⟩
  refine OddLRHive.Nlt_eq_Qtri 3 _ hlr ?_
  by_contra h
  push_neg at h
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mpr h) (by decide)

/-! ## `sign(x₁x₂x₃, x₁x₃x₂) = -1` -/

open OddMath.SkewPolynomial in
/-- **E §4.2, p.13**: `sign(x₁x₂x₃, x₁x₃x₂) = -1` in `OPol_3` (the paper's `x_i` is
`generator (i-1)`). -/
theorem signBetween_example :
    signBetween (generator (0 : Fin 3) * generator 1 * generator 2)
      (generator (0 : Fin 3) * generator 2 * generator 1) = -1 := by
  have hY : generator (0 : Fin 3) * generator 1 * generator 2 =
      monomial (expSingle 0 + expSingle 1 + expSingle 2) 1 := by
    change mul (mul (generator (0 : Fin 3)) (generator 1)) (generator 2) = _
    rw [mul_generator]
    change mul (monomial _ _) (monomial (expSingle 2) 1) = _
    rw [mul_monomial]
    congr 1
  have hZ : generator (0 : Fin 3) * generator 2 * generator 1 =
      monomial (expSingle 0 + expSingle 1 + expSingle 2) (-1) := by
    change mul (mul (generator (0 : Fin 3)) (generator 2)) (generator 1) = _
    rw [mul_generator]
    change mul (monomial _ _) (monomial (expSingle 1) 1) = _
    rw [mul_monomial]
    congr 1
    exact add_right_comm _ _ _
  rw [hY, hZ]
  unfold signBetween
  have hne : monomial (expSingle (0 : Fin 3) + expSingle 1 + expSingle 2) (1 : ℤ) ≠
      monomial (expSingle 0 + expSingle 1 + expSingle 2) (-1) := by
    intro h
    have := Finsupp.single_injective _ h
    omega
  rw [if_neg hne, if_pos (by rw [monomial_neg, neg_neg])]

end OddMath.Frontier.OddLRExamples
