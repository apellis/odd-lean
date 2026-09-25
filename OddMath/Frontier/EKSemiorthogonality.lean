import OddMath.Frontier.EKMixedPairing
import OddMath.Frontier.DegreeShapes
import Mathlib.Combinatorics.Young.YoungDiagram

/-! EK 1107.5610v2 Proposition 2.14, over the actual integral radical quotient.
Rows/columns have their literal source order. Empty diagrams and zero parts are
allowed at matrix level; source compositions are positive lists. -/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKSemiorthogonality
open EKRadicalQuotient EKPairingMatrices EKMixedPairing

def hPartition (μ : YoungDiagram) : Q := (μ.rowLens.map EKElementaryQuotient.h).prod
def ePartition (μ : YoungDiagram) : Q := (μ.rowLens.map EKElementaryQuotient.e).prod

def ferrers {r : ℕ} (β : Fin r → ℕ) (c : ℕ) : Raw r c :=
  fun i j => if j.val < β i then 1 else 0

theorem sum_initial (n b : ℕ) :
    (∑ k : Fin n, if k.val < b then 1 else 0) = min b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, ih]
    split_ifs <;> omega

/-- If earlier columns are Ferrers columns, a row already full cannot accept
another strand. This is the integral row-capacity argument in EK p.17. -/
theorem column_capacity {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (M : Mat β α) (h01 : ∀ i j, M i j ≤ 1) (j : Fin c)
    (hprev : ∀ k : Fin c, k < j → ∀ i, M i k = ferrers β c i k) :
    ∀ i, M i j ≤ ferrers β c i j := by
  intro i
  by_cases hj : j.val < β i
  · simpa [ferrers, hj] using h01 i j
  · have hb : β i ≤ c := by omega
    have hle (k : Fin c) : ferrers β c i k ≤ M i k := by
      by_cases hk : k.val < β i
      · have hkj : k < j := by exact (show k.val < j.val by omega)
        rw [hprev k hkj i]
      · simp [ferrers, hk]
    have hs : (∑ k, ferrers β c i k) = ∑ k, M i k := by
      rw [show (∑ k, M i k) = β i from congrFun M.property.1 i]
      simpa [ferrers, min_eq_left hb] using sum_initial c (β i)
    have heq := (Finset.sum_eq_sum_iff_of_le (fun k (_ : k ∈ Finset.univ) => hle k)).mp hs
    have hjj := heq j (Finset.mem_univ j)
    exact le_of_eq hjj.symm

/-- Every column up to a prescribed bound is forced by equality of the column
margins with the Ferrers margins. No uniqueness hypothesis is assumed. -/
theorem columns_forced {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (M : Mat β α) (h01 : ∀ i j, M i j ≤ 1) (K : ℕ)
    (hcols : ∀ j : Fin c, j.val < K → α j = colSum (ferrers β c) j) :
    ∀ j : Fin c, j.val < K → ∀ i, M i j = ferrers β c i j := by
  intro j hj
  have aux : ∀ n, ∀ j : Fin c, j.val = n → n < K → ∀ i,
      M i j = ferrers β c i j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hjn hn
      have hp : ∀ k : Fin c, k < j → ∀ i, M i k = ferrers β c i k := by
        intro k hk
        apply ih k.val (by simpa [← hjn] using hk) k rfl
        exact lt_trans (by simpa [← hjn] using hk) hn
      have hle := column_capacity M h01 j hp
      have hs : (∑ i, M i j) = ∑ i, ferrers β c i j :=
        (congrFun M.property.2 j).trans (hcols j (by omega))
      exact fun i => (Finset.sum_eq_sum_iff_of_le
        (fun k (_ : k ∈ Finset.univ) => hle k)).mp hs i (Finset.mem_univ i)
  exact aux j.val j rfl hj

theorem ferrers_unique {r c : ℕ} {β : Fin r → ℕ}
    (M : Mat β (colSum (ferrers β c))) (h01 : ∀ i j, M i j ≤ 1) :
    (M : Raw r c) = ferrers β c := by
  funext i j
  exact columns_forced M h01 c (fun _ _ => rfl) j j.isLt i

/-- The first lexicographically larger column is impossible. -/
theorem no_matrix_first_larger {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (M : Mat β α) (h01 : ∀ i j, M i j ≤ 1) (j : Fin c)
    (hprev : ∀ k : Fin c, k < j → α k = colSum (ferrers β c) k)
    (hlarge : colSum (ferrers β c) j < α j) : False := by
  have hp := columns_forced M h01 j.val (fun k hk => hprev k hk)
  have hle := column_capacity M h01 j hp
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
  change colSum M j ≤ colSum (ferrers β c) j at hs
  rw [M.property.2] at hs
  omega

/-- Actual Young-diagram margins, without zero padding. -/
def rows (μ : YoungDiagram) : Fin (μ.colLen 0) → ℕ := fun i => μ.rowLen i

theorem ferrers_colSum (μ : YoungDiagram) (c : ℕ) (j : Fin c) :
    colSum (ferrers (rows μ) c) j = μ.colLen j := by
  have he (i : Fin (μ.colLen 0)) :
      (j.val < μ.rowLen i.val) ↔ i.val < μ.colLen j.val :=
    YoungDiagram.mem_iff_lt_rowLen.symm.trans YoungDiagram.mem_iff_lt_colLen
  simp only [colSum, ferrers, rows, he]
  rw [sum_initial, min_eq_left (μ.colLen_anti 0 j.val (Nat.zero_le _))]

theorem ferrers_rowSum (μ : YoungDiagram) :
    rowSum (ferrers (rows μ) (μ.rowLen 0)) = rows μ := by
  funext i
  exact (sum_initial _ _).trans
    (min_eq_left (μ.rowLen_anti 0 i.val (Nat.zero_le _)))

theorem rowLens_eq_ofFn (μ : YoungDiagram) : μ.rowLens = List.ofFn (rows μ) := by
  apply List.ext_getElem
  · simp [YoungDiagram.length_rowLens]
  · intro i hi hj
    simp [YoungDiagram.get_rowLens, rows]

theorem hPartition_eq_mixed (μ : YoungDiagram) :
    hPartition μ = mixed (rows μ) (fun _ => false) := by
  simp [hPartition, rowLens_eq_ofFn, mixed, List.map_ofFn, Function.comp_def]

theorem ePartition_eq_mixed (μ : YoungDiagram) :
    ePartition μ = mixed (rows μ) (fun _ => true) := by
  simp [ePartition, rowLens_eq_ofFn, mixed, List.map_ofFn, Function.comp_def]

/-- The literal strict northeast/southwest cell-pair count from EK p.16.
Each pair is counted once, with its northeast cell first. -/
def ell (μ : YoungDiagram) : ℕ :=
  ∑ p ∈ μ.cells, (μ.cells.filter (fun q => p.1 < q.1 ∧ q.2 < p.2)).card

private theorem sum_cells (μ : YoungDiagram) (f : ℕ × ℕ → ℕ) :
    ∑ p ∈ μ.cells, f p = ∑ i : Fin (μ.colLen 0), ∑ j : Fin (μ.rowLen 0),
      if (i.val,j.val) ∈ μ then f (i.val,j.val) else 0 := by
  have hsub : μ.cells ⊆ Finset.range (μ.colLen 0) ×ˢ Finset.range (μ.rowLen 0) := by
    intro p hp
    have hr := YoungDiagram.mem_iff_lt_colLen.mp hp
    have hc := YoungDiagram.mem_iff_lt_rowLen.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le hr (μ.colLen_anti 0 p.2 (Nat.zero_le _))),
      Finset.mem_range.mpr (lt_of_lt_of_le hc (μ.rowLen_anti 0 p.1 (Nat.zero_le _)))⟩
  calc
    _ = ∑ p ∈ μ.cells, if p ∈ μ then f p else 0 := by
      apply Finset.sum_congr rfl; intro p hp; exact (if_pos hp).symm
    _ = ∑ p ∈ Finset.range (μ.colLen 0) ×ˢ Finset.range (μ.rowLen 0),
        if p ∈ μ then f p else 0 := by
      apply Finset.sum_subset hsub
      intro p _ hp
      exact if_neg hp
    _ = _ := by
      rw [Finset.sum_product]
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl; intro i _
      exact Finset.sum_range _

private theorem ite_sum {ι : Type} [Fintype ι] (p : Prop) [Decidable p] (f : ι → ℕ) :
    (if p then ∑ i, f i else 0) = ∑ i, if p then f i else 0 := by
  by_cases h : p <;> simp [h]

theorem ell_eq_crossing (μ : YoungDiagram) :
    ell μ = crossing (ferrers (rows μ) (μ.rowLen 0)) := by
  unfold ell
  simp only [Finset.card_filter]
  rw [sum_cells]
  simp only [sum_cells]
  unfold crossing
  apply Finset.sum_congr rfl; intro i _
  simp only [ite_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro l _
  simp only [ferrers, rows, YoungDiagram.mem_iff_lt_rowLen, Fin.lt_def]
  split_ifs <;> simp_all

/-- The unique admissible Ferrers matrix for conjugate margins. -/
def ferrersMixed {r : ℕ} (β : Fin r → ℕ) (c : ℕ) (hb : ∀ i, β i ≤ c) :
    MixedMatrices β (fun _ => false) (colSum (ferrers β c)) (fun _ => true) :=
  ⟨⟨ferrers β c, by
      constructor
      · funext i; exact (sum_initial _ _).trans (min_eq_left (hb i))
      · rfl⟩, by intro i j _; simp only [ferrers]; split_ifs <;> omega⟩

theorem mixed_ferrers_pairing {r : ℕ} (β : Fin r → ℕ) (c : ℕ)
    (hb : ∀ i, β i ≤ c) :
    quotientPairing (mixed β (fun _ => false))
      (mixed (colSum (ferrers β c)) (fun _ => true)) =
      (-1 : ℤ)^crossing (ferrers β c) := by
  classical
  rw [quotientPairing_eq_restricted_matrices]
  rw [Finset.sum_eq_single (ferrersMixed β c hb)]
  · simp [ferrersMixed, blackPairs]
  · intro M _ hne
    exfalso
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact ferrers_unique M.val (fun i j => M.property i j (by simp))
  · simp

/-- EK Proposition 2.14(1), equation (2.20), with the source cell-pair sign. -/
theorem proposition_2_14_diagonal (μ : YoungDiagram) :
    quotientPairing (hPartition μ) (ePartition μ.transpose) = (-1 : ℤ)^ell μ := by
  have he : ePartition μ.transpose =
      mixed (colSum (ferrers (rows μ) (μ.rowLen 0))) (fun _ => true) := by
    rw [ePartition_eq_mixed]
    unfold rows
    rw [YoungDiagram.colLen_transpose]
    congr 1
    funext j
    rw [YoungDiagram.rowLen_transpose]
    exact (ferrers_colSum μ _ j).symm
  rw [hPartition_eq_mixed, he, ell_eq_crossing]
  exact mixed_ferrers_pairing _ _ (fun i => μ.rowLen_anti 0 i.val (Nat.zero_le _))

/-- Either coloring vanishes when the first nonmatching column is larger. -/
theorem pairing_first_larger {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (b : Bool) (j : Fin c)
    (hprev : ∀ k : Fin c, k < j → α k = colSum (ferrers β c) k)
    (hlarge : colSum (ferrers β c) j < α j) :
    quotientPairing (mixed β (fun _ => b)) (mixed α (fun _ => !b)) = 0 := by
  rw [quotientPairing_eq_restricted_matrices]
  apply Finset.sum_eq_zero
  intro M _
  exact (no_matrix_first_larger M.val
    (fun i k => M.property i k (by cases b <;> simp)) j hprev hlarge).elim

/-- A positive-list lexicographic comparison has a first strictly larger
entry, with omitted entries on the smaller side padded by zero. -/
theorem lex_first_larger {β α : List ℕ} (hlex : List.Lex (· < ·) β α)
    (hpos : ∀ a ∈ α, 0 < a) :
    ∃ j, j < α.length ∧
      (∀ k < j, β[k]?.getD 0 = α[k]?.getD 0) ∧
      β[j]?.getD 0 < α[j]?.getD 0 := by
  induction hlex with
  | nil =>
    refine ⟨0, by simp, ?_, ?_⟩
    · intro k hk; omega
    · simpa using hpos _ (by simp)
  | rel h =>
    refine ⟨0, by simp, ?_, ?_⟩
    · intro k hk; omega
    · simpa using h
  | @cons a β α h ih =>
    obtain ⟨j,hj,hprev,hlt⟩ := ih (fun x hx => hpos x (by simp [hx]))
    refine ⟨j+1, by simpa using hj, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero => simp
      | succ k => simpa using hprev k (by omega)
    · simpa using hlt

/-- Young row lengths extended by zero are the actual rowLen function. -/
theorem rowLens_getD (μ : YoungDiagram) (j : ℕ) :
    μ.rowLens[j]?.getD 0 = μ.rowLen j := by
  by_cases hj : j < μ.rowLens.length
  · rw [List.getElem?_eq_getElem hj]
    simp
  · have hz : μ.rowLen j = 0 := by
      have h : ¬ (j,0) ∈ μ := by
        rw [YoungDiagram.mem_iff_lt_colLen]
        simpa only [YoungDiagram.length_rowLens] using hj
      rw [YoungDiagram.mem_iff_lt_rowLen] at h
      omega
    rw [List.getElem?_eq_none (show μ.rowLens.length ≤ j by omega)]
    exact hz.symm

/-- Literal list words are the inherited mixed quotient words. -/
theorem list_word_eq_mixed (α : List ℕ) (b : Bool) :
    (α.map (fun n => if b then EKElementaryQuotient.e n else EKElementaryQuotient.h n)).prod =
      mixed (fun i : Fin α.length => α[i.val]) (fun _ => b) := by
  simp only [mixed, ← List.ofFn_getElem_eq_map]

/-- EK Proposition 2.14(2), (2.21), both color orders. Positivity is the
source composition convention. The result even holds without equal weight. -/
theorem proposition_2_14_vanishing (μ : YoungDiagram) (α : List ℕ)
    (hpos : ∀ a ∈ α, 0 < a) (hlex : List.Lex (· < ·) μ.transpose.rowLens α) :
    quotientPairing (hPartition μ) (α.map EKElementaryQuotient.e).prod = 0 ∧
    quotientPairing (ePartition μ) (α.map EKElementaryQuotient.h).prod = 0 := by
  obtain ⟨j,hj,hprev,hlt⟩ := lex_first_larger hlex hpos
  have hprev' (k : Fin α.length) (hk : k < (⟨j,hj⟩ : Fin α.length)) :
      α[k.val] = colSum (ferrers (rows μ) α.length) k := by
    have h := hprev k.val hk
    rw [rowLens_getD, YoungDiagram.rowLen_transpose,
      List.getElem?_eq_getElem k.isLt] at h
    simpa only [Option.getD_some, ferrers_colSum] using h.symm
  have hlt' : colSum (ferrers (rows μ) α.length) ⟨j,hj⟩ < α[j] := by
    rw [rowLens_getD, YoungDiagram.rowLen_transpose,
      List.getElem?_eq_getElem hj] at hlt
    simpa only [Option.getD_some, ferrers_colSum] using hlt
  have h0 := pairing_first_larger (rows μ) (fun i : Fin α.length => α[i.val]) false
    ⟨j,hj⟩ hprev' hlt'
  have h1 := pairing_first_larger (rows μ) (fun i : Fin α.length => α[i.val]) true
    ⟨j,hj⟩ hprev' hlt'
  constructor
  · rw [hPartition_eq_mixed]
    simpa only [← list_word_eq_mixed, Bool.not_false, Bool.true_eq, if_true] using h0
  · rw [ePartition_eq_mixed]
    simpa only [← list_word_eq_mixed, Bool.not_true, Bool.false_eq_true, if_false] using h1

private theorem transpose_rowLens_injective :
    Function.Injective (fun μ : YoungDiagram => μ.transpose.rowLens) := by
  intro μ ν h
  apply YoungDiagram.transpose_eq_iff.mp
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext h

private theorem triangular_independent (v dual : YoungDiagram → Q)
    (hdiag : ∀ μ, quotientPairing (v μ) (dual μ) ≠ 0)
    (htri : ∀ μ ν, List.Lex (· < ·) μ.transpose.rowLens ν.transpose.rowLens →
      quotientPairing (v μ) (dual ν) = 0) : LinearIndependent ℤ v := by
  classical
  rw [linearIndependent_iff']
  intro s g hz i hi
  by_contra hgi
  let t := s.filter (fun μ => g μ ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi,hgi⟩⟩
  obtain ⟨ν,hν,hmax⟩ := t.exists_max_image (fun μ => μ.transpose.rowLens) ht
  have hνs := (Finset.mem_filter.mp hν).1
  have hνg := (Finset.mem_filter.mp hν).2
  have hpair := congrArg (fun x : Q => quotientPairing x (dual ν)) hz
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, map_zero, LinearMap.zero_apply] at hpair
  rw [Finset.sum_eq_single ν] at hpair
  · exact hνg ((mul_eq_zero.mp hpair).resolve_right (hdiag ν))
  · intro μ hμ hne
    by_cases hg : g μ = 0
    · simp [hg]
    · have hμt : μ ∈ t := Finset.mem_filter.mpr ⟨hμ,hg⟩
      have hlt : μ.transpose.rowLens < ν.transpose.rowLens :=
        lt_of_le_of_ne (hmax μ hμt)
          (fun he => hne (transpose_rowLens_injective he))
      rw [htri μ ν hlt, mul_zero]
  · exact fun h => (h hνs).elim

/-- Integral independence follows from the unit-triangular mixed pairing,
not positive definiteness or a field/faithfulness assumption. -/
theorem hPartition_linearIndependent : LinearIndependent ℤ hPartition := by
  apply triangular_independent hPartition (fun μ => ePartition μ.transpose)
  · intro μ
    rw [proposition_2_14_diagonal]
    exact pow_ne_zero _ (by norm_num)
  · intro μ ν hlt
    exact (proposition_2_14_vanishing μ ν.transpose.rowLens
      ν.transpose.pos_of_mem_rowLens hlt).1

theorem ePartition_linearIndependent : LinearIndependent ℤ ePartition := by
  apply triangular_independent ePartition (fun μ => hPartition μ.transpose)
  · intro μ
    rw [quotientPairing_symm]
    have hd := proposition_2_14_diagonal μ.transpose
    rw [YoungDiagram.transpose_transpose] at hd
    rw [hd]
    exact pow_ne_zero _ (by norm_num)
  · intro μ ν hlt
    exact (proposition_2_14_vanishing μ ν.transpose.rowLens
      ν.transpose.pos_of_mem_rowLens hlt).2

/-- The fixed-degree family uses the existing exhaustive shape index. -/
theorem degree_hPartition_linearIndependent (d : ℕ) :
    LinearIndependent ℤ (fun μ : DegreeShapes.DegreeShape d => hPartition μ.val) :=
  hPartition_linearIndependent.comp _ Subtype.val_injective

theorem degree_ePartition_linearIndependent (d : ℕ) :
    LinearIndependent ℤ (fun μ : DegreeShapes.DegreeShape d => ePartition μ.val) :=
  ePartition_linearIndependent.comp _ Subtype.val_injective

/-- Zero generators are units; removing arbitrary leading, interior or
trailing zero padding does not change either literal quotient word. Lexicographic
composition hypotheses in Proposition 2.14 concern positive parts only. -/
theorem word_filter_zero (α : List ℕ) (b : Bool) :
    ((α.filter (· ≠ 0)).map
      (fun n => if b then EKElementaryQuotient.e n else EKElementaryQuotient.h n)).prod =
    (α.map (fun n => if b then EKElementaryQuotient.e n else EKElementaryQuotient.h n)).prod := by
  induction α with
  | nil => simp
  | cons a α ih =>
    by_cases ha : a = 0
    · subst a
      cases b <;> simpa [EKElementaryQuotient.e, EKElementaryQuotient.h,
        CompleteElementary.elementary_zero, CompleteElementary.h_zero] using ih
    · simpa [ha] using congrArg
        (fun x => (if b then EKElementaryQuotient.e a else EKElementaryQuotient.h a) * x) ih

end OddMath.Frontier.EKSemiorthogonality
