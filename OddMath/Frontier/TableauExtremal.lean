import OddMath.Frontier.TableauPolynomial
import OddMath.Frontier.OddSymmetricKernel

/-!
# Genuine extremal-shape RAW tableau comparisons
Ellis arXiv:1111.3932v1 Definition 3.3 and Lemma 3.5. The inherited
polynomial is the literal row-word sum, without a Schur shape prefactor.
-/
namespace OddMath.Frontier.TableauExtremal
open TableauSign TableauContent TableauRowWord TableauEvaluation TableauPolynomial
open FiniteCompleteElementary FiniteCompleteElementary.FiniteWords
open OddMath.SkewPolynomial
open scoped BigOperators
noncomputable section

/-- The actual one-row Young diagram, including the empty case. -/
def rowShape (k : ℕ) : YoungDiagram where
  cells := {0} ×ˢ Finset.range k
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_range] at hb ⊢
    exact ⟨by have := hab.1; omega, lt_of_le_of_lt hab.2 hb.2⟩

/-- The actual one-column Young diagram, including the empty case. -/
def columnShape (k : ℕ) : YoungDiagram where
  cells := Finset.range k ×ˢ {0}
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_range] at hb ⊢
    exact ⟨lt_of_le_of_lt hab.1 hb.1, by have := hab.2; omega⟩

@[simp] theorem mem_rowShape (k i j : ℕ) : (i,j) ∈ rowShape k ↔ i = 0 ∧ j < k := by
  simp [rowShape, eq_comm, and_comm]
@[simp] theorem mem_columnShape (k i j : ℕ) : (i,j) ∈ columnShape k ↔ j = 0 ∧ i < k := by
  simp [columnShape, and_comm, eq_comm]
@[simp] theorem rowShape_zero : rowShape 0 = ⊥ := by
  apply YoungDiagram.ext
  simp [rowShape]
@[simp] theorem columnShape_zero : columnShape 0 = ⊥ := by
  apply YoungDiagram.ext
  simp [columnShape]

abbrev Bounded (n : ℕ) (μ : YoungDiagram) := {T : PositiveTableau μ // InAlphabet n T}

/-- Fill actual row cells with positive labels; all off-shape entries remain zero. -/
def rowTableau {n k : ℕ} (f : Weak n k) : PositiveTableau (rowShape k) where
  entry i j := if h : i = 0 ∧ j < k then (f.val ⟨j,h.2⟩).val + 1 else 0
  row_weak' := by
    intro i a b hab hb
    obtain ⟨rfl,hbk⟩ := (mem_rowShape k i b).mp hb
    have ha : a < k := lt_trans hab hbk
    simpa [ha,hbk] using Nat.add_le_add_right
      (show (f.val ⟨a,ha⟩).val ≤ (f.val ⟨b,hbk⟩).val from f.property (le_of_lt hab)) 1
  col_strict' := by
    intro a b j hab hb
    have := ((mem_rowShape k b j).mp hb).1
    omega
  zeros' := by
    intro i j h
    simpa only [mem_rowShape] using (dif_neg (by simpa using h))
  positive := by
    intro i j h
    have h := (mem_rowShape k i j).mp h
    simp [h]

/-- Fill actual column cells top-to-bottom; the later row word reverses this order. -/
def columnTableau {n k : ℕ} (f : Strict n k) : PositiveTableau (columnShape k) where
  entry i j := if h : j = 0 ∧ i < k then (f.val ⟨i,h.2⟩).val + 1 else 0
  row_weak' := by
    intro i a b hab hb
    have := ((mem_columnShape k i b).mp hb).1
    omega
  col_strict' := by
    intro a b j hab hb
    obtain ⟨rfl,hbk⟩ := (mem_columnShape k b j).mp hb
    have ha : a < k := lt_trans hab hbk
    simpa [ha,hbk] using Nat.add_lt_add_right
      (show (f.val ⟨a,ha⟩).val < (f.val ⟨b,hbk⟩).val from f.property hab) 1
  zeros' := by
    intro i j h
    simpa only [mem_columnShape] using (dif_neg (by simpa using h))
  positive := by
    intro i j h
    have h := (mem_columnShape k i j).mp h
    simp [h]

@[simp] theorem rowTableau_entry {n k : ℕ} (f : Weak n k) (j : Fin k) :
    (rowTableau f).entry 0 j = (f.val j).val + 1 := by
  change (if h : 0 = 0 ∧ j.val < k then (f.val ⟨j,h.2⟩).val + 1 else 0) = _
  simp only [j.isLt, and_self, ↓reduceDIte]
@[simp] theorem columnTableau_entry {n k : ℕ} (f : Strict n k) (i : Fin k) :
    (columnTableau f).entry i 0 = (f.val i).val + 1 := by
  change (if h : 0 = 0 ∧ i.val < k then (f.val ⟨i,h.2⟩).val + 1 else 0) = _
  simp only [i.isLt, and_self, ↓reduceDIte]

theorem rowTableau_bounded {n k : ℕ} (f : Weak n k) : InAlphabet n (rowTableau f) := by
  rintro ⟨i,j⟩ h
  obtain ⟨rfl,hj⟩ := (mem_rowShape k i j).mp h
  change (rowTableau f).entry 0 (⟨j,hj⟩ : Fin k) ≤ n
  rw [rowTableau_entry]
  exact Nat.succ_le_of_lt (f.val ⟨j,hj⟩).isLt

theorem columnTableau_bounded {n k : ℕ} (f : Strict n k) :
    InAlphabet n (columnTableau f) := by
  rintro ⟨i,j⟩ h
  obtain ⟨rfl,hi⟩ := (mem_columnShape k i j).mp h
  change (columnTableau f).entry (⟨i,hi⟩ : Fin k) 0 ≤ n
  rw [columnTableau_entry]
  exact Nat.succ_le_of_lt (f.val ⟨i,hi⟩).isLt

/-- Read positive row entries back into the finite weak-word alphabet. -/
def rowLetters {n k : ℕ} (T : Bounded n (rowShape k)) : Weak n k :=
  ⟨fun j => ⟨T.val.entry 0 j - 1, by
    have hp := T.val.positive ((mem_rowShape k 0 j).mpr ⟨rfl,j.isLt⟩)
    have hb := T.property (0,j) ((mem_rowShape k 0 j).mpr ⟨rfl,j.isLt⟩)
    change 0 < T.val.entry 0 j at hp
    change T.val.entry 0 j ≤ n at hb
    omega⟩, by
    intro a b hab
    exact Nat.sub_le_sub_right
      (T.val.toSemistandardYoungTableau.row_weak_of_le hab
        ((mem_rowShape k 0 b).mpr ⟨rfl,b.isLt⟩)) 1⟩

/-- Read positive column entries top-to-bottom into the finite strict-word alphabet. -/
def columnLetters {n k : ℕ} (T : Bounded n (columnShape k)) : Strict n k :=
  ⟨fun i => ⟨T.val.entry i 0 - 1, by
    have hp := T.val.positive ((mem_columnShape k i 0).mpr ⟨rfl,i.isLt⟩)
    have hb := T.property (i,0) ((mem_columnShape k i 0).mpr ⟨rfl,i.isLt⟩)
    change 0 < T.val.entry i 0 at hp
    change T.val.entry i 0 ≤ n at hb
    omega⟩, by
    intro a b hab
    have hp := T.val.positive ((mem_columnShape k a 0).mpr ⟨rfl,a.isLt⟩)
    have hs := T.val.toSemistandardYoungTableau.col_strict hab
      ((mem_columnShape k b 0).mpr ⟨rfl,b.isLt⟩)
    change T.val.entry a 0 - 1 < T.val.entry b 0 - 1
    change T.val.entry a 0 < T.val.entry b 0 at hs
    omega⟩

/-- A genuine equivalence, not an assumed tableau/word identification. -/
def rowEquiv (n k : ℕ) : Bounded n (rowShape k) ≃ Weak n k where
  toFun := rowLetters
  invFun f := ⟨rowTableau f,rowTableau_bounded f⟩
  left_inv T := by
    apply Subtype.ext
    apply ext_cells
    rintro ⟨i,j⟩ h
    obtain ⟨rfl,hj⟩ := (mem_rowShape k i j).mp h
    have hp := T.val.positive ((mem_rowShape k 0 j).mpr ⟨rfl,hj⟩)
    simp only [rowTableau, rowLetters, and_self, true_and, hj, dif_pos,
      Nat.sub_add_cancel (by omega : 1 ≤ T.val.entry 0 j)]
  right_inv f := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    change (rowTableau f).entry 0 j - 1 = (f.val j).val
    rw [rowTableau_entry, Nat.add_sub_cancel]

def columnEquiv (n k : ℕ) : Bounded n (columnShape k) ≃ Strict n k where
  toFun := columnLetters
  invFun f := ⟨columnTableau f,columnTableau_bounded f⟩
  left_inv T := by
    apply Subtype.ext
    apply ext_cells
    rintro ⟨i,j⟩ h
    obtain ⟨rfl,hi⟩ := (mem_columnShape k i j).mp h
    have hp := T.val.positive ((mem_columnShape k i 0).mpr ⟨rfl,hi⟩)
    simp only [columnTableau, columnLetters, and_self, true_and, hi, dif_pos,
      Nat.sub_add_cancel (by omega : 1 ≤ T.val.entry i 0)]
  right_inv f := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (columnTableau f).entry i 0 - 1 = (f.val i).val
    rw [columnTableau_entry, Nat.add_sub_cancel]

/-- Reading order is antisymmetric as well as total. -/
instance rowLE_antisymm : IsAntisymm (ℕ × ℕ) RowLE := ⟨by
  intro a b hab hba
  apply Prod.ext <;> unfold RowLE at hab hba <;> omega⟩

theorem rowCells_row (k : ℕ) : rowCells (rowShape k) =
    List.ofFn (fun j : Fin k => (0,j.val)) := by
  apply List.eq_of_perm_of_sorted _ (rowCells_sorted _) _
  · apply (List.perm_ext_iff_of_nodup (rowCells_nodup _) (List.nodup_ofFn.mpr ?_)).mpr
    · rintro ⟨i,j⟩
      simp only [mem_rowCells, YoungDiagram.mem_cells, mem_rowShape, List.mem_ofFn,
        Prod.mk.injEq]
      constructor
      · rintro ⟨rfl,hj⟩
        exact ⟨⟨j,hj⟩,rfl,rfl⟩
      · rintro ⟨a,ha,hj⟩
        exact ⟨ha.symm,hj ▸ a.isLt⟩
    · intro a b h
      exact Fin.ext (congrArg Prod.snd h)
  · apply List.sorted_ofFn_iff.mpr
    intro a b hab
    exact Or.inr ⟨rfl,le_of_lt hab⟩

theorem rowCells_column (k : ℕ) : rowCells (columnShape k) =
    (List.ofFn (fun i : Fin k => (i.val,0))).reverse := by
  apply List.eq_of_perm_of_sorted _ (rowCells_sorted _) _
  · apply (List.perm_ext_iff_of_nodup (rowCells_nodup _) (List.nodup_reverse.mpr
      (List.nodup_ofFn.mpr ?_))).mpr
    · rintro ⟨i,j⟩
      simp only [mem_rowCells, YoungDiagram.mem_cells, mem_columnShape, List.mem_reverse,
        List.mem_ofFn, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl,hi⟩
        exact ⟨⟨i,hi⟩,rfl,rfl⟩
      · rintro ⟨a,hi,hj⟩
        exact ⟨hj.symm,hi ▸ a.isLt⟩
    · intro a b h
      exact Fin.ext (congrArg Prod.fst h)
  · apply List.pairwise_reverse.mpr
    apply List.sorted_ofFn_iff.mpr
    intro a b hab
    exact Or.inl hab

/-- Actual source row word; repetitions are retained. -/
theorem rowWord_row {n k : ℕ} (f : Weak n k) :
    rowWord (rowTableau f) = List.ofFn (fun j => (f.val j).val + 1) := by
  rw [rowWord,rowCells_row,List.map_ofFn]
  congr 1
  funext j
  exact rowTableau_entry f j

/-- Source bottom-to-top reading reverses the strictly increasing column. -/
theorem rowWord_column {n k : ℕ} (f : Strict n k) :
    rowWord (columnTableau f) = (List.ofFn (fun i => (f.val i).val + 1)).reverse := by
  rw [rowWord,rowCells_column,List.map_reverse,List.map_ofFn]
  congr 2
  funext i
  exact columnTableau_entry f i

theorem rowFinWord_row {n k : ℕ} (f : Weak n k) :
    rowFinWord n (rowTableau f) (rowTableau_bounded f) = List.ofFn f.val := by
  apply List.map_injective_iff.mpr (show Function.Injective (fun i : Fin n => i.val + 1)
    from fun a b h => Fin.ext (by change a.val + 1 = b.val + 1 at h; omega))
  rw [rowFinWord_labels,rowWord_row,List.map_ofFn]
  rfl

theorem rowFinWord_column {n k : ℕ} (f : Strict n k) :
    rowFinWord n (columnTableau f) (columnTableau_bounded f) =
      (List.ofFn f.val).reverse := by
  apply List.map_injective_iff.mpr (show Function.Injective (fun i : Fin n => i.val + 1)
    from fun a b h => Fin.ext (by change a.val + 1 = b.val + 1 at h; omega))
  rw [rowFinWord_labels,rowWord_column,List.map_reverse,List.map_ofFn]
  rfl

/-- Weakly increasing words have no strict inversions, even with repetitions. -/
theorem inversions_of_sorted (l : List ℕ) (hl : l.Sorted (· ≤ ·)) : inversions l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    have hf : l.filter (fun b => b < a) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro b hb
      simpa using not_lt_of_ge (ha b hb)
    simp [inversions,hf,ih hl]

/-- Every pair in a strictly decreasing word contributes exactly one inversion. -/
theorem inversions_of_strictAnti (l : List ℕ) (hl : l.Sorted (· > ·)) :
    inversions l = l.length.choose 2 := by
  induction l with
  | nil => simp [inversions]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    have hf : l.filter (fun b => b < a) = l := by
      apply List.filter_eq_self.mpr
      intro b hb
      simpa using ha b hb
    simp [inversions,hf,ih hl,Nat.choose_succ_succ]

/-- The reversed product sign is proved in the actual skew algebra through PBW.
Distinctness is essential; it follows from strict increase, not square-zero. -/
theorem reverse_tildeProduct {n k : ℕ} (f : Strict n k) :
    (((List.ofFn f.val).reverse).map PlacticEvaluation.tildeGenerator).prod =
      (-1 : ℤ) ^ (k.choose 2) •
        (List.ofFn (fun i => PlacticEvaluation.tildeGenerator (f.val i))).prod := by
  have hs : (List.ofFn (fun i => (f.val i).val)).Sorted (· ≤ ·) := by
    apply List.sorted_ofFn_iff.mpr
    intro i j hij
    exact f.property.monotone (le_of_lt hij)
  have hr : (List.ofFn (fun i => (f.val i).val)).reverse.Sorted (· > ·) := by
    apply List.pairwise_reverse.mpr
    apply List.sorted_ofFn_iff.mpr
    intro i j hij
    exact f.property hij
  rw [← PlacticEvaluation.toSkew_word,wordPolynomial_eq]
  have he := wordPolynomial_eq (List.ofFn f.val)
  rw [PlacticEvaluation.toSkew_word,List.map_ofFn] at he
  simp only [Function.comp_def] at he
  rw [he]
  simp only [List.count_reverse,List.map_reverse,List.map_ofFn,Function.comp_def,
    List.sum_reverse,inversions_of_sorted _ hs,inversions_of_strictAnti _ hr,
    List.length_reverse,List.length_ofFn,zero_add,pow_add]
  simp only [monomial,Finsupp.smul_single,smul_eq_mul]

/-- Literal row evaluation equals the weak word's ordered product. -/
theorem rowPolynomial_row {n k : ℕ} (f : Weak n k) :
    rowPolynomial n (rowTableau f) (rowTableau_bounded f) =
      (List.ofFn (fun i => PlacticEvaluation.tildeGenerator (f.val i))).prod := by
  rw [rowPolynomial,rowFinWord_row,PlacticEvaluation.toSkew_word,List.map_ofFn]
  rfl

/-- Literal column evaluation carries the full reversal sign. -/
theorem rowPolynomial_column {n k : ℕ} (f : Strict n k) :
    rowPolynomial n (columnTableau f) (columnTableau_bounded f) =
      (-1 : ℤ) ^ (k.choose 2) •
        (List.ofFn (fun i => PlacticEvaluation.tildeGenerator (f.val i))).prod := by
  rw [rowPolynomial,rowFinWord_column,PlacticEvaluation.toSkew_word,reverse_tildeProduct]

/-- Membership in the inherited finite domain is exactly the genuine alphabet bound. -/
def boundedEquiv (n : ℕ) (μ : YoungDiagram) :
    {T : PositiveTableau μ // T ∈ tableauxInAlphabet n μ} ≃ Bounded n μ :=
  Equiv.subtypeEquivRight (fun T => mem_tableauxInAlphabet n T)

/-- Reindex the ACTUAL inherited finite SSYT sum by the proved row equivalence. -/
theorem tableauPolynomial_row (n k : ℕ) :
    tableauPolynomial n (rowShape k) = completePoly n k := by
  classical
  rw [tableauPolynomial,Finset.attach_eq_univ,completePoly_eq_weakSum,weakSum]
  let e := (boundedEquiv n (rowShape k)).trans (rowEquiv n k)
  symm
  apply Fintype.sum_equiv e.symm
  intro f
  exact (rowPolynomial_row f).symm

/-- Reindex the ACTUAL inherited finite SSYT sum, retaining the column reversal sign. -/
theorem tableauPolynomial_column (n k : ℕ) :
    tableauPolynomial n (columnShape k) =
      (-1 : ℤ) ^ (k.choose 2) • elementaryPoly n k := by
  classical
  rw [tableauPolynomial,Finset.attach_eq_univ,elementaryPoly_eq_strictSum,strictSum,
    Finset.smul_sum]
  let e := (boundedEquiv n (columnShape k)).trans (columnEquiv n k)
  symm
  apply Fintype.sum_equiv e.symm
  intro f
  exact (rowPolynomial_column f).symm

/-- Actual all-size row tableau polynomials lie in the actual joint kernel. -/
theorem tableauPolynomial_row_mem (n k : ℕ) :
    tableauPolynomial (n+2) (rowShape k) ∈ OddSymmetricKernel.kernelSubring n := by
  rw [tableauPolynomial_row]
  exact OddSymmetricKernel.complete_mem n k

/-- The column reversal scalar is an integer, so kernel subring closure applies. -/
theorem tableauPolynomial_column_mem (n k : ℕ) :
    tableauPolynomial (n+2) (columnShape k) ∈ OddSymmetricKernel.kernelSubring n := by
  rw [tableauPolynomial_column]
  exact (OddSymmetricKernel.kernelSubring n).zsmul_mem
    (OddSymmetricKernel.elementary_mem n k) _

theorem tableauPolynomial_column_eq_zero {n k : ℕ} (h : n < k) :
    tableauPolynomial n (columnShape k) = 0 := by
  rw [tableauPolynomial_column,elementaryPoly_eq_zero_of_lt h,smul_zero]

@[simp] theorem tableauPolynomial_row_zero (n : ℕ) :
    tableauPolynomial n (rowShape 0) = 1 := by simp
@[simp] theorem tableauPolynomial_column_zero (n : ℕ) :
    tableauPolynomial n (columnShape 0) = 1 := by simp

@[simp] theorem tableauPolynomial_row_alphabet_zero (k : ℕ) :
    tableauPolynomial 0 (rowShape (k+1)) = 0 := by
  rw [tableauPolynomial_row,completePoly_eq_weakSum,weakSum_empty]
@[simp] theorem tableauPolynomial_column_alphabet_zero (k : ℕ) :
    tableauPolynomial 0 (columnShape (k+1)) = 0 :=
  tableauPolynomial_column_eq_zero (by omega)

/-- Arbitrary noncommutative integer expressions in BOTH actual tableau families. -/
def tableauKernelEvaluation (n : ℕ) : FreeAlgebra ℤ (Bool × ℕ) →+*
    OddSymmetricKernel.kernelSubring n :=
  (FreeAlgebra.lift ℤ (fun j => if j.1 then
    ⟨tableauPolynomial (n+2) (columnShape j.2),tableauPolynomial_column_mem n j.2⟩ else
    ⟨tableauPolynomial (n+2) (rowShape j.2),tableauPolynomial_row_mem n j.2⟩)).toRingHom

/-- The unrestricted evaluation is an independent lift into the actual skew ring. -/
def tableauEvaluation (n : ℕ) : FreeAlgebra ℤ (Bool × ℕ) →+* SkewPolynomial (n+2) :=
  (FreeAlgebra.lift ℤ (fun j => if j.1 then
    tableauPolynomial (n+2) (columnShape j.2) else
    tableauPolynomial (n+2) (rowShape j.2))).toRingHom

theorem subtype_comp_tableauKernelEvaluation (n : ℕ) :
    (OddSymmetricKernel.kernelSubring n).subtype.comp (tableauKernelEvaluation n) =
      tableauEvaluation n := by
  apply RingHom.ext
  intro a
  induction a using FreeAlgebra.induction with
  | grade0 z => simp
  | grade1 j =>
    simp only [RingHom.comp_apply,tableauKernelEvaluation,tableauEvaluation,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,FreeAlgebra.lift_ι_apply]
    split <;> rfl
  | add a b ha hb => simp only [map_add,ha,hb]
  | mul a b ha hb => simp only [map_mul,ha,hb]

theorem tableauEvaluation_mem (n : ℕ) (a : FreeAlgebra ℤ (Bool × ℕ)) :
    tableauEvaluation n a ∈ OddSymmetricKernel.kernelSubring n := by
  rw [← subtype_comp_tableauKernelEvaluation]
  exact (tableauKernelEvaluation n a).property

end
end OddMath.Frontier.TableauExtremal
