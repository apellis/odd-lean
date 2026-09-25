import OddMath.Frontier.RowBump

/-!
Actual cell-row extraction and the first strictly greater input decision.
Reading order is bottom-to-top; the insertion step starts at row zero.
The output of this module is a word, not a certified inserted tableau.
-/
namespace OddMath.Frontier.TableauRowStep

open TableauSign TableauEvaluation TableauRowWord

noncomputable def regionWord (n : ℕ) {μ : YoungDiagram}
    (T : PositiveTableau μ) (hT : InAlphabet n T)
    (p : ℕ → Bool) : List (Fin n) :=
  ((rowCells μ).attach.filter (fun c => p c.val.1)).map fun c =>
    ⟨T.entry c.val.1 c.val.2 - 1, by
      have hc := (mem_rowCells μ c.val).mp c.property
      have hp := T.positive (by simpa using hc)
      have hb := hT c.val hc
      change T.entry c.val.1 c.val.2 ≤ n at hb
      change 0 < T.entry c.val.1 c.val.2 at hp
      omega⟩

noncomputable def row (n : ℕ) {μ : YoungDiagram}
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) : List (Fin n) :=
  regionWord n T hT (fun i => decide (i = r))
noncomputable def below (n : ℕ) {μ : YoungDiagram}
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) : List (Fin n) :=
  regionWord n T hT (fun i => decide (r < i))
noncomputable def above (n : ℕ) {μ : YoungDiagram}
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) : List (Fin n) :=
  regionWord n T hT (fun i => decide (i < r))

private theorem label_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => i.val + 1) := by
  intro a b h
  apply Fin.ext
  change a.val + 1 = b.val + 1 at h
  omega

private theorem region_labels (n : ℕ) {μ : YoungDiagram}
    (T : PositiveTableau μ) (hT : InAlphabet n T) (p : ℕ → Bool) :
    (regionWord n T hT p).map (fun i => i.val + 1) =
      ((rowCells μ).filter (fun c => p c.1)).map (fun c => T.entry c.1 c.2) := by
  unfold regionWord
  rw [List.map_map]
  have he :
      (((rowCells μ).attach.filter (fun c => p c.val.1)).map
        (fun c => T.entry c.val.1 c.val.2 - 1 + 1)) =
      (((rowCells μ).attach.filter (fun c => p c.val.1)).map
        (fun c => T.entry c.val.1 c.val.2)) := by
    apply List.map_congr_left
    intro c _
    have hc := (mem_rowCells μ c.val).mp c.property
    have hp := T.positive (by simpa using hc)
    change 0 < T.entry c.val.1 c.val.2 at hp
    change T.entry c.val.1 c.val.2 - 1 + 1 = T.entry c.val.1 c.val.2
    omega
  change (((rowCells μ).attach.filter (fun c => p c.val.1)).map
    (fun c => T.entry c.val.1 c.val.2 - 1 + 1)) = _
  rw [he]
  have hv := List.attach_map_val (l := rowCells μ) (f := id)
  have h := congrArg (fun l : List (ℕ × ℕ) =>
      (l.filter (fun c => p c.1)).map (fun c => T.entry c.1 c.2)) hv
  simpa only [List.filter_map, List.map_map, Function.comp_def, List.map_id] using h

theorem rowCells_row (μ : YoungDiagram) (r : ℕ) :
    (rowCells μ).filter (fun p => decide (p.1 = r)) =
      (List.range (μ.rowLen r)).map (fun c => (r, c)) := by
  letI : IsAntisymm (ℕ × ℕ) RowLE := ⟨by
    intro a b hab hba
    rcases a with ⟨i,j⟩
    rcases b with ⟨k,l⟩
    unfold RowLE at hab hba
    simp only [Prod.mk.injEq]
    constructor <;> omega⟩
  apply List.eq_of_perm_of_sorted (r := RowLE)
  · apply (List.perm_ext_iff_of_nodup ((rowCells_nodup μ).filter _)
      ((List.nodup_range).map (by intro a b h; simpa using h))).mpr
    intro p
    rcases p with ⟨i,c⟩
    simp only [List.mem_filter, mem_rowCells, decide_eq_true_eq, List.mem_map,
      List.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨hc, rfl⟩
      exact ⟨c, (YoungDiagram.mem_iff_lt_rowLen).mp hc, rfl, rfl⟩
    · rintro ⟨j, hj, rfl, rfl⟩
      exact ⟨(YoungDiagram.mem_iff_lt_rowLen).mpr hj, rfl⟩
  · exact (rowCells_sorted μ).filter _
  · apply List.pairwise_map.mpr
    apply (List.pairwise_lt_range (n := μ.rowLen r)).imp
    intro a b h
    exact Or.inr ⟨rfl, h.le⟩

theorem row_labels (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) :
    (row n T hT r).map (fun i => i.val + 1) =
      (List.range (μ.rowLen r)).map (fun c => T.entry r c) := by
  rw [row, region_labels, rowCells_row, List.map_map]
  rfl

theorem row_length (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) :
    (row n T hT r).length = μ.rowLen r := by
  simpa using congrArg List.length (row_labels n μ T hT r)

theorem row_sorted (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) :
    (row n T hT r).Sorted (· ≤ ·) := by
  have hs : ((List.range (μ.rowLen r)).map (fun c => T.entry r c)).Sorted (· ≤ ·) := by
    apply List.pairwise_map.mpr
    apply (List.pairwise_lt_range (n := μ.rowLen r)).imp_of_mem
    intro a b _ hb hab
    exact T.toSemistandardYoungTableau.row_weak_of_le hab.le
      ((YoungDiagram.mem_iff_lt_rowLen).mpr (List.mem_range.mp hb))
  rw [← row_labels n μ T hT r] at hs
  change List.Pairwise _ _ at hs
  rw [List.pairwise_map] at hs
  exact hs.imp (by intro a b h; exact Nat.le_of_add_le_add_right h)

-- The three filters are consecutive only because the cells are RowLE-sorted.
private theorem cells_split (l : List (ℕ × ℕ)) (r : ℕ) (hs : l.Sorted RowLE) :
    l = l.filter (fun c => decide (r < c.1)) ++
      (l.filter (fun c => decide (c.1 = r)) ++
        l.filter (fun c => decide (c.1 < r))) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    obtain ⟨ho, ht⟩ := List.sorted_cons.mp hs
    have hi := ih ht
    by_cases hb : r < c.1
    · have he : c.1 ≠ r := by omega
      have ha : ¬ c.1 < r := by omega
      simpa only [List.filter_cons, hb, he, ha, decide_true, decide_false,
        Bool.true_eq, Bool.false_eq_true, if_true, if_false, List.cons_append] using
        congrArg (List.cons c) hi
    · have hz : l.filter (fun d => decide (r < d.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro d hd
        have h := ho d hd
        unfold RowLE at h
        simp only [decide_eq_true_eq]
        omega
      by_cases he : c.1 = r
      · have ha : ¬ c.1 < r := by omega
        simpa only [List.filter_cons, hb, he, ha, decide_true, decide_false,
          Bool.true_eq, Bool.false_eq_true, if_true, if_false, List.cons_append,
          Nat.lt_irrefl, hz, List.nil_append] using congrArg (List.cons c) hi
      · have ha : c.1 < r := by omega
        have hez : l.filter (fun d => decide (d.1 = r)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro d hd
          have h := ho d hd
          unfold RowLE at h
          simp only [decide_eq_true_eq]
          omega
        simpa only [List.filter_cons, hb, he, ha, decide_true, decide_false,
          Bool.true_eq, Bool.false_eq_true, if_true, if_false, List.cons_append,
          hz, hez, List.nil_append] using congrArg (List.cons c) hi

theorem rowFinWord_split (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) :
    rowFinWord n T hT =
      below n T hT r ++ (row n T hT r ++ above n T hT r) := by
  apply (List.map_inj_right (f := fun i : Fin n => i.val + 1)
    (fun _ _ h => label_injective n h)).mp
  rw [rowFinWord_labels, List.map_append, List.map_append]
  simp only [below, row, above, region_labels, rowWord]
  have h := congrArg (List.map (fun c : ℕ × ℕ => T.entry c.1 c.2))
    (cells_split (rowCells μ) r (rowCells_sorted μ))
  simpa only [List.map_append] using h

theorem rowFinWord_top (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) :
    rowFinWord n T hT = below n T hT 0 ++ row n T hT 0 := by
  have hz : above n T hT 0 = [] := by
    simp [above, regionWord]
  simpa only [hz, List.append_nil] using rowFinWord_split n μ T hT 0

/-- All fields certify the original input, never the output identity. -/
inductive FirstGreater {n : ℕ} (w : List (Fin n)) (a : Fin n) : Type
  | append (ha : ∀ x ∈ w, x ≤ a) : FirstGreater w a
  | bump (u : List (Fin n)) (b : Fin n) (v : List (Fin n))
      (hsplit : w = u ++ (b :: v))
      (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) : FirstGreater w a

/-- Structural recursion: equality goes in the prefix, never bumps. -/
def firstGreater (n : ℕ) (w : List (Fin n)) (a : Fin n) : FirstGreater w a :=
  match w with
  | [] => .append (by simp)
  | x :: xs =>
    if h : a < x then .bump [] x xs rfl (by simp) h
    else
      match firstGreater n xs a with
      | .append ha => .append (by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact le_of_not_gt h
          · exact ha y hy)
      | .bump u b v hsplit hu hab => .bump (x :: u) b v
          (by simp only [List.cons_append, hsplit])
          (by
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact le_of_not_gt h
            · exact hu y hy) hab

theorem topRow_step (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (a : Fin n) :
    let l := below n T hT 0
    let w := row n T hT 0
    ((∀ x ∈ w, x ≤ a) ∧
      (w ++ [a]).Sorted (· ≤ ·) ∧
      rowPolynomial n T hT * PlacticEvaluation.tildeGenerator a =
        PlacticEvaluation.toSkew n (OddPlactic.word n (l ++ (w ++ [a])))) ∨
    (∃ (u : List (Fin n)) (b : Fin n) (v : List (Fin n)),
      w = u ++ (b :: v) ∧ (∀ x ∈ u, x ≤ a) ∧ a < b ∧
      (u ++ (a :: v)).Sorted (· ≤ ·) ∧
      rowPolynomial n T hT * PlacticEvaluation.tildeGenerator a =
        (-1 : ℤ) ^ (u.length + v.length) •
          PlacticEvaluation.toSkew n
            (OddPlactic.word n (l ++ (b :: (u ++ (a :: v)))))) := by
  dsimp only
  have hs := row_sorted n μ T hT 0
  have ht := rowFinWord_top n μ T hT
  cases firstGreater n (row n T hT 0) a with
  | append ha =>
    refine Or.inl ⟨ha, RowBump.row_append_sorted n _ a hs ha, ?_⟩
    rw [rowPolynomial, ht, ← PlacticEvaluation.toSkew_q n a, ← map_mul]
    congr 1
    simp only [OddPlactic.word_append, OddPlactic.word_cons, OddPlactic.word_nil,
      mul_one, mul_assoc]
  | bump u b v hsplit hu hab =>
    have hs' : (u ++ (b :: v)).Sorted (· ≤ ·) := hsplit ▸ hs
    refine Or.inr ⟨u, b, v, hsplit, hu, hab,
      RowBump.row_bump_sorted n u v a b hs' hu hab, ?_⟩
    exact RowBump.rowPolynomial_bump n μ T hT (below n T hT 0) u v a b
      (ht.trans (congrArg (List.append (below n T hT 0)) hsplit)) hs' hu hab

theorem row_step_context (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ)
    (l z u v : List (Fin n)) (a b : Fin n)
    (hsplit : row n T hT r = u ++ (b :: v))
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    OddPlactic.word n (l ++ ((row n T hT r ++ [a]) ++ z)) =
      (-1 : ℤ) ^ (u.length + v.length) •
        OddPlactic.word n (l ++ ((b :: (u ++ (a :: v))) ++ z)) := by
  rw [hsplit]
  exact RowBump.row_bump_context n l z u v a b
    (hsplit ▸ row_sorted n μ T hT r) hu hab

end OddMath.Frontier.TableauRowStep
