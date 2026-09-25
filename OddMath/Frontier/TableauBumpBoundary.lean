import OddMath.Frontier.TableauRowRecursion

/-!
Adjacent-row carry boundary, not a full insertion/output-tableau theorem.
Fulton, Young Tableaux §1.1, printed pp. 7–8 (frozen preview PDF pp. 19–20):
the bumped letter stays in its column or moves left, and the entry above is
no larger than the incoming letter. We use the installed firstGreater.
-/
namespace OddMath.Frontier.TableauBumpBoundary
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion

def ColumnBelow {n : ℕ} (upper lower : List (Fin n)) : Prop :=
  ∃ hlen : lower.length ≤ upper.length,
    ∀ (c : ℕ) (hc : c < lower.length),
      upper[c]'(lt_of_lt_of_le hc hlen) < lower[c]'hc

private theorem row_label_at (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r c : ℕ) (hc : c < (row n T hT r).length) :
    (row n T hT r)[c].val + 1 = T.entry r c := by
  have hm := row_labels n μ T hT r
  have hr : c < μ.rowLen r := by simpa only [row_length] using hc
  have he := congrArg (fun l : List ℕ => l[c]?) hm
  simpa [List.getElem?_eq_getElem, hc, hr] using he

theorem rows_columnBelow (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r : ℕ) :
    ColumnBelow (row n T hT r) (row n T hT (r+1)) := by
  have hl : (row n T hT (r+1)).length ≤ (row n T hT r).length := by
    simpa only [row_length] using μ.rowLen_anti r (r+1) (by omega)
  refine ⟨hl, ?_⟩
  intro c hc
  have hu := row_label_at n μ T hT r c (lt_of_lt_of_le hc hl)
  have hd := row_label_at n μ T hT (r+1) c hc
  have hm : (r+1, c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr
    (by simpa only [row_length] using hc)
  have ht := T.toSemistandardYoungTableau.col_strict (by omega : r < r+1) hm
  change T.entry r c < T.entry (r+1) c at ht
  change (row n T hT r)[c].val < (row n T hT (r+1))[c].val
  omega

private theorem below_nil {n : ℕ} (upper : List (Fin n)) : ColumnBelow upper [] := by
  exact ⟨by simp, by simp⟩

private theorem below_cons {n : ℕ} (x y : Fin n) (xs ys : List (Fin n)) :
    ColumnBelow (x :: xs) (y :: ys) ↔ x < y ∧ ColumnBelow xs ys := by
  constructor
  · rintro ⟨hl, hp⟩
    refine ⟨?_, ⟨by simpa using hl, ?_⟩⟩
    · simpa using hp 0 (by simp)
    · intro c hc
      simpa using hp (c+1) (by simpa using hc)
  · rintro ⟨hxy, hl, hp⟩
    refine ⟨by simpa using hl, ?_⟩
    intro c hc
    cases c with
    | zero => simpa using hxy
    | succ c => simpa using hp c (by simpa using hc)

-- Lowering the replaced upper entry preserves every old strict column.
private theorem lower_upper {n : ℕ} (u v lower : List (Fin n)) (a b : Fin n)
    (hab : a ≤ b) (hcol : ColumnBelow (u ++ (b :: v)) lower) :
    ColumnBelow (u ++ (a :: v)) lower := by
  induction u generalizing lower with
  | nil =>
    cases lower with
    | nil => exact below_nil _
    | cons y ys =>
      obtain ⟨hy, ht⟩ := (below_cons b y v ys).mp hcol
      exact (below_cons a y v ys).mpr ⟨lt_of_le_of_lt hab hy, ht⟩
  | cons x xs ih =>
    cases lower with
    | nil => exact below_nil _
    | cons y ys =>
      obtain ⟨hy, ht⟩ := (below_cons x y (xs ++ (b :: v)) ys).mp hcol
      exact (below_cons x y (xs ++ (a :: v)) ys).mpr ⟨hy, ih ys ht⟩

theorem bump_boundary (n : ℕ) (u v : List (Fin n)) (a b : Fin n)
    (lower : List (Fin n)) (hcol : ColumnBelow (u ++ (b :: v)) lower)
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    match firstGreater n lower b with
    | .append _ => lower.length ≤ u.length ∧
        ColumnBelow (u ++ (a :: v)) (lower ++ [b])
    | .bump p _c q _ _ _ => p.length ≤ u.length ∧
        ColumnBelow (u ++ (a :: v)) (p ++ (b :: q)) := by
  induction u generalizing lower with
  | nil =>
    cases lower with
    | nil =>
      exact ⟨by simp, (below_cons a b v []).mpr ⟨hab, below_nil v⟩⟩
    | cons y ys =>
      obtain ⟨hby, ht⟩ := (below_cons b y v ys).mp hcol
      simp only [firstGreater, hby, ↓reduceDIte, List.nil_append, List.length_nil]
      exact ⟨le_rfl, (below_cons a b v ys).mpr ⟨hab, ht⟩⟩
  | cons x xs ih =>
    have hx : x ≤ a := hu x (by simp)
    have hxs : ∀ z ∈ xs, z ≤ a := fun z hz => hu z (by simp [hz])
    cases lower with
    | nil =>
      exact ⟨by simp, (below_cons x b (xs ++ (a :: v)) []).mpr
        ⟨lt_of_le_of_lt hx hab, below_nil _⟩⟩
    | cons y ys =>
      obtain ⟨hxy, ht⟩ := (below_cons x y (xs ++ (b :: v)) ys).mp hcol
      by_cases hby : b < y
      · simp only [firstGreater, hby, ↓reduceDIte, List.nil_append]
        exact ⟨by simp, (below_cons x b (xs ++ (a :: v)) ys).mpr
          ⟨lt_of_le_of_lt hx hab, lower_upper xs v ys a b hab.le ht⟩⟩
      · have hi := ih ys ht hxs
        simp only [firstGreater, hby, ↓reduceDIte]
        cases he : firstGreater n ys b with
        | append ha =>
          simp only [he] at hi ⊢
          exact ⟨Nat.succ_le_succ hi.1,
            (below_cons x y (xs ++ (a :: v)) (ys ++ [b])).mpr ⟨hxy, hi.2⟩⟩
        | bump p c q hs hp hbc =>
          simp only [he] at hi ⊢
          exact ⟨Nat.succ_le_succ hi.1,
            (below_cons x y (xs ++ (a :: v)) (p ++ (b :: q))).mpr ⟨hxy, hi.2⟩⟩

theorem tableau_bump_boundary (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r : ℕ) (a : Fin n) :
    match firstGreater n (row n T hT r) a with
    | .append _ => True
    | .bump u b v _ _ _ =>
      match firstGreater n (row n T hT (r+1)) b with
      | .append _ => (row n T hT (r+1)).length ≤ u.length ∧
          ColumnBelow (u ++ (a :: v)) (row n T hT (r+1) ++ [b])
      | .bump p _c q _ _ _ => p.length ≤ u.length ∧
          ColumnBelow (u ++ (a :: v)) (p ++ (b :: q)) := by
  cases firstGreater n (row n T hT r) a with
  | append ha => trivial
  | bump u b v hs hu hab =>
    dsimp only
    have hb := bump_boundary n u v a b (row n T hT (r+1))
      (hs ▸ rows_columnBelow n μ T hT r) hu hab
    cases he : firstGreater n (row n T hT (r+1)) b <;> simpa only [he] using hb

end OddMath.Frontier.TableauBumpBoundary
