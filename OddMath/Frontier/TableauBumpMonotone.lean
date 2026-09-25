import OddMath.Frontier.TableauInsertion

/-!
Fulton, Young Tableaux §1.1, Row Bumping Lemma (1), printed pp.9–10.
The second weakly larger input follows a strictly rightward route. The proofs
below compare the installed firstGreater decisions, not a surrogate algorithm.
-/
namespace OddMath.Frontier.TableauBumpMonotone
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion
  TableauBumpBoundary TableauRunGeometry

 theorem firstGreater_append (n : ℕ) (w : List (Fin n)) (a : Fin n)
    (ha : ∀ x ∈ w, x ≤ a) : firstGreater n w a = .append ha := by
  cases he : firstGreater n w a with
  | append hb => rfl
  | bump u c v hs hu hac =>
    have hca := ha c (by simp [hs])
    exact False.elim (not_lt_of_ge hca hac)

-- All letters skipped before the first bump, and its replacement, are ≤ b.
-- Any letter selected later is in the old suffix and hence ≥ the old bump.
theorem modified_step (n : ℕ) (u v : List (Fin n)) (a b c : Fin n)
    (hu : ∀ x ∈ u, x ≤ a) (hab : a ≤ b) (hv : ∀ x ∈ v, c ≤ x) :
    match firstGreater n (u ++ (a :: v)) b with
    | .append _ => u.length < (u ++ (a :: v)).length
    | .bump p d _ _ _ _ => u.length < p.length ∧ c ≤ d := by
  induction u with
  | nil =>
    have hba : ¬ b < a := not_lt_of_ge hab
    simp only [List.nil_append, firstGreater, hba, ↓reduceDIte]
    cases he : firstGreater n v b with
    | append hb => simp
    | bump p d q hs hp hbd =>
      exact ⟨by simp, hv d (by simp [hs])⟩
  | cons x xs ih =>
    have hxb : ¬ b < x := not_lt_of_ge (le_trans (hu x (by simp)) hab)
    have hi := ih (fun y hy => hu y (by simp [hy]))
    simp only [List.cons_append, firstGreater, hxb, ↓reduceDIte]
    cases he : firstGreater n (xs ++ (a :: v)) b with
    | append hb => simp
    | bump p d q hs hp hbd =>
      simp only [he] at hi
      exact ⟨Nat.succ_lt_succ hi.1, hi.2⟩

theorem last_cons (c : ℕ) (cs : List ℕ) (h : cs ≠ []) :
    (c :: cs).getLast! = cs.getLast! := by
  cases cs with
  | nil => exact False.elim (h rfl)
  | cons d ds => simp

-- The installed adjacent-row boundary bounds the next selected column.
theorem next_head_le (n : ℕ) (u v : List (Fin n)) (a c : Fin n)
    (ws : List (List (Fin n)))
    (hc : ColumnBelow (u ++ (c :: v)) (ws[0]?.getD []))
    (hu : ∀ x ∈ u, x ≤ a) (hac : a < c) :
    (runRows n ws c).columns.head! ≤ u.length := by
  have hb := bump_boundary n u v a c (ws[0]?.getD []) hc hu hac
  cases ws with
  | nil => simp [runRows]
  | cons w ws =>
    simp only [List.getElem?_cons_zero, Option.getD_some] at hb
    cases he : firstGreater n w c with
    | append ha =>
      simp only [he] at hb
      simpa [runRows, he] using hb.1
    | bump p d q hs hp hcd =>
      simp only [he] at hb
      simpa [runRows, he] using hb.1

-- A single insertion route never moves right; only genuine column geometry
-- is needed here. This handles the unequal-stopping-row endpoint case.
theorem last_le_head (n : ℕ) (rs : List (List (Fin n))) (a : Fin n)
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    (runRows n rs a).columns.getLast! ≤ (runRows n rs a).columns.head! := by
  induction rs generalizing a with
  | nil => simp [runRows]
  | cons w ws ih =>
    have ht : ∀ r : ℕ, ColumnBelow (ws[r]?.getD []) (ws[r+1]?.getD []) := by
      intro r
      simpa using hc (r+1)
    have hh : ColumnBelow w (ws[0]?.getD []) := by simpa using hc 0
    cases he : firstGreater n w a with
    | append ha => simp [runRows, he]
    | bump u c v hs hu hac =>
      have hb := next_head_le n u v a c ws (hs ▸ hh) hu hac
      simpa only [runRows, he, List.head!_cons,
        last_cons _ _ (runRows_columns_nonempty n ws c)] using le_trans (ih c ht) hb

-- Raw-row induction: row sorting propagates the bumped-letter inequality;
-- column geometry is used only when the second route terminates first.
theorem run_pair_le (n : ℕ) (rs : List (List (Fin n))) (a b : Fin n)
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD []))
    (hab : a ≤ b) :
    let q1 := runRows n rs a
    let q2 := runRows n q1.output b
    q2.columns.length ≤ q1.columns.length ∧
      (∀ r : ℕ, r < q2.columns.length →
        q1.columns[r]?.getD 0 < q2.columns[r]?.getD 0) ∧
      q1.columns.getLast! < q2.columns.getLast! := by
  induction rs generalizing a b with
  | nil =>
    simp only [runRows, firstGreater, not_lt_of_ge hab, ↓reduceDIte]
    refine ⟨by simp, ?_, by simp⟩
    intro r hr
    have hr0 : r = 0 := by simpa using hr
    subst r
    simp
  | cons w ws ih =>
    have hw := hs w (by simp)
    have hst : ∀ z ∈ ws, z.Sorted (· ≤ ·) :=
      fun z hz => hs z (List.mem_cons_of_mem w hz)
    have hct : ∀ r : ℕ, ColumnBelow (ws[r]?.getD []) (ws[r+1]?.getD []) := by
      intro r
      simpa using hc (r+1)
    have hh : ColumnBelow w (ws[0]?.getD []) := by simpa using hc 0
    cases he : firstGreater n w a with
    | append ha =>
      have hb : ∀ x ∈ w ++ [a], x ≤ b := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact le_trans (ha x hx) hab
        · simpa using (List.mem_singleton.mp hx ▸ hab)
      have he2 := firstGreater_append n (w ++ [a]) b hb
      simp only [runRows, he, he2]
      refine ⟨by simp, ?_, by simp⟩
      intro r hr
      have hr0 : r = 0 := by simpa using hr
      subst r
      simp
    | bump u c v hsplit hu hac =>
      have hv : ∀ x ∈ v, c ≤ x :=
        (List.sorted_cons.mp (List.pairwise_append.mp (hsplit ▸ hw)).2.1).1
      have hm := modified_step n u v a b c hu hab hv
      have hlast := le_trans (last_le_head n ws c hct)
        (next_head_le n u v a c ws (hsplit ▸ hh) hu hac)
      cases he2 : firstGreater n (u ++ (a :: v)) b with
      | append hb =>
        simp only [he2] at hm
        simp only [runRows, he, he2]
        refine ⟨by simp, ?_, ?_⟩
        · intro r hr
          have hr0 : r = 0 := by simpa using hr
          subst r
          simp
        · rw [last_cons _ _ (runRows_columns_nonempty n ws c)]
          simpa using lt_of_le_of_lt hlast hm
      | bump p d q hsplit2 hp hbd =>
        simp only [he2] at hm
        have hi := ih c d hst hct hm.2
        simp only [runRows, he, he2]
        refine ⟨Nat.succ_le_succ hi.1, ?_, ?_⟩
        · intro r hr
          cases r with
          | zero => simpa using hm.1
          | succ r =>
            exact hi.2.1 r (by simpa using hr)
        · rw [last_cons _ _ (runRows_columns_nonempty n ws c),
            last_cons _ _ (runRows_columns_nonempty n (runRows n ws c).output d)]
          exact hi.2.2

theorem insert_pair_le (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a b : Fin n) :
  let I := TableauInsertion.insert n μ T hT a
  let J := TableauInsertion.insert n I.shape I.tableau I.bounded b
  let q1 := runRows n (rows n T hT) a
  let q2 := runRows n (rows n I.tableau I.bounded) b
  a ≤ b → q2.columns.length ≤ q1.columns.length ∧
    (∀ r : ℕ, r < q2.columns.length →
      (q1.columns[r]?.getD 0) < (q2.columns[r]?.getD 0)) ∧
    I.newCell.2 < J.newCell.2 ∧ J.newCell.1 ≤ I.newCell.1 := by
  dsimp only
  intro hab
  have h := run_pair_le n (rows n T hT) a b
    (rows_sorted n μ T hT) (rows_columns n μ T hT) hab
  simp only [TableauInsertion.insert_newCell, newCell, TableauInsertion.insert_rows]
  exact ⟨h.1, h.2.1, h.2.2, Nat.sub_le_sub_right h.1 1⟩

end OddMath.Frontier.TableauBumpMonotone
