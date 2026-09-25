import OddMath.Frontier.TableauInsertion

/-!
Fulton, Young Tableaux §1.1, Row Bumping Lemma (2), printed pp. 9–10.
For strictly descending successive inputs, the second actual route is weakly
left and strictly longer. Equality of the route columns is allowed.
The raw comparison needs only firstGreater's prefix certificate, not sortedness.
The terminal column comparison uses the genuine Young diagrams and exact cell
insertion; it is not inferred from a default value at a missing path position.
-/
namespace OddMath.Frontier.TableauBumpStrict
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion

-- In the modified row, a smaller input bumps at or before the newly inserted a.
-- The bumped letter is at most a, hence strictly below the old bumped letter.
private theorem split_compare (n : ℕ) (u v p q : List (Fin n)) (a c b : Fin n)
    (he : u ++ (a :: v) = p ++ (c :: q))
    (hp : ∀ x ∈ p, x ≤ b) (hba : b < a) (hu : ∀ x ∈ u, x ≤ a) :
    p.length ≤ u.length ∧ c ≤ a := by
  induction u generalizing p with
  | nil =>
    cases p with
    | nil =>
      have h := (List.cons.inj he).1
      exact ⟨by simp, h ▸ le_rfl⟩
    | cons d p =>
      have h := (List.cons.inj he).1
      have hd := hp d (by simp)
      exact False.elim ((not_le_of_gt hba) (h ▸ hd))
  | cons x u ih =>
    cases p with
    | nil =>
      have h := (List.cons.inj he).1
      exact ⟨by simp, h ▸ hu x (by simp)⟩
    | cons d p =>
      have h := (List.cons.inj he).2
      obtain ⟨hl, hc⟩ := ih p h
        (fun y hy => hp y (List.mem_cons_of_mem d hy))
        (fun y hy => hu y (List.mem_cons_of_mem x hy))
      exact ⟨by simpa using hl, hc⟩

private theorem run_pair_gt (n : ℕ) (rs : List (List (Fin n))) (a b : Fin n)
    (hba : b < a) :
    (runRows n rs a).columns.length <
        (runRows n (runRows n rs a).output b).columns.length ∧
      (∀ r : ℕ, r < (runRows n rs a).columns.length →
        ((runRows n (runRows n rs a).output b).columns[r]?.getD 0) ≤
          ((runRows n rs a).columns[r]?.getD 0)) := by
  induction rs generalizing a b with
  | nil =>
    simp [runRows, firstGreater, hba]
  | cons w ws ih =>
    cases hfirst : firstGreater n w a with
    | append ha =>
      cases hsecond : firstGreater n (w ++ [a]) b with
      | append hb =>
        exact False.elim ((not_le_of_gt hba) (hb a (by simp)))
      | bump p c q hs hp hbc =>
        have hc := split_compare n w [] p q a c b hs hp hba ha
        have hn := List.length_pos_iff.mpr (runRows_columns_nonempty n ws c)
        simp only [runRows, hfirst, hsecond, List.length_singleton, List.length_cons,
          List.length_nil]
        refine ⟨by omega, ?_⟩
        intro r hr
        have hz : r = 0 := by omega
        subst r
        simpa using hc.1
    | bump u c v hs hu hac =>
      cases hsecond : firstGreater n (u ++ (a :: v)) b with
      | append hb =>
        exact False.elim ((not_le_of_gt hba) (hb a (by simp)))
      | bump p d q ht hp hbd =>
        have hc := split_compare n u v p q a d b ht hp hba hu
        have hi := ih c d (lt_of_le_of_lt hc.2 hac)
        simp only [runRows, hfirst, hsecond, List.length_cons]
        refine ⟨by omega, ?_⟩
        intro r hr
        cases r with
        | zero => simpa using hc.1
        | succ r =>
          simpa using hi.2 r (by omega)

-- Exact one-cell growth of genuine diagrams supplies the terminal column order.
-- If q were to the right of p and below it, the cell (q.row,p.col) would already
-- belong to μ, forcing p to belong to μ, contradicting its being the first new cell.
private theorem added_cells_columns (μ ν ξ : YoungDiagram) (p q : ℕ × ℕ)
    (hp : p ∉ μ.cells)
    (hν : ν.cells = TableauInsertion.insertCell p μ.cells)
    (hξ : ξ.cells = TableauInsertion.insertCell q ν.cells)
    (hr : p.1 < q.1) : q.2 ≤ p.2 := by
  by_contra h
  have hc : p.2 < q.2 := Nat.lt_of_not_ge h
  have hq : q ∈ ξ.cells := by simp [hξ, TableauInsertion.insertCell]
  have hmid : (q.1, p.2) ∈ ξ.cells :=
    ξ.up_left_mem (le_refl q.1) hc.le hq
  rw [hξ] at hmid
  rcases Finset.mem_insert.mp hmid with he | hmid
  · have hec := congrArg Prod.snd he
    exact (Nat.ne_of_lt hc) hec
  rw [hν] at hmid
  rcases Finset.mem_insert.mp hmid with he | hmid
  · have her := congrArg Prod.fst he
    exact (Nat.ne_of_lt hr) her.symm
  exact hp (μ.up_left_mem hr.le (le_refl p.2) hmid)

/-- The strict-input half of the Row Bumping Lemma for genuine bounded tableaux. -/
theorem insert_pair_gt (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a b : Fin n) :
  let I := TableauInsertion.insert n μ T hT a
  let J := TableauInsertion.insert n I.shape I.tableau I.bounded b
  let q1 := runRows n (rows n T hT) a
  let q2 := runRows n (rows n I.tableau I.bounded) b
  b < a → q1.columns.length < q2.columns.length ∧
    (∀ r : ℕ, r < q1.columns.length →
      (q2.columns[r]?.getD 0) ≤ (q1.columns[r]?.getD 0)) ∧
    J.newCell.2 ≤ I.newCell.2 ∧ I.newCell.1 < J.newCell.1 := by
  dsimp only
  intro hba
  have hraw := run_pair_gt n (rows n T hT) a b hba
  rw [← TableauInsertion.insert_rows n μ T hT a] at hraw
  have hn := List.length_pos_iff.mpr (runRows_columns_nonempty n (rows n T hT) a)
  have hrow : (TableauInsertion.insert n μ T hT a).newCell.1 <
      (TableauInsertion.insert n (TableauInsertion.insert n μ T hT a).shape
        (TableauInsertion.insert n μ T hT a).tableau
        (TableauInsertion.insert n μ T hT a).bounded b).newCell.1 := by
    simp only [TableauInsertion.insert_newCell, newCell]
    omega
  have hI := TableauInsertion.insert_cells n μ T hT a
  have hJ := TableauInsertion.insert_cells n (TableauInsertion.insert n μ T hT a).shape
    (TableauInsertion.insert n μ T hT a).tableau
    (TableauInsertion.insert n μ T hT a).bounded b
  exact ⟨hraw.1, hraw.2, added_cells_columns _ _ _ _ _ hI.1 hI.2 hJ.2 hrow, hrow⟩

#print axioms split_compare
#print axioms run_pair_gt
#print axioms added_cells_columns
#print axioms insert_pair_gt
end OddMath.Frontier.TableauBumpStrict
