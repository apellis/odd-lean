import OddMath.Frontier.TableauReverseRun

/-!
Both inverse laws for the installed finite row recursions.
Fulton, Young Tableaux §1.1, printed p.8 / frozen preview PDF20,
lines700–709: upward reverse bumping at the rightmost STRICTLY smaller
entry recovers the original tableau and letter. Rows and path are top-first;
Fin n values label positive entries by val+1. No algorithm is redefined here.
-/
namespace OddMath.Frontier.TableauReverseRunInverse
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion
  TableauReverseRow TableauReverseRun TableauBumpBoundary TableauCorner

private theorem last_cons (cs : List ℕ) (k : ℕ) (h : cs ≠ []) :
    (k :: cs).getLast! = cs.getLast! := by
  cases cs with
  | nil => exact False.elim (h rfl)
  | cons j js => simp

theorem reverse_after_runRows (n : ℕ) (rs : List (List (Fin n))) (a : Fin n)
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·)) (hn : ∀ w ∈ rs, w ≠ []) :
    reverseRows n (runRows n rs a).output (newCell n rs a).1 (newCell n rs a).2 =
      some ⟨rs, a, (runRows n rs a).columns⟩ := by
  induction rs generalizing a with
  | nil => simp [runRows, newCell, reverseRows]
  | cons w ws ih =>
    have hst : ∀ z ∈ ws, z.Sorted (· ≤ ·) := fun z hz => hs z (by simp [hz])
    have hnt : ∀ z ∈ ws, z ≠ [] := fun z hz => hn z (by simp [hz])
    have hw : w.length ≠ 0 := by simpa using hn w (by simp)
    have hl := reverse_after_forward n w a (hs w (by simp))
    cases hd : firstGreater n w a with
    | append ha =>
      simp [newCell, runRows, hd, reverseRows, hw]
    | bump u b v hsplit hu hab =>
      simp only [hd] at hl
      have hi := ih b hst hnt
      have hne := runRows_columns_nonempty n ws b
      have hp := List.length_pos_iff.mpr hne
      have he : (runRows n ws b).columns.length =
          ((runRows n ws b).columns.length - 1) + 1 := by omega
      simp only [newCell, runRows, hd, List.length_cons, Nat.add_sub_cancel,
        last_cons _ _ hne]
      rw [he]
      simp only [newCell] at hi
      simp only [reverseRows, hi]
      simp [hl]

private theorem runRows_append (n : ℕ) (w : List (Fin n))
    (ws : List (List (Fin n))) (a : Fin n) (ha : ∀ x ∈ w, x ≤ a) :
    runRows n (w::ws) a = ⟨(w ++ [a])::ws, [w.length], 0⟩ := by
  cases hd : firstGreater n w a with
  | append _ => simp [runRows, hd]
  | bump u b v hw _ hab =>
    have hb := ha b (by simp [hw])
    exact False.elim (not_lt.mpr hb hab)

private theorem split_last {n : ℕ} (w : List (Fin n)) (c : ℕ)
    (he : w.length = c+1) : ∃ b, w[c]? = some b ∧ w = w.take c ++ [b] := by
  have hc : c < w.length := by omega
  refine ⟨w[c], by simp [hc], ?_⟩
  rw [List.take_concat_get', ← he, List.take_length]

-- The recursion itself needs no column relation; the public theorem retains
-- the installed six-premise contract and uses its geometry for the new corner.
private theorem reconstruct (n : ℕ) (rs : List (List (Fin n))) (r c : ℕ)
    (q : ReverseRun n) (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hn : ∀ w ∈ rs, w ≠ []) (hr : r < rs.length)
    (he : (rs[r]?.getD []).length = c+1) (hb : (rs[r+1]?.getD []).length ≤ c)
    (hq : reverseRows n rs r c = some q) :
    (runRows n q.output q.letter).output = rs ∧
      (runRows n q.output q.letter).columns = q.columns := by
  induction r generalizing rs q with
  | zero =>
    cases rs with
    | nil => simp at hr
    | cons w ws =>
      have he' : w.length = c+1 := by simpa using he
      obtain ⟨b,hget,hw⟩ := split_last w c he'
      have hlen : (w.take c).length = c := by simp [List.length_take,he']
      by_cases hz : c = 0
      · have hws : ws = [] := by
          cases ws with
          | nil => rfl
          | cons v vs =>
            have hv := hn v (by simp)
            have hvz : v.length = 0 := by simpa [hz] using hb
            exact False.elim (hv (List.length_eq_zero_iff.mp hvz))
        subst ws
        subst c
        simp only [reverseRows, hget, if_pos rfl, Option.some.injEq] at hq
        cases hq
        have hw' : w = [b] := by simpa using hw
        simp [runRows,hw']
      · simp only [reverseRows, hget, if_neg hz, Option.some.injEq] at hq
        cases hq
        have hle : ∀ x ∈ w.take c, x ≤ b := by
          have hsorted := hs w (by simp)
          rw [hw] at hsorted
          exact fun x hx => (List.pairwise_append.mp hsorted).2.2 x hx b (by simp)
        rw [runRows_append n (w.take c) ws b hle]
        simp [← hw,hlen]
  | succ r ih =>
    cases rs with
    | nil => simp at hr
    | cons w ws =>
      have hst : ∀ z ∈ ws, z.Sorted (· ≤ ·) := fun z hz => hs z (by simp [hz])
      have hnt : ∀ z ∈ ws, z ≠ [] := fun z hz => hn z (by simp [hz])
      cases ht : reverseRows n ws r c with
      | none => simp [reverseRows,ht] at hq
      | some t =>
        cases hv : reverseStep n w t.letter with
        | none => simp [reverseRows,ht,hv] at hq
        | some triple =>
          rcases triple with ⟨v,a,k⟩
          simp only [reverseRows,ht] at hq
          simp [hv] at hq
          cases hq
          have hi := ih ws t hst hnt (by simpa using hr)
            (by simpa using he) (by simpa using hb) ht
          have hl := forward_after_reverse n w v t.letter a k (hs w (by simp)) hv
          cases hd : firstGreater n v a with
          | append _ => simp only [hd] at hl
          | bump u b z _ _ _ =>
            simp only [hd] at hl
            obtain ⟨hout, hb', hk⟩ := hl
            subst b
            simpa [runRows,hd,hout,hk] using hi

theorem runRows_after_reverse (n : ℕ) (rs : List (List (Fin n))) (r c : ℕ)
    (q : ReverseRun n) (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ j, ColumnBelow (rs[j]?.getD []) (rs[j+1]?.getD []))
    (hn : ∀ w ∈ rs, w ≠ []) (hr : r < rs.length)
    (he : (rs[r]?.getD []).length = c+1) (hb : (rs[r+1]?.getD []).length ≤ c)
    (hq : reverseRows n rs r c = some q) :
    (runRows n q.output q.letter).output = rs ∧
    (runRows n q.output q.letter).columns = q.columns ∧
    newCell n q.output q.letter = (r,c) := by
  obtain ⟨hout,hcols⟩ := reconstruct n rs r c q hs hn hr he hb hq
  obtain ⟨t,ht,_,_,_,_,hlen,_,hlast,_⟩ := reverseRows_geometry n rs r c hs hc hn hr he hb
  have hqt : t = q := Option.some.inj (ht.symm.trans hq)
  subst t
  refine ⟨hout,hcols,?_⟩
  simp [newCell,hcols,hlen,hlast]

theorem reverseRows_count (n : ℕ) (rs : List (List (Fin n))) (r c : ℕ)
    (q : ReverseRun n) (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ j, ColumnBelow (rs[j]?.getD []) (rs[j+1]?.getD []))
    (hn : ∀ w ∈ rs, w ≠ []) (hr : r < rs.length)
    (he : (rs[r]?.getD []).length = c+1) (hb : (rs[r+1]?.getD []).length ≤ c)
    (hq : reverseRows n rs r c = some q) (i : Fin n) :
    q.output.flatten.count i + (if i = q.letter then 1 else 0) = rs.flatten.count i := by
  have h := runRows_count n q.output q.letter i
  rw [(runRows_after_reverse n rs r c q hs hc hn hr he hb hq).1] at h
  exact h.symm

theorem tableau_reverse_after_runRows (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (a : Fin n) :
    reverseRows n (runRows n (rows n T hT) a).output
      (newCell n (rows n T hT) a).1 (newCell n (rows n T hT) a).2 =
    some ⟨rows n T hT, a, (runRows n (rows n T hT) a).columns⟩ :=
  reverse_after_runRows n (rows n T hT) a (rows_sorted n μ T hT)
    (TableauRunGeometry.rows_nonempty n μ T hT)

private theorem rows_getD (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r : ℕ) :
    (rows n T hT)[r]?.getD [] = row n T hT r := by
  by_cases hr : r < μ.colLen 0
  · simp [rows, hr]
  · have hz : μ.rowLen r = 0 := by
      have hn : ¬ (r, 0) ∈ μ := by simpa only [YoungDiagram.mem_iff_lt_colLen] using hr
      rw [YoungDiagram.mem_iff_lt_rowLen] at hn
      omega
    have he : row n T hT r = [] := List.length_eq_zero_iff.mp (by rw [row_length, hz])
    have ho : (List.range (μ.colLen 0))[r]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hr)
    simp [rows, ho, he]

theorem tableau_runRows_after_reverse (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (p : ℕ × ℕ)
    (hp : IsCorner μ p) (q : ReverseRun n)
    (hq : reverseRows n (rows n T hT) p.1 p.2 = some q) :
    (runRows n q.output q.letter).output = rows n T hT ∧
    (runRows n q.output q.letter).columns = q.columns ∧
    newCell n q.output q.letter = p := by
  apply runRows_after_reverse n (rows n T hT) p.1 p.2 q
    (rows_sorted n μ T hT) (TableauRunGeometry.rows_columns n μ T hT)
    (TableauRunGeometry.rows_nonempty n μ T hT) ?_ ?_ ?_ hq
  · rw [rows_length]
    have h := YoungDiagram.mem_iff_lt_colLen.mp hp.1
    exact lt_of_lt_of_le h (μ.colLen_anti 0 p.2 (Nat.zero_le _))
  · rw [rows_getD, row_length]
    exact corner_rowLen μ p hp
  · rw [rows_getD, row_length]
    have h := hp.2.1
    rw [YoungDiagram.mem_iff_lt_rowLen] at h
    omega

#print axioms last_cons
#print axioms reverse_after_runRows
#print axioms runRows_append
#print axioms split_last
#print axioms reconstruct
#print axioms runRows_after_reverse
#print axioms reverseRows_count
#print axioms tableau_reverse_after_runRows
#print axioms rows_getD
#print axioms tableau_runRows_after_reverse
end OddMath.Frontier.TableauReverseRunInverse
